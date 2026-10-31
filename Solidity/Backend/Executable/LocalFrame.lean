import Solidity.Backend.Executable.ScalarSequence

/-! Actual local reads from the owned two-cell typed frame. Code is uniform
in the state: it duplicates existing words, never specializes a local into a
literal. The general runtime-frame producer and fetched execution stay open. -/
namespace Solidity.Backend.Executable.LocalFrame
open Scalar ScalarSequence
variable {C : Contract}

def intRead : Val C [.val .int, .val .uint] .int := .simple (.local .here)
def uintRead : Val C [.val .int, .val .uint] .uint := .simple (.local (.there .here))
def intCode : Program := [.op (.DUP 0)]
def uintCode : Program := [.op (.DUP 1)]

theorem int_source (σ : State C [.val .int, .val .uint]) :
    intRead.evalT σ = .ok (TEnv.get .here σ.env) := rfl
theorem uint_source (σ : State C [.val .int, .val .uint]) :
    uintRead.evalT σ = .ok (TEnv.get (.there .here) σ.env) := rfl

theorem reads (σ : State C [.val .int, .val .uint]) (spill : Stack) :
    run intCode (frameTail σ spill) = some (encodeValue .int (TEnv.get .here σ.env) :: frameTail σ spill) ∧
    run uintCode (frameTail σ spill) = some (encodeValue .uint (TEnv.get (.there .here) σ.env) :: frameTail σ spill) := ⟨rfl, rfl⟩

theorem read_capacity (σ : State C [.val .int, .val .uint]) (spill : Stack) :
    (stackBound intCode ((frameTail σ spill).length : Int) = true ↔ spill.length ≤ 1021) ∧
    (stackBound uintCode ((frameTail σ spill).length : Int) = true ↔ spill.length ≤ 1021) := by
  simp only [stackBound, intCode, uintCode, heightTrace, stackDelta, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, safeHeight, decide_eq_true_eq, frame_length]
  constructor <;> constructor <;> intro h <;> omega

/-- The right operand is evaluated first. Its PUSH shifts the uint local from
DUP2 to DUP3; the top signed local is protected, not mistaken for the operand. -/
def operands (b : PrimTy.uint.Denote) : Program := literal .uint b ++ [.op (.DUP 2)]
def code (b : PrimTy.uint.Denote) : Program := operands b ++ subChoice.code
def expr (b : PrimTy.uint.Denote) : Val C [.val .int, .val .uint] .uint :=
  .binop .subW rfl rfl uintRead (literalExpr b)

theorem stages (σ : State C [.val .int, .val .uint]) (spill : Stack)
    (b u : PrimTy.uint.Denote)
    (result : BinOp.evalT .subW rfl (TEnv.get (.there .here) σ.env) b = some u) :
    run (literal .uint b) (frameTail σ spill) = some (encodeValue .uint b :: frameTail σ spill) ∧
    run (operands b) (frameTail σ spill) = some
      (encodeValue .uint (TEnv.get (.there .here) σ.env) :: encodeValue .uint b :: frameTail σ spill) ∧
    run (code b) (frameTail σ spill) = some (encodeValue .uint u :: frameTail σ spill) := by
  have pushed := literal_correct .uint b (frameTail σ spill)
  have copied : run (operands b) (frameTail σ spill) = some
      (encodeValue .uint (TEnv.get (.there .here) σ.env) :: encodeValue .uint b :: frameTail σ spill) :=
    run_comp pushed rfl
  have selected : run subChoice.code
      (encodeValue .uint (TEnv.get (.there .here) σ.env) :: encodeValue .uint b :: frameTail σ spill) =
      some (encodeValue .uint u :: frameTail σ spill) := by
    rw [subChoice.correct, result]; rfl
  exact ⟨pushed, copied, run_comp copied selected⟩

theorem source (σ : State C [.val .int, .val .uint]) (b u : PrimTy.uint.Denote)
    (result : BinOp.evalT .subW rfl (TEnv.get (.there .here) σ.env) b = some u)
    (short : BinOp.shortT .subW (TEnv.get (.there .here) σ.env) = none) :
    (expr b).evalT σ = .ok u := by
  change (match BinOp.shortT .subW (TEnv.get (.there .here) σ.env) with
    | some value => Except.ok (ε := THalt) value
    | none => TRes.ofOpt (BinOp.evalT .subW rfl (TEnv.get (.there .here) σ.env) b)) = .ok u
  rw [short, result]
  rfl

theorem heights (b : PrimTy.uint.Denote) (h : Int) :
    heightTrace (code b) h = [h,h+1,h+2,h+1] := by
  change heightTrace [pushWord (encodeValue .uint b), .op (.DUP 2), .op .SUB] h = _
  simp only [heightTrace, stackDelta, pushWord, numericDelta, unary, binary,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true]
  simp only [Int.add_assoc, Int.reduceAdd]

theorem capacity (σ : State C [.val .int, .val .uint]) (spill : Stack) (b : PrimTy.uint.Denote) :
    stackBound (code b) ((frameTail σ spill).length : Int) = true ↔ spill.length ≤ 1020 := by
  simp only [stackBound, heights, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, safeHeight, decide_eq_true_eq, frame_length]
  omega

/-- Every real prefix has physical capacity, derived from the combination's
peak rather than tail preservation or a supplied simulation certificate. -/
theorem prefix_safe (σ : State C [.val .int, .val .uint]) (spill : Stack)
    (b : PrimTy.uint.Denote) (room : spill.length ≤ 1020) (first rest : Program)
    (split : first ++ rest = code b) {after : Stack}
    (ran : run first (frameTail σ spill) = some after) : after.length ≤ 1024 := by
  apply prefix_capacity first rest ran
  rw [split]
  exact (capacity σ spill b).mpr room

theorem bytes (b : PrimTy.uint.Denote) :
    Backend.encode (code b) = (0x7f :: (toBytesBE 32 (encodeValue .uint b).toNat).toList) ++ [0x82,0x03] := by
  change Backend.encode ([pushWord (encodeValue .uint b)] ++ [.op (.DUP 2), .op .SUB]) = _
  rw [Backend.encode_append]
  simp only [encode_cons, encode_nil, List.append_nil, encode_pushWord,
    show Instr.encode (.op (.DUP 2)) = [0x82] from rfl,
    show Instr.encode (.op .SUB) = [0x03] from rfl]
  rfl

theorem decode (b : PrimTy.uint.Denote) : Backend.decode (Backend.encode (code b)) = some (code b) :=
  Backend.decode_encode _

/-- info: 'Solidity.Backend.Executable.LocalFrame.reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reads
/-- info: 'Solidity.Backend.Executable.LocalFrame.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source
/-- info: 'Solidity.Backend.Executable.LocalFrame.prefix_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_safe
end Solidity.Backend.Executable.LocalFrame
