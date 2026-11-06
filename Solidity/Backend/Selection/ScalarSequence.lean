import Solidity.Backend.Scalar.Select

/-!
# Staged scalar consumer over an actual typed caller frame

This consumes the published selectors and certificates. It does not introduce
instruction selection or a new semantics. Scalar.run is the independent gasless
numeric slice; total encoding/decoding is an encoder roundtrip, not fetched
runtime or Osaka execution. The caller-frame producer and its connection to
runtime locals remain open. Short-circuit refusal is explicit source evidence.
-/
namespace Solidity.Backend.Selection.ScalarSequence
open Scalar

def subChoice : BinaryCertificate .subW .uint rfl :=
  (selectBinary .subW .uint rfl).get (by rfl)
def castChoice : UnaryCertificate .toInt .uint rfl :=
  (selectUnary .toInt .uint rfl).get (by rfl)
def cmpChoice : BinaryCertificate .lt .int rfl :=
  (selectBinary .lt .int rfl).get (by rfl)
def notChoice : UnaryCertificate .not .bool rfl :=
  (selectUnary .not .bool rfl).get (by rfl)

def zero : PrimTy.int.Denote := ⟨0, by decide⟩
def literalExpr {C : Contract} {Γ : Ctx} (a : PrimTy.uint.Denote) : Val C Γ .uint :=
  .simple (.lit a.val a.property)
def subExpr {C : Contract} {Γ : Ctx} (a b : PrimTy.uint.Denote) : Val C Γ .uint :=
  .binop .subW rfl rfl (literalExpr a) (literalExpr b)

def subCertificate {C : Contract} {Γ : Ctx} (a b u : PrimTy.uint.Denote)
    (result : BinOp.evalT .subW rfl a b = some u)
    (short : BinOp.shortT .subW a = none) : ClosedCertificate (subExpr (C := C) (Γ := Γ) a b) :=
  (numericLiteral .uint a.val a.property).binary
    (numericLiteral .uint b.val b.property) subChoice u result short

def operands (a b : PrimTy.uint.Denote) : Program := literal .uint b ++ literal .uint a
def subtract (a b : PrimTy.uint.Denote) : Program := operands a b ++ subChoice.code
def casted (a b : PrimTy.uint.Denote) : Program := subtract a b ++ castChoice.code
def duplicated (a b : PrimTy.uint.Denote) : Program := casted a b ++ [.op (.DUP 0)]
def prepared (a b : PrimTy.uint.Denote) : Program := duplicated a b ++ literal .int zero
def ordered (a b : PrimTy.uint.Denote) : Program := prepared a b ++ [.op (.SWAP 0)]
def compared (a b : PrimTy.uint.Denote) : Program := ordered a b ++ cmpChoice.code
def code (a b : PrimTy.uint.Denote) : Program := compared a b ++ notChoice.code

/-- Exact operand and saved-result order at all eight nontrivial boundaries. -/
theorem stages {C : Contract} {Γ : Ctx} (a b u : PrimTy.uint.Denote)
    (s : PrimTy.int.Denote) (cmp : Bool) (tail : Stack)
    (subResult : BinOp.evalT .subW rfl a b = some u)
    (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s)
    (cmpResult : BinOp.evalT .lt rfl s zero = some cmp) :
    run (operands a b) tail = some (encodeValue .uint a :: encodeValue .uint b :: tail) ∧
    run (subtract a b) tail = some (encodeValue .uint u :: tail) ∧
    run (casted a b) tail = some (encodeValue .int s :: tail) ∧
    run (duplicated a b) tail = some (encodeValue .int s :: encodeValue .int s :: tail) ∧
    run (prepared a b) tail = some (encodeValue .int zero :: encodeValue .int s :: encodeValue .int s :: tail) ∧
    run (ordered a b) tail = some (encodeValue .int s :: encodeValue .int zero :: encodeValue .int s :: tail) ∧
    run (compared a b) tail = some (encodeValue .bool cmp :: encodeValue .int s :: tail) ∧
    run (code a b) tail = some (encodeValue .bool (!cmp) :: encodeValue .int s :: tail) := by
  have ho : run (operands a b) tail = some (encodeValue .uint a :: encodeValue .uint b :: tail) :=
    run_comp (literal_correct .uint b tail) (literal_correct .uint a _)
  have hs : run (subtract a b) tail = some (encodeValue .uint u :: tail) :=
    (subCertificate (C := C) (Γ := Γ) a b u subResult subShort).target tail
  have hc : run castChoice.code (encodeValue .uint u :: tail) = some (encodeValue .int s :: tail) := by
    rw [castChoice.correct, castResult]; rfl
  have hcast : run (casted a b) tail = some (encodeValue .int s :: tail) := run_comp hs hc
  have hd : run (duplicated a b) tail = some (encodeValue .int s :: encodeValue .int s :: tail) :=
    run_comp hcast rfl
  have hp : run (prepared a b) tail = some (encodeValue .int zero :: encodeValue .int s :: encodeValue .int s :: tail) :=
    run_comp hd (literal_correct .int zero _)
  have hw : run (ordered a b) tail = some (encodeValue .int s :: encodeValue .int zero :: encodeValue .int s :: tail) :=
    run_comp hp rfl
  have ht : run cmpChoice.code (encodeValue .int s :: encodeValue .int zero :: encodeValue .int s :: tail) =
      some (encodeValue .bool cmp :: encodeValue .int s :: tail) := by
    rw [cmpChoice.correct, cmpResult]; rfl
  have hcmp : run (compared a b) tail = some (encodeValue .bool cmp :: encodeValue .int s :: tail) := run_comp hw ht
  have hn : run notChoice.code (encodeValue .bool cmp :: encodeValue .int s :: tail) =
      some (encodeValue .bool (!cmp) :: encodeValue .int s :: tail) := by
    cases cmp <;> rfl
  exact ⟨ho, hs, hcast, hd, hp, hw, hcmp, run_comp hcmp hn⟩

def resultExpr {C : Contract} {Γ : Ctx} (a b : PrimTy.uint.Denote) : Val C Γ .bool :=
  .unop .not rfl rfl (.binop .lt rfl rfl
    (.unop .toInt rfl rfl (subExpr a b)) (.simple (.lit 0 rfl)))

/-- Independent intrinsic source evaluation, using the published closed
certificate composition and both exact short-circuit refusal equations. -/
theorem source_result {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (a b u : PrimTy.uint.Denote) (s : PrimTy.int.Denote) (cmp : Bool)
    (subResult : BinOp.evalT .subW rfl a b = some u)
    (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s)
    (cmpResult : BinOp.evalT .lt rfl s zero = some cmp)
    (cmpShort : BinOp.shortT .lt s = none) :
    (resultExpr a b).evalT σ = .ok (!cmp) := by
  have hn : UnOp.evalT .not (p := .bool) rfl cmp = some (!cmp) := by cases cmp <;> rfl
  exact (((subCertificate a b u subResult subShort).unary castChoice s castResult).binary
    (numericLiteral .int 0 rfl) cmpChoice cmp cmpResult cmpShort).unary notChoice (!cmp) hn |>.source σ

/-- The first physical PUSH boundary, before the left operand is emitted. -/
theorem first_boundary (a b : PrimTy.uint.Denote) (tail : Stack) :
    run ((code a b).take 1) tail = some (encodeValue .uint b :: tail) :=
  literal_correct .uint b tail

/-- The physical instructions are chosen by the existing selectors, not a
caller-provided simulation oracle; casts preserve the original word bits. -/
theorem instructions (a b : PrimTy.uint.Denote) : code a b =
    [pushWord (encodeValue .uint b), pushWord (encodeValue .uint a), .op .SUB,
     .op (.DUP 0), pushWord (encodeValue .int zero), .op (.SWAP 0), .op .SLT, .op .ISZERO] := rfl

/-- Exact peak, including DUP and the comparison operand above the saved word. -/
theorem heights (a b : PrimTy.uint.Denote) (h : Int) :
    heightTrace (code a b) h = [h, h+1, h+2, h+1, h+2, h+3, h+3, h+2, h+2] := by
  rw [instructions]
  simp only [heightTrace, stackDelta, pushWord, numericDelta, unary, binary,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true]
  simp only [Int.add_assoc, Int.reduceAdd, Int.add_zero]

theorem capacity_iff (a b : PrimTy.uint.Denote) (h : Int) :
    stackBound (code a b) h = true ↔ 0 ≤ h ∧ h + 3 ≤ 1024 := by
  simp only [stackBound, heights, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, safeHeight, decide_eq_true_eq]
  omega

/-- A concrete frame representation of two existing typed caller locals. The
producer linking this representation to actual runtime locals is still open. -/
def callerFrame {C : Contract} (σ : State C [.val .int, .val .uint]) : Stack :=
  [encodeValue .int (TEnv.get .here σ.env), encodeValue .uint (TEnv.get (.there .here) σ.env)]
def frameTail {C : Contract} (σ : State C [.val .int, .val .uint]) (spill : Stack) : Stack :=
  callerFrame σ ++ spill

theorem frame_length {C : Contract} (σ : State C [.val .int, .val .uint]) (spill : Stack) :
    (frameTail σ spill).length = spill.length + 2 := by
  simp only [frameTail, callerFrame, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Capacity is derived from the two typed frame cells and the exact +3 peak. -/
theorem frame_capacity {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1019) (a b : PrimTy.uint.Denote) :
    stackBound (code a b) ((frameTail σ spill).length : Int) = true := by
  apply (capacity_iff _ _ _).mpr
  rw [frame_length]
  constructor <;> omega

/-- Necessary and sufficient spill capacity, computed from the actual
instruction heights and the two populated caller-frame positions. -/
theorem frame_capacity_iff {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (a b : PrimTy.uint.Denote) :
    stackBound (code a b) ((frameTail σ spill).length : Int) = true ↔ spill.length ≤ 1019 := by
  rw [capacity_iff, frame_length]
  constructor <;> intro h <;> omega

/-- Source/target composition for this concrete sequence, over the actual typed
caller frame; all operator witnesses are source equations, never simulations. -/
theorem typed_result {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1019)
    (a b u : PrimTy.uint.Denote) (s : PrimTy.int.Denote) (cmp : Bool)
    (subResult : BinOp.evalT .subW rfl a b = some u)
    (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s)
    (cmpResult : BinOp.evalT .lt rfl s zero = some cmp)
    (cmpShort : BinOp.shortT .lt s = none) :
    (resultExpr a b).evalT σ = .ok (!cmp) ∧
    run (code a b) (frameTail σ spill) =
      some (encodeValue .bool (!cmp) :: encodeValue .int s :: frameTail σ spill) ∧
    stackBound (code a b) ((frameTail σ spill).length : Int) = true := by
  obtain ⟨_, _, _, _, _, _, _, target⟩ := stages (C := C) (Γ := [.val .int, .val .uint])
    a b u s cmp (frameTail σ spill) subResult subShort castResult cmpResult
  exact ⟨source_result σ a b u s cmp subResult subShort castResult cmpResult cmpShort,
    target, frame_capacity σ spill room a b⟩

/-- Every actual whole-sequence prefix transports that derived capacity. -/
theorem frame_prefix_safe {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1019) (a b : PrimTy.uint.Denote)
    (before after : Program) (split : before ++ after = code a b) {st : Stack}
    (ran : run before (frameTail σ spill) = some st) : st.length ≤ 1024 := by
  apply prefix_capacity before after ran
  rw [split]
  exact frame_capacity σ spill room a b

/-- All emitted bytes in actual order, including every full PUSH32 payload. -/
theorem emitted_bytes (a b : PrimTy.uint.Denote) : Backend.encode (code a b) =
    (pushWord (encodeValue .uint b)).encode ++ (pushWord (encodeValue .uint a)).encode ++
    [0x03,0x80] ++ (pushWord (encodeValue .int zero)).encode ++ [0x90,0x12,0x15] := by
  rw [instructions]
  simp only [encode_cons, encode_nil, List.append_nil, List.append_assoc,
    show Instr.encode (.op .SUB) = [0x03] from rfl,
    show Instr.encode (.op (.DUP 0)) = [0x80] from rfl,
    show Instr.encode (.op (.SWAP 0)) = [0x90] from rfl,
    show Instr.encode (.op .SLT) = [0x12] from rfl,
    show Instr.encode (.op .ISZERO) = [0x15] from rfl,
    List.cons_append, List.nil_append]

/-- Exact total byte count, not just the final opcode or an encoding fragment. -/
theorem bytes_length (a b : PrimTy.uint.Denote) : (Backend.encode (code a b)).length = 104 := by
  rw [length_encode, instructions]
  rfl

theorem decode_bytes (a b : PrimTy.uint.Denote) :
    Backend.decode (Backend.encode (code a b)) = some (code a b) := decode_encode _

#print axioms source_result
#print axioms typed_result
#print axioms frame_capacity_iff
#print axioms stages
#print axioms heights
#print axioms frame_capacity
#print axioms frame_prefix_safe
end Solidity.Backend.Selection.ScalarSequence
