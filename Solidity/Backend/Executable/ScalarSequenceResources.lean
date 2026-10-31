import Solidity.Backend.Executable.ScalarSequence

/-! Resource transport for the selected sequence and an actual checked-add
follow-up test. Invocation prefix laws are consumed read only, not duplicated.
The checked test is real numeric code with a failure flag; this is not a
compiled branch, panic emitter, fetched decoder or pinned EVM theorem. -/
namespace Solidity.Backend.Executable.ScalarSequence
open Scalar

def addChoice : CheckedCertificate .add .uint rfl :=
  (selectChecked .add .uint rfl).get (by rfl)

/-- Derive the published closed invocation from the whole-sequence capacity. -/
def subtractionInvocation {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1019) (a b u : PrimTy.uint.Denote)
    (result : BinOp.evalT .subW rfl a b = some u) (short : BinOp.shortT .subW a = none) :
    ClosedInvocation (subCertificate (C := C) (Γ := [.val .int, .val .uint]) a b u result short)
      (frameTail σ spill) where
  capacity := by
    change stackBound (subtract a b) _ = true
    apply stackBound_prefix (subtract a b)
      (castChoice.code ++ [.op (.DUP 0)] ++ literal .int zero ++ [.op (.SWAP 0)] ++ cmpChoice.code ++ notChoice.code)
    simpa only [code, compared, ordered, prepared, duplicated, casted, List.append_assoc]
      using frame_capacity σ spill room a b

/-- The comparison's saved signed word is part of its protected tail, so its
input capacity must include that word as well as the two caller frame cells. -/
def comparisonInvocation {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1019) (s : PrimTy.int.Denote) :
    BinaryInvocation cmpChoice s zero (encodeValue .int s :: frameTail σ spill) where
  capacity := by
    change stackBound [.op .SLT] _ = true
    simp only [stackBound, heightTrace, stackDelta, numericDelta, unary, binary,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, safeHeight,
      decide_eq_true_eq, List.length_cons, frame_length]
    omega

/-- Existing invocation laws transport every successful stage prefix using
capacity derived above, rather than caller-supplied per-stage capacity oracles. -/
theorem stage_prefixes {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1019) (a b u : PrimTy.uint.Denote)
    (s : PrimTy.int.Denote) (result : BinOp.evalT .subW rfl a b = some u)
    (short : BinOp.shortT .subW a = none) :
    (∀ before after, before ++ after = (subCertificate (C := C) (Γ := [.val .int, .val .uint]) a b u result short).code →
      ∀ st, run before (frameTail σ spill) = some st → st.length ≤ 1024) ∧
    (∀ before after, before ++ after = cmpChoice.code → ∀ st,
      run before (encodeValue .int s :: encodeValue .int zero :: encodeValue .int s :: frameTail σ spill) = some st →
      st.length ≤ 1024) := by
  exact ⟨fun before after split st ran =>
    (subtractionInvocation σ spill room a b u result short).prefix_safe before after split ran,
    fun before after split st ran => (comparisonInvocation σ spill room s).prefix_safe before after split ran⟩

/-- Append operand materialization and the selected real overflow test to the
entire previous sequence. The prior Boolean and signed result stay protected. -/
def checkedCode (a b : PrimTy.uint.Denote) : Program :=
  code a b ++ literal .uint b ++ literal .uint a ++ addChoice.test

/-- The complete selected follow-up reaches a real flag and the original
operands above the earlier typed results and unchanged caller frame. -/
theorem checked_stages {C : Contract} {Γ : Ctx} (a b u : PrimTy.uint.Denote)
    (s : PrimTy.int.Denote) (cmp : Bool) (tail : Stack)
    (subResult : BinOp.evalT .subW rfl a b = some u)
    (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s)
    (cmpResult : BinOp.evalT .lt rfl s zero = some cmp) :
    run (checkedCode a b) tail = some
      (flag (!PrimTy.uint.inRange (a.val + b.val)) :: encodeValue .uint a :: encodeValue .uint b ::
       encodeValue .bool (!cmp) :: encodeValue .int s :: tail) := by
  obtain ⟨_, _, _, _, _, _, _, base⟩ := stages (C := C) (Γ := Γ)
    a b u s cmp tail subResult subShort castResult cmpResult
  exact run_comp (run_comp (run_comp base (literal_correct .uint b _)) (literal_correct .uint a _))
    (unsignedAddTest_typed a b _)

/-- Exact words after each checked-test instruction, including its entry.
The tail can contain both earlier results and the populated caller frame. -/
theorem test_boundaries (a b : PrimTy.uint.Denote) (tail : Stack) :
    run (addChoice.test.take 0) (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (encodeValue .uint a :: encodeValue .uint b :: tail) ∧
    run (addChoice.test.take 1) (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (encodeValue .uint b :: encodeValue .uint a :: encodeValue .uint b :: tail) ∧
    run (addChoice.test.take 2) (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (encodeValue .uint a :: encodeValue .uint b :: encodeValue .uint a :: encodeValue .uint b :: tail) ∧
    run (addChoice.test.take 3) (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some ((encodeValue .uint a + encodeValue .uint b) :: encodeValue .uint a :: encodeValue .uint b :: tail) ∧
    run (addChoice.test.take 4) (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (encodeValue .uint a :: (encodeValue .uint a + encodeValue .uint b) :: encodeValue .uint a :: encodeValue .uint b :: tail) ∧
    run (addChoice.test.take 5) (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (flag (!PrimTy.uint.inRange (a.val+b.val)) :: encodeValue .uint a :: encodeValue .uint b :: tail) :=
  ⟨rfl, rfl, rfl, rfl, rfl, unsignedAddTest_typed a b tail⟩

/-- Exact operand materialization between the base sequence and checked test. -/
theorem followup_boundaries {C : Contract} {Γ : Ctx} (a b u : PrimTy.uint.Denote)
    (s : PrimTy.int.Denote) (cmp : Bool) (tail : Stack)
    (subResult : BinOp.evalT .subW rfl a b = some u) (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s) (cmpResult : BinOp.evalT .lt rfl s zero = some cmp) :
    run (code a b ++ literal .uint b) tail =
      some (encodeValue .uint b :: encodeValue .bool (!cmp) :: encodeValue .int s :: tail) ∧
    run (code a b ++ literal .uint b ++ literal .uint a) tail =
      some (encodeValue .uint a :: encodeValue .uint b :: encodeValue .bool (!cmp) :: encodeValue .int s :: tail) := by
  obtain ⟨_, _, _, _, _, _, _, base⟩ := stages (C := C) (Γ := Γ)
    a b u s cmp tail subResult subShort castResult cmpResult
  have first := run_comp base (literal_correct .uint b _)
  exact ⟨first, run_comp first (literal_correct .uint a _)⟩

/-- The two DUP2 instructions create the exact +6 peak, even though the final
height is only +5; retaining only the exit height would miss real overflow. -/
theorem checked_heights (a b : PrimTy.uint.Denote) (h : Int) :
    heightTrace (checkedCode a b) h =
      [h,h+1,h+2,h+1,h+2,h+3,h+3,h+2,h+2,h+3,h+4,h+5,h+6,h+5,h+6,h+5] := by
  unfold checkedCode
  rw [instructions]
  change heightTrace
    ([pushWord (encodeValue .uint b), pushWord (encodeValue .uint a), .op .SUB,
      .op (.DUP 0), pushWord (encodeValue .int zero), .op (.SWAP 0), .op .SLT, .op .ISZERO] ++
      [pushWord (encodeValue .uint b)] ++ [pushWord (encodeValue .uint a)] ++
      [.op (.DUP 1), .op (.DUP 1), .op .ADD, .op (.DUP 1), .op .GT]) h = _
  simp only [List.cons_append, List.nil_append, heightTrace, stackDelta, pushWord,
    numericDelta, unary, binary, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, if_false, if_true, Int.add_assoc, Int.reduceAdd, Int.add_zero]

theorem checked_capacity_iff (a b : PrimTy.uint.Denote) (h : Int) :
    stackBound (checkedCode a b) h = true ↔ 0 ≤ h ∧ h + 6 ≤ 1024 := by
  simp only [stackBound, checked_heights, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, safeHeight, decide_eq_true_eq]
  omega

theorem checked_frame_capacity_iff {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (a b : PrimTy.uint.Denote) :
    stackBound (checkedCode a b) ((frameTail σ spill).length : Int) = true ↔ spill.length ≤ 1016 := by
  rw [checked_capacity_iff, frame_length]
  constructor <;> intro h <;> omega

/-- The selected test/body invocation is discharged by the actual +6/+4
height calculations, including both prior results in the protected tail. -/
def followupInvocation {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1016) (a b : PrimTy.uint.Denote)
    (s : PrimTy.int.Denote) (cmp : Bool) :
    CheckedInvocation addChoice a b
      (encodeValue .bool (!cmp) :: encodeValue .int s :: frameTail σ spill) where
  testCapacity := by
    change stackBound [.op (.DUP 1), .op (.DUP 1), .op .ADD, .op (.DUP 1), .op .GT] _ = true
    simp only [stackBound, heightTrace, stackDelta, numericDelta, unary, binary,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, safeHeight,
      decide_eq_true_eq, List.length_cons, frame_length]
    omega
  bodyCapacity := by
    change stackBound [.op .ADD] _ = true
    simp only [stackBound, heightTrace, stackDelta, numericDelta, unary, binary,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, safeHeight,
      decide_eq_true_eq, List.length_cons, frame_length]
    omega

/-- Consume the published checked-prefix law with the independently derived
invocation; this is a stage consequence of the actual composed sequence. -/
theorem checked_prefix_safe {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1016) (a b : PrimTy.uint.Denote)
    (s : PrimTy.int.Denote) (cmp : Bool) (before after : Program)
    (split : before ++ after = addChoice.test) {st : Stack}
    (ran : run before (encodeValue .uint a :: encodeValue .uint b ::
      encodeValue .bool (!cmp) :: encodeValue .int s :: frameTail σ spill) = some st) : st.length ≤ 1024 :=
  (followupInvocation σ spill room a b s cmp).testPrefix_safe before after split ran

/-- Exact bytes of the complete append, with both immediate payloads and
all five real test opcodes accounted for. -/
theorem checked_emitted_bytes (a b : PrimTy.uint.Denote) : Backend.encode (checkedCode a b) =
    Backend.encode (code a b) ++ (pushWord (encodeValue .uint b)).encode ++
      (pushWord (encodeValue .uint a)).encode ++ [0x81,0x81,0x01,0x81,0x11] := by
  simp only [checkedCode, encode_append, literal,
    show addChoice.test = [.op (.DUP 1), .op (.DUP 1), .op .ADD, .op (.DUP 1), .op .GT] from rfl,
    encode_cons, encode_nil, List.append_nil,
    show Instr.encode (.op (.DUP 1)) = [0x81] from rfl,
    show Instr.encode (.op .ADD) = [0x01] from rfl,
    show Instr.encode (.op .GT) = [0x11] from rfl, List.cons_append, List.nil_append]

theorem checked_bytes_length (a b : PrimTy.uint.Denote) :
    (Backend.encode (checkedCode a b)).length = 175 := by
  rw [length_encode]
  unfold checkedCode
  rw [instructions]
  rfl

theorem checked_decode_bytes (a b : PrimTy.uint.Denote) :
    Backend.decode (Backend.encode (checkedCode a b)) = some (checkedCode a b) := decode_encode _

/-- info: 'Solidity.Backend.Executable.ScalarSequence.stage_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage_prefixes
/-- info: 'Solidity.Backend.Executable.ScalarSequence.checked_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_stages
/-- info: 'Solidity.Backend.Executable.ScalarSequence.checked_heights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_heights
/-- info: 'Solidity.Backend.Executable.ScalarSequence.checked_frame_capacity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_frame_capacity_iff
/-- info: 'Solidity.Backend.Executable.ScalarSequence.checked_prefix_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_prefix_safe
end Solidity.Backend.Executable.ScalarSequence
