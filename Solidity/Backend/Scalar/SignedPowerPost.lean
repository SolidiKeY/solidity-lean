import Solidity.Backend.Scalar.SignedPowerPrefix

/-! The signed-power magnitude/result guard accepts magnitude 2^255 only
for a negative result. Sign application is a real arithmetic slice. -/
namespace Solidity.Backend.Scalar

def powerSignedValue (negative : Bool) (r : PrimTy.uint.Denote) : Int :=
  if negative then -r.val else r.val

def powerPostValue (negative : Bool) (r : PrimTy.uint.Denote) : Option PrimTy.int.Denote :=
  PrimTy.int.ofInt? (powerSignedValue negative r)

def powerPostTest : Program :=
  [.op (.DUP ⟨1, by decide⟩), pushWord (BitVec.ofNat 256 (2^255)), .op .ADD,
   .op (.DUP ⟨1, by decide⟩), .op .LT, .op .ISZERO]

def powerSignBody : Program :=
  [.op (.DUP ⟨1, by decide⟩), pushWord 2, .op .MUL, pushWord 1, .op .SUB,
   .op .MUL, .op (.SWAP ⟨0, by decide⟩), .op .POP]


private theorem stepDup2 (a b : Word) (tail : Stack) :
    step (.op (.DUP ⟨1, by decide⟩)) (a::b::tail) = some (b::a::b::tail) := rfl
private theorem stepAdd (a b : Word) (tail : Stack) :
    step (.op .ADD) (a::b::tail) = some ((a+b)::tail) := rfl
private theorem stepSub (a b : Word) (tail : Stack) :
    step (.op .SUB) (a::b::tail) = some ((a-b)::tail) := rfl
private theorem stepMul (a b : Word) (tail : Stack) :
    step (.op .MUL) (a::b::tail) = some ((a*b)::tail) := rfl
private theorem stepLt (a b : Word) (tail : Stack) :
    step (.op .LT) (a::b::tail) = some (flag (decide (a.toNat<b.toNat))::tail) := rfl
private theorem stepZero (a : Word) (tail : Stack) :
    step (.op .ISZERO) (a::tail) = some (flag (a==0)::tail) := rfl
private theorem stepSwap (a b : Word) (tail : Stack) :
    step (.op (.SWAP ⟨0, by decide⟩)) (a::b::tail) = some (b::a::tail) := rfl
private theorem stepPop (a : Word) (tail : Stack) :
    step (.op .POP) (a::tail) = some tail := rfl

theorem powerPostTest_correct (negative : Bool) (r : PrimTy.uint.Denote) (tail : Stack) :
    run powerPostTest (encodeValue .uint r::flag negative::tail) =
      some (flag (!PrimTy.int.inRange (powerSignedValue negative r)) ::
        encodeValue .uint r::flag negative::tail) := by
  simp only [powerPostTest, run, stepDup2, step_pushWord, stepAdd, stepLt,
    stepZero, Option.bind_some]
  rw [flag_iszero, encode_uint_toNat]
  have hc : (BitVec.ofNat 256 (2^255)+flag negative).toNat =
      2^255+(if negative then 1 else 0) := by
    cases negative <;> decide +kernel
  rw [hc]
  have hr : 0 ≤ r.val ∧ r.val < ((2 ^ 256 : Nat) : Int) := uint_range r
  have he : decide (r.val.toNat<2^255+(if negative then 1 else 0)) =
      PrimTy.int.inRange (powerSignedValue negative r) := by
    apply Bool.eq_iff_iff.mpr
    cases negative <;> simp only [powerSignedValue, Bool.false_eq_true, if_false,
      if_true, PrimTy.inRange, decide_eq_true_eq] <;> omega
  rw [he]

theorem powerSignBody_correct (negative : Bool) (r : PrimTy.uint.Denote) (tail : Stack) :
    run powerSignBody (encodeValue .uint r::flag negative::tail) =
      some (BitVec.ofInt 256 (powerSignedValue negative r)::tail) := by
  simp only [powerSignBody, run, stepDup2, step_pushWord, stepMul, stepSub,
    stepSwap, stepPop, Option.bind_some]
  cases negative with
  | false =>
    change some (((1#256-2#256*0#256)*encodeValue .uint r)::tail) = some (BitVec.ofInt 256 r.val::tail)
    rw [BitVec.mul_zero, BitVec.sub_zero, BitVec.one_mul]
    rfl
  | true =>
    change some (((-1#256)*BitVec.ofInt 256 r.val)::tail) = some (BitVec.ofInt 256 (-r.val)::tail)
    rw [BitVec.neg_mul, BitVec.one_mul, BitVec.ofInt_neg]

theorem powerPost_correct (negative : Bool) (r : PrimTy.uint.Denote) (tail : Stack) :
    guarded powerPostTest powerSignBody overflowFailure (encodeValue .uint r::flag negative::tail) =
      some (checkedOutcome .int (powerPostValue negative r) tail) := by
  unfold guarded
  rw [powerPostTest_correct]
  cases hr : PrimTy.int.inRange (powerSignedValue negative r) with
  | false =>
    rw [show powerPostValue negative r = none by
      simp only [powerPostValue, PrimTy.ofInt?, hr, Bool.false_eq_true, dite_false]]
    rfl
  | true =>
    rw [show powerPostValue negative r = some ⟨powerSignedValue negative r, hr⟩ by
      simp only [powerPostValue, PrimTy.ofInt?, hr, dite_true]]
    change (run powerSignBody (encodeValue .uint r::flag negative::tail)).map Except.ok =
      some (.ok (BitVec.ofInt 256 (powerSignedValue negative r)::tail))
    rw [powerSignBody_correct]
    rfl

/-- The original typed helper's numeric result, including its rejecting arm. -/
theorem powerPostValue_map (negative : Bool) (r : PrimTy.uint.Denote) :
    (powerPostValue negative r).map (·.val) =
      if negative then (if r.val≤Semantics.intBound then some (-r.val) else none)
      else (if r.val<Semantics.intBound then some r.val else none) := by
  have hr : 0 ≤ r.val ∧ r.val < ((2 ^ 256 : Nat) : Int) := uint_range r
  have hH : (0:Int)<Semantics.intBound := by decide
  cases negative with
  | false =>
    change (PrimTy.int.ofInt? r.val).map (·.val) = _
    by_cases hn : r.val<Semantics.intBound
    · have hi : PrimTy.int.inRange r.val=true := by
        simp only [PrimTy.inRange, decide_eq_true_eq]
        exact ⟨by omega, hn⟩
      simp only [PrimTy.ofInt?, hi, dite_true, Option.map_some, hn, if_true,
        Bool.false_eq_true, if_false]
    · have hi : PrimTy.int.inRange r.val=false := by
        apply Bool.eq_false_iff.mpr
        intro hi
        have hb : -Semantics.intBound ≤ r.val ∧ r.val < Semantics.intBound := by
          simpa only [PrimTy.inRange, decide_eq_true_eq] using hi
        exact hn hb.2
      simp only [PrimTy.ofInt?, hi, Bool.false_eq_true, dite_false, Option.map_none, hn, if_false]
  | true =>
    change (PrimTy.int.ofInt? (-r.val)).map (·.val) = _
    by_cases hn : r.val≤Semantics.intBound
    · have hi : PrimTy.int.inRange (-r.val)=true := by
        simp only [PrimTy.inRange, decide_eq_true_eq]
        change -Semantics.intBound ≤ -r.val ∧ -r.val < Semantics.intBound
        omega
      simp only [PrimTy.ofInt?, hi, dite_true, Option.map_some, hn, if_true]
    · have hi : PrimTy.int.inRange (-r.val)=false := by
        apply Bool.eq_false_iff.mpr
        intro hi
        have hb : -Semantics.intBound ≤ -r.val ∧ -r.val < Semantics.intBound := by
          simpa only [PrimTy.inRange, decide_eq_true_eq] using hi
        exact hn (by omega)
      simp only [PrimTy.ofInt?, hi, Bool.false_eq_true, dite_false, Option.map_none, hn, if_false, if_true]

theorem powerPost_source {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (nv : Val C Γ .bool) (rv : Val C Γ .uint) (negative : Bool) (r : PrimTy.uint.Denote)
    (hn : nv.evalT σ = .ok negative) (hr : rv.evalT σ = .ok r) :
    ((Val.signedPowerResult nv rv).evalT σ).toOption.map (·.val) =
      (powerPostValue negative r).map (·.val) := by
  rw [NumericLowering.signedPowerResult_eval σ nv rv negative r hn hr, powerPostValue_map]

#print axioms powerPostTest_correct
#print axioms powerSignBody_correct
#print axioms powerPost_correct
#print axioms powerPost_source
end Solidity.Backend.Scalar
