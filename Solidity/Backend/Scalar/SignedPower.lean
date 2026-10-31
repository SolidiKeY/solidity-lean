import Solidity.Backend.Scalar.SignedPowerPost
import Solidity.Backend.Scalar.Capacity
import Solidity.Backend.Scalar.Negation

/-! A certificate for the committed heterogeneous checked signed-power helper.
The source calculation uses the existing intrinsic unsigned power and int
range constructor. Target stages are real programs with an explicit guarded
observation boundary; generic control/revert emission remains separate. -/
namespace Solidity.Backend.Scalar

def powerSourceResult (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote) : Option PrimTy.int.Denote :=
  (BinOp.evalT .pow (p := .uint) rfl (magnitudeValue a) n).bind (powerPostValue (powerNegative a n))

def powerFinish : Except (List UInt8) Stack → Option (Except (List UInt8) Stack)
  | .error failure => some (.error failure)
  | .ok result => guarded powerPostTest powerSignBody overflowFailure result

def signedPowerExecute (st : Stack) : Option (Except (List UInt8) Stack) :=
  (run powerPrepare st).bind fun prepared =>
    (guarded checkedUintPow.test checkedUintPow.body overflowFailure prepared).bind powerFinish

theorem signedPower_correct (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote) (tail : Stack) :
    signedPowerExecute (encodeValue .int a::encodeValue .uint n::tail) =
      some (checkedOutcome .int (powerSourceResult a n) tail) := by
  rw [signedPowerExecute, powerPrepare_correct, Option.bind_some, checkedUintPow.correct]
  cases hv : BinOp.evalT .pow (p := .uint) rfl (magnitudeValue a) n with
  | none =>
    simp only [powerSourceResult, hv, Option.bind_none]
    rfl
  | some r =>
    simp only [powerSourceResult, hv, Option.bind_some]
    exact powerPost_correct (powerNegative a n) r tail

theorem powerSourceResult_map (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote) :
    (powerSourceResult a n).map (·.val) = NumericLowering.signedPower a.val n.val.toNat := by
  let m : Int := (a.val.natAbs:Int)^n.val.toNat
  have hm : 0 ≤ m := Int.pow_nonneg (Int.natCast_nonneg _)
  have hH : Semantics.intBound < Semantics.uintBound := by decide
  have hn : ¬ n.val<0 := by have : 0 ≤ n.val ∧ n.val < ((2 ^ 256 : Nat) : Int) := uint_range n; omega
  change (((if n.val<0 then none else some m).bind PrimTy.uint.ofInt?).bind
    (powerPostValue (powerNegative a n))).map (·.val) = _
  simp only [hn, if_false, Option.bind_some]
  by_cases hw : m<Semantics.uintBound
  · have hr : PrimTy.uint.inRange m=true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]
      exact ⟨hm, hw⟩
    simp only [PrimTy.ofInt?, hr, dite_true, Option.bind_some]
    rw [powerPostValue_map]
    change (if powerNegative a n then (if m≤Semantics.intBound then some (-m) else none)
      else (if m<Semantics.intBound then some m else none)) = _
    unfold NumericLowering.signedPower
    by_cases hs : a.val<0 ∧ n.val.toNat%2=1
    · simp only [powerNegative, hs]
      rfl
    · simp only [powerNegative, hs, decide_false, Bool.false_eq_true, if_false]
      rfl
  · have hr : PrimTy.uint.inRange m=false := by
      apply Bool.eq_false_iff.mpr
      intro hi
      have hri : 0≤m ∧ m<Semantics.uintBound := by
        simpa only [PrimTy.inRange, decide_eq_true_eq] using hi
      exact hw hri.2
    simp only [PrimTy.ofInt?, hr, Bool.false_eq_true, dite_false, Option.bind_none, Option.map_none]
    have hle : ¬m≤Semantics.intBound := by omega
    have hlt : ¬m<Semantics.intBound := by omega
    change none = if a.val<0 ∧ n.val.toNat%2=1 then
      (if m≤Semantics.intBound then some (-m) else none)
      else (if m<Semantics.intBound then some m else none)
    simp only [hle, hlt, if_false]
    split <;> rfl

/-- The current committed intrinsic Val helper supplies the source side. -/
theorem signedPower_source {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (nv : Val C Γ .uint) (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hn : nv.evalT σ = .ok n) :
    ((Val.checkedSignedPower av nv).evalT σ).toOption.map (·.val) =
      (powerSourceResult a n).map (·.val) := by
  rw [NumericLowering.checkedSignedPower_eval σ av nv a n ha hn, powerSourceResult_map]


/-- Caller-supplied capacity evidence includes the retained sign word and
all intermediate peaks of every independently executed stage. -/
structure SignedPowerInvocation (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote) (tail : Stack) where
  prepareCapacity : stackBound powerPrepare ((tail.length+2:Nat):Int) = true
  powerTestCapacity : stackBound checkedUintPow.test ((tail.length+3:Nat):Int) = true
  powerBodyCapacity : stackBound checkedUintPow.body ((tail.length+3:Nat):Int) = true
  resultTestCapacity : stackBound powerPostTest ((tail.length+2:Nat):Int) = true
  resultBodyCapacity : stackBound powerSignBody ((tail.length+2:Nat):Int) = true

theorem SignedPowerInvocation.correct {a : PrimTy.int.Denote} {n : PrimTy.uint.Denote} {tail : Stack}
    (_ : SignedPowerInvocation a n tail) :
    signedPowerExecute (encodeValue .int a::encodeValue .uint n::tail) =
      some (checkedOutcome .int (powerSourceResult a n) tail) := signedPower_correct a n tail

def signedPowerWitness : SignedPowerInvocation
    (⟨-2, by decide⟩ : PrimTy.int.Denote) (⟨3, by decide⟩ : PrimTy.uint.Denote) [99] where
  prepareCapacity := by decide +kernel
  powerTestCapacity := by decide +kernel
  powerBodyCapacity := by decide +kernel
  resultTestCapacity := by decide +kernel
  resultBodyCapacity := by decide +kernel

theorem signedPower_negative_three_source :
    (powerSourceResult (⟨-2, by decide⟩ : PrimTy.int.Denote)
      (⟨3, by decide⟩ : PrimTy.uint.Denote)).map (·.val) = some (-8) := by
  rw [powerSourceResult_map]
  decide +kernel

theorem signedPower_minimum_one_source :
    (powerSourceResult minimumInt (⟨1, by decide⟩ : PrimTy.uint.Denote)).map (·.val) =
      some minimumInt.val := by
  rw [powerSourceResult_map]
  decide +kernel

theorem signedPower_positive_boundary_source :
    (powerSourceResult (⟨2, by decide⟩ : PrimTy.int.Denote)
      (⟨255, by decide⟩ : PrimTy.uint.Denote)).map (·.val) = none := by
  rw [powerSourceResult_map]
  decide +kernel

theorem signedPower_unsigned_overflow_source :
    (powerSourceResult (⟨-2, by decide⟩ : PrimTy.int.Denote)
      (⟨256, by decide⟩ : PrimTy.uint.Denote)).map (·.val) = none := by
  rw [powerSourceResult_map]
  decide +kernel

#print axioms signedPower_negative_three_source
#print axioms signedPower_minimum_one_source
#print axioms signedPower_positive_boundary_source
#print axioms signedPower_unsigned_overflow_source


private def integerPowerOutcome (res : Option Int) (tail : Stack) : Except (List UInt8) Stack :=
  res.elim (.error overflowFailure) (fun z => .ok (BitVec.ofInt 256 z::tail))

private theorem checkedOutcome_int_map (res : Option PrimTy.int.Denote) (tail : Stack) :
    checkedOutcome .int res tail = integerPowerOutcome (res.map (·.val)) tail := by
  cases res <;> rfl

theorem signedPower_negative_three_target (tail : Stack) :
    signedPowerExecute (encodeValue .int (⟨-2, by decide⟩ : PrimTy.int.Denote)::
      encodeValue .uint (⟨3, by decide⟩ : PrimTy.uint.Denote)::tail) =
      some (.ok (BitVec.ofInt 256 (-8)::tail)) := by
  rw [signedPower_correct, checkedOutcome_int_map, signedPower_negative_three_source]
  rfl

theorem signedPower_minimum_one_target (tail : Stack) :
    signedPowerExecute (encodeValue .int minimumInt::
      encodeValue .uint (⟨1, by decide⟩ : PrimTy.uint.Denote)::tail) =
      some (.ok (encodeValue .int minimumInt::tail)) := by
  rw [signedPower_correct, checkedOutcome_int_map, signedPower_minimum_one_source]
  rfl

theorem signedPower_positive_boundary_target (tail : Stack) :
    signedPowerExecute (encodeValue .int (⟨2, by decide⟩ : PrimTy.int.Denote)::
      encodeValue .uint (⟨255, by decide⟩ : PrimTy.uint.Denote)::tail) =
      some (.error overflowFailure) := by
  rw [signedPower_correct, checkedOutcome_int_map, signedPower_positive_boundary_source]
  rfl

theorem signedPower_unsigned_overflow_target (tail : Stack) :
    signedPowerExecute (encodeValue .int (⟨-2, by decide⟩ : PrimTy.int.Denote)::
      encodeValue .uint (⟨256, by decide⟩ : PrimTy.uint.Denote)::tail) =
      some (.error overflowFailure) := by
  rw [signedPower_correct, checkedOutcome_int_map, signedPower_unsigned_overflow_source]
  rfl

#print axioms signedPower_negative_three_target
#print axioms signedPower_minimum_one_target
#print axioms signedPower_positive_boundary_target
#print axioms signedPower_unsigned_overflow_target

#print axioms signedPowerWitness
#print axioms SignedPowerInvocation.correct

#print axioms signedPower_correct
#print axioms powerSourceResult_map
#print axioms signedPower_source
end Solidity.Backend.Scalar
