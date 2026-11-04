import Solidity.Lowering.V07.UnsignedWidthCasts

/-! Unsigned complement uses the actual intrinsic word complement followed by
width narrowing. These operational clauses do not claim frontend admission. -/
namespace Solidity.Lowering.V07.UnsignedComplement
open UnsignedNarrowing (ty)

def complementValue {C : Contract} {Γ : Ctx} (bits : Nat) (v : Val C Γ .uint) : Val C Γ .uint :=
  UnsignedCasts.castValue bits (.unop .bnot rfl rfl v)

theorem word_wrap (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi) :
    Source.IntTy.u256.wrap (-x-1) = Semantics.uintBound-1-x := by
  change 0 ≤ x ∧ x ≤ ((2^256-1 : Nat) : Int) at hx
  change (-x-1) % Semantics.uintBound = _
  rw [← Int.add_emod_left Semantics.uintBound (-x-1)]
  have h : Semantics.uintBound + (-x-1) = Semantics.uintBound-1-x := by omega
  rw [h]
  apply Int.emod_eq_of_lt <;> unfold Semantics.uintBound <;> omega

theorem word_eval (x : PrimTy.uint.Denote) :
    UnOp.evalT .bnot rfl x = some (integerValue Source.IntTy.u256
      (Source.IntTy.u256.wrap (-x.val-1)) (Source.IntTy.u256.wrap_mem (-x.val-1))) := by
  have hx := integer_range Source.IntTy.u256 (Source.IntTy.u256.wrap (-x.val-1))
    (Source.IntTy.u256.wrap_mem (-x.val-1))
  have bounds : Source.IntTy.u256.lo ≤ x.val ∧ x.val ≤ Source.IntTy.u256.hi := by
    have h := x.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    change 0 ≤ x.val ∧ x.val ≤ ((2^256-1 : Nat) : Int)
    change 0 ≤ x.val ∧ x.val < Semantics.uintBound at h
    unfold Semantics.uintBound at h
    omega
  rw [word_wrap x.val bounds] at hx
  have canonical : integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (-x.val-1))
      (Source.IntTy.u256.wrap_mem (-x.val-1)) = (⟨Semantics.uintBound-1-x.val,hx⟩ : PrimTy.uint.Denote) :=
    Subtype.ext (word_wrap x.val bounds)
  rw [canonical]
  change PrimTy.uint.inRange (Semantics.uintBound-1-x.val) = true at hx
  change PrimTy.uint.ofInt? (Semantics.uintBound-1-x.val) = some ⟨_,hx⟩
  simp only [PrimTy.ofInt?,dif_pos hx]

theorem source_value (checked : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {D : Source.Layout}
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    Source.unaryVal checked .bitNot (.int x hx : Source.Val D (.int (ty bits valid))) =
      .ok (Source.intWrap (ty bits valid) (-x-1)) := by rfl

theorem value_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (v : Val C Γ .uint)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : v.evalT target = .ok (integerValue (ty bits valid) x hx)) :
    (complementValue bits v).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1))
        ((ty bits valid).wrap_mem (-x-1))) := by
  have raw : (Val.unop .bnot rfl rfl v).evalT target =
      .ok (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (-x-1))
        (Source.IntTy.u256.wrap_mem (-x-1))) := by
    rw [Val.evalT,read]
    change TRes.ofOpt (UnOp.evalT .bnot rfl (integerValue (ty bits valid) x hx)) = _
    rw [word_eval]
    rfl
  have result := UnsignedCasts.value_run target bits valid (.unop .bnot rfl rfl v)
    (Source.IntTy.u256.wrap (-x-1)) (Source.IntTy.u256.wrap_mem (-x-1)) raw
  have narrow : (ty bits valid).wrap (Source.IntTy.u256.wrap (-x-1)) =
      (ty bits valid).wrap (-x-1) := UnsignedNarrowing.word_then_narrow bits valid.2.2 (-x-1)
  simpa only [complementValue,narrow] using result

theorem source_of_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (e : Source.RExpr E Γ (.int (ty bits valid)))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.unary .bitNot e)).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (-x-1))),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

/-- The local source read and target input evaluation follow from the initial
family. Complement is valid in both checked and unchecked frames. -/
theorem local_transport (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (k : ι) (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get (si k) = .int x hx) :
    (Source.evalE G F (fuel+2) (.unary .bitNot (.local (si k)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (-x-1))),source) ∧
    (complementValue bits (.simple (.local (ti k)))).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1))
        ((ty bits valid).wrap_mem (-x-1))) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (-x-1) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1))
        ((ty bits valid).wrap_mem (-x-1))) := by
  have input := source_local_transport G F fuel source target (ty bits valid) (si k) (ti k)
    x hx read (family.read k x hx read)
  exact ⟨source_of_run bits valid G F (fuel+1) source source (.local (si k)) x hx input.1,
    value_run bits valid target (.simple (.local (ti k))) x hx input.2.1,integer_related _ _ _⟩

end Solidity.Lowering.V07.UnsignedComplement

/-- info: 'Solidity.Lowering.V07.UnsignedComplement.word_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedComplement.word_wrap

/-- info: 'Solidity.Lowering.V07.UnsignedComplement.word_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedComplement.word_eval

/-- info: 'Solidity.Lowering.V07.UnsignedComplement.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedComplement.source_value

/-- info: 'Solidity.Lowering.V07.UnsignedComplement.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedComplement.value_run

/-- info: 'Solidity.Lowering.V07.UnsignedComplement.source_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedComplement.source_of_run

/-- info: 'Solidity.Lowering.V07.UnsignedComplement.local_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedComplement.local_transport
