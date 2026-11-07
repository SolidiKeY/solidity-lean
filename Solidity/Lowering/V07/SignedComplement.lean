import Solidity.Lowering.V07.SignedNarrowSubtraction

/-! Signed bitwise complement at every approved width, using the existing
signed subtraction value program with leading literal -1. No opcode compiler,
new value representation or Source admission claim is introduced. -/
namespace Solidity.Lowering.V07.SignedComplement
open SignedWidthCasts (ty)

def complementValue {C : Contract} {Γ : Ctx} (bits : Nat) (v : Val C Γ .int) : Val C Γ .int :=
  SignedNarrowSubtraction.subValue bits (.simple (.lit (-1) (by decide))) v

theorem minus_one_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).lo ≤ -1 ∧ -1 ≤ (ty bits valid).hi := by
  have h := Source.two_pow_pos (bits-1)
  change -((2^(bits-1) : Nat) : Int) ≤ -1 ∧ -1 ≤ ((2^(bits-1)-1 : Nat) : Int)
  omega

theorem source_value (checked : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) {D : Source.Layout}
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    Source.unaryVal checked .bitNot (.int x hx : Source.Val D (.int (ty bits valid))) =
      .ok (Source.intWrap (ty bits valid) (-x-1)) := by rfl

theorem value_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (v : Val C Γ .int)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : v.evalT target = .ok (integerValue (ty bits valid) x hx)) :
    (complementValue bits v).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1))
        ((ty bits valid).wrap_mem (-x-1))) := by
  have result := SignedNarrowSubtraction.sub_value_run bits valid target
    (.simple (.lit (-1) (by decide))) v (-1) x (minus_one_range bits valid) hx rfl read
  have arithmetic : -1-x = -x-1 := by omega
  simpa only [complementValue,arithmetic] using result

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
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
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

end Solidity.Lowering.V07.SignedComplement

/-- info: 'Solidity.Lowering.V07.SignedComplement.minus_one_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplement.minus_one_range

/-- info: 'Solidity.Lowering.V07.SignedComplement.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplement.source_value

/-- info: 'Solidity.Lowering.V07.SignedComplement.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplement.value_run

/-- info: 'Solidity.Lowering.V07.SignedComplement.source_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplement.source_of_run

/-- info: 'Solidity.Lowering.V07.SignedComplement.local_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedComplement.local_transport
