import Solidity.Backend.PrimitivePackets.BitNot.Selected
import Solidity.Backend.Passes.ValueCertificate

/-! Actual selected unsigned NOT execution, including width narrowing. The
existing full represented state and arbitrary saved stack are retained. No
requested code, desired execution or favourable poststate is a premise. -/
namespace Solidity.Backend.PrimitivePackets.BitNot
open Evm Evm.Memory Solidity.Lowering.V07
open UnsignedNarrowing (ty)

theorem value_success {C : Contract} {Γ : Ctx} (s : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i : Idx Γ (.val .uint)) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get i s.env = integerValue (ty bits valid) x hx) :
    (value bits i).evalT s = .ok (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1))
      ((ty bits valid).wrap_mem (-x-1))) := by
  apply UnsignedComplement.value_run bits valid s (.simple (.local i)) x hx
  simp only [Val.evalT,Simple.evalT,read]

theorem target_success {C : Contract} {Γ : Ctx} {offset L frame : Nat} {F : Frag Γ}
    (s : State C Γ) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i : Idx Γ (.val .uint)) (x : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get i s.env = integerValue (ty bits valid) x hx)
    {base : Nat → Fin W} {m : Machine} (represented : StateRepr L offset frame F s base m)
    (tail : List Word) :
    ∃ word, ReprV .uint (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1))
        ((ty bits valid).wrap_mem (-x-1))) word ∧
      run (selected (C:=C) bits offset F i).code {m with stack := tail} =
        .ok ({m with stack := tail}.push word) 0 := by
  exact Backend.Passes.value_success_tail (selected (C:=C) bits offset F i) represented
    (value_success s bits valid i x hx read) tail
end Solidity.Backend.PrimitivePackets.BitNot

/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.value_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.value_success
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.target_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.target_success
