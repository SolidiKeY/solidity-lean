import Solidity.Backend.PrimitivePackets.CheckedAdd.Source
import Solidity.Backend.PrimitivePackets.CheckedAdd.Selected
import Solidity.Backend.Passes.ValueCertificate

/-! Actual selected checked-add target execution. Overflow uses the original
coarse Evm.Out.revert, which carries no payload or final machine. No equality
between this target verdict and Source panic bytes is claimed. -/
namespace Solidity.Backend.PrimitivePackets.CheckedAdd
open Evm Evm.Memory Solidity.Lowering.V07

theorem value_success {C : Contract} {Γ : Ctx} (s : State C Γ)
    (a b : Idx Γ (.val .uint)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : TEnv.get a s.env = integerValue U x hx)
    (hb : TEnv.get b s.env = integerValue U y hy)
    (fits : U.lo ≤ x+y ∧ x+y ≤ U.hi) :
    (value a b).evalT s = .ok (integerValue U (x+y) fits) := by
  simp only [value,Val.evalT,Simple.evalT,ha,hb,BinOp.shortT,bind,Except.bind]
  change TRes.ofOpt (PrimTy.uint.ofInt? (x+y)) = _
  have hr : PrimTy.uint.inRange (x+y) = true := integer_range U (x+y) fits
  simp only [PrimTy.ofInt?,dif_pos hr,TRes.ofOpt]
  first | rfl | simp only [integerValue,U]

theorem value_overflow {C : Contract} {Γ : Ctx} (s : State C Γ)
    (a b : Idx Γ (.val .uint)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : TEnv.get a s.env = integerValue U x hx)
    (hb : TEnv.get b s.env = integerValue U y hy)
    (overflow : ¬ (U.lo ≤ x+y ∧ x+y ≤ U.hi)) :
    (value a b).evalT s = .error .revert := by
  simp only [value,Val.evalT,Simple.evalT,ha,hb,BinOp.shortT,bind,Except.bind]
  change TRes.ofOpt (PrimTy.uint.ofInt? (x+y)) = _
  have hr : PrimTy.uint.inRange (x+y) ≠ true := by
    intro h
    simp only [PrimTy.inRange,decide_eq_true_eq] at h
    change ¬ (0 ≤ x+y ∧ x+y ≤ Semantics.uintBound-1) at overflow
    apply overflow
    change 0 ≤ x+y ∧ x+y ≤ Semantics.uintBound-1
    change 0 ≤ x+y ∧ x+y < Semantics.uintBound at h
    omega
  simp only [PrimTy.ofInt?,dif_neg hr,TRes.ofOpt]

theorem target_success {C : Contract} {Γ : Ctx} {offset L frame : Nat} {F : Frag Γ}
    (s : State C Γ) (a b : Idx Γ (.val .uint)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : TEnv.get a s.env = integerValue U x hx)
    (hb : TEnv.get b s.env = integerValue U y hy)
    (fits : U.lo ≤ x+y ∧ x+y ≤ U.hi)
    {base : Nat → Fin W} {m : Machine} (represented : StateRepr L offset frame F s base m)
    (tail : List Word) :
    ∃ word, ReprV .uint (integerValue U (x+y) fits) word ∧
      run (selected (C:=C) offset F a b).code {m with stack := tail} =
        .ok ({m with stack := tail}.push word) 0 := by
  exact Backend.Passes.value_success_tail (selected (C:=C) offset F a b) represented
    (value_success s a b x y hx hy ha hb fits) tail

theorem target_overflow {C : Contract} {Γ : Ctx} {offset L frame : Nat} {F : Frag Γ}
    (s : State C Γ) (a b : Idx Γ (.val .uint)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : TEnv.get a s.env = integerValue U x hx)
    (hb : TEnv.get b s.env = integerValue U y hy)
    (overflow : ¬ (U.lo ≤ x+y ∧ x+y ≤ U.hi))
    {base : Nat → Fin W} {m : Machine} (represented : StateRepr L offset frame F s base m)
    (tail : List Word) :
    run (selected (C:=C) offset F a b).code {m with stack := tail} = .revert := by
  exact (Backend.Passes.value_revert_iff (selected (C:=C) offset F a b) represented tail).mpr
    (value_overflow s a b x y hx hy ha hb overflow)
end Solidity.Backend.PrimitivePackets.CheckedAdd
