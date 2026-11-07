import Solidity.Calculus.DecisionNumericTwoPrefix
import Solidity.Calculus.DecisionNumericLogic

/-! # Two-prefix equality source producer
Both actual source polarities produce the same numeric body. Optional equality,
normalization identities and the source-derived body-size estimate are retained.
This does not assume a future source/coverage bridge or change any fuel.
-/
namespace Solidity.Decide

/-- Equality over two real uint locals has one actual numeric leaf at either
polarity, bounded by the operands' source sizes without a fixed node premise. -/
theorem uintTwoPrefix_eq_sourceBound {C : Contract}
    {a b : Tm C [.val .uint, .val .uint] (.val .uint)}
    (ha : a.UIntLinear) (hb : b.UIntLinear) :
    ∃ ψ : LFml C,
      (Fml.eq a b).toLS true (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some ψ ∧
      (Fml.eq a b).toLS false (((SymS.init (C := C)).pushQ .uint).pushQ .uint) = some ψ ∧
      ψ.UIntQF (fun q => q = ⟨.uint, 0⟩ ∨ q = ⟨.uint, 1⟩) (fun _ => False) ∧
      ψ.elim = ψ ∧ ψ.condSimp = ψ ∧ ψ.nodes ≤ 7 * (a.size + b.size) + 13 := by
  obtain ⟨x, hx, hNx, hEx, hCx, hSx⟩ := uintLinear_two_prefix_sourceBound ha
  obtain ⟨y, hy, hNy, hEy, hCy, hSy⟩ := uintLinear_two_prefix_sourceBound hb
  rw [toLT_eq_toL_of_agree a _ (uintLinear_agrees ha)] at hx
  rw [toLT_eq_toL_of_agree b _ (uintLinear_agrees hb)] at hy
  have hfix : (Fml.eqAt true a b x y).elim = Fml.eqAt true a b x y ∧
      (Fml.eqAt true a b x y).condSimp = Fml.eqAt true a b x y :=
    uintEq_fixed ha hb hEx hEy hCx hCy
  refine ⟨Fml.eqAt true a b x y, ?_, ?_, uintEq_logic ha hb hNx hNy,
    hfix.1, hfix.2, ?_⟩
  · change (a.toL _).bind (fun u => (b.toL _).map (fun v => Fml.eqAt true a b u v)) = _
    rw [hx, hy]
    rfl
  · change (a.toL _).bind (fun u => (b.toL _).map (fun v => Fml.eqAt false a b u v)) = _
    rw [hx, hy]
    exact congrArg some (uintLinear_eqAt_polarity ha hb x y false)
  · have hbnd : (Fml.eqAt true a b x y).elim.condSimp.prenex.nodes ≤
        7 * x.nodes + 7 * y.nodes + 13 := uintEq_prepared_nodes_le ha hb hEx hEy hCx hCy
    rw [hfix.1, hfix.2, (uintEq_logic ha hb hNx hNy).prenex_fixed] at hbnd
    omega

end Solidity.Decide
