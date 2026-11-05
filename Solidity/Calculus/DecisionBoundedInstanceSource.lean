import Solidity.Calculus.DecisionBoundedInstance
import Solidity.Calculus.ExactUpdates
import Solidity.Calculus.ParameterReduction
import Solidity.Calculus.HashPremise

/-! # Actual source transport for bounded literal-instance certificates
Every producer certificate is concrete and retains its original meaning. No
collector, coverage or exhaustive source theorem is supplied by this interface.
-/
namespace Solidity.Decide

/-- Close the real positive prefix and reverse each actual preparation stage. -/
theorem boundedUIntInstance_source_valid {C : Contract} {φ : Fml C []}
    (r : SourceReduction φ) (u : UniversalPrefix r.leaf.elim.condSimp.prenex)
    {value : PrimTy.uint.Denote} (w : BoundedUIntLiteralInstance u.body value) :
    Fml.Valid φ := by
  intro σ
  have hp : r.leaf.elim.condSimp.prenex.holds σ AEnv.dflt :=
    u.close σ AEnv.dflt (fun ν => w.valid σ ν)
  have hc : r.leaf.elim.condSimp.holds σ AEnv.dflt :=
    (LFml.prenex_holds σ _ _).mp hp
  have he : r.leaf.elim.holds σ AEnv.dflt := (LFml.condSimp_holds σ _ _).mp hc
  exact (r.elim_holds_iff σ).mp he

/-- The existing hash-free interface is explicit and unchanged. -/
theorem boundedUIntInstance_source_validH {C : Contract} {φ : Fml C []}
    (r : SourceReduction φ) (u : UniversalPrefix r.leaf.elim.condSimp.prenex)
    {value : PrimTy.uint.Denote} (w : BoundedUIntLiteralInstance u.body value)
    (hh : φ.hasHash = false) : Fml.ValidH φ :=
  (Fml.validH_iff hh).mpr (boundedUIntInstance_source_valid r u w)

end Solidity.Decide
