import Solidity.Lowering.Readonly.SourceKnownStatementEffects
import Solidity.Lowering.Readonly.SourceKnownLibraryEffects

/-! Closed Source journal induction for the real delegated calldata guard.
Regression purpose: library try is covered without strengthening the frozen
seventeen-field history premise or assuming a child/storage frame.
This proves journal histories only, not admission or physical ABI adequacy. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env}

/-- Every actual evaluator component preserves guarded journal ancestry in
both calldata modes, at every horizon and for every Source global. -/
theorem all_known_at (global : Glob E) (n : Nat) : KnownAt global n := by
  induction n with
  | zero => exact known_at_zero global
  | succ n ih =>
    exact {
      evalE := by intro known F Γ τ e; exact evalE_succ_known global F n known ih e
      evalPair := by intro known F Γ σ τ a b; exact evalPair_succ_known global F n known ih a b
      evalArgs := by intro known F Γ τs es; exact evalArgs_succ_known global F n known ih es
      evalConvArgs := by intro known F Γ τs es; exact evalConvArgs_succ_known global F n known ih es
      evalLoc := by intro known F Γ τ l; exact evalLoc_succ_known global F n known ih l
      evalBuiltin := by intro known F Γ σs b args τ; exact evalBuiltin_succ_known global F n known ih b args τ
      evalArgsRev := by intro known F Γ τs es; exact evalArgsRev_succ_known global F n known ih es
      pay := by intro known F Γ a v; exact pay_succ_known global F n known ih a v
      execS := by intro known F nps ph R M k Γ Γ' s l; exact execS_succ_known global F n known ih nps ph s l
      forIter := by intro known F nps ph R M u Γ₁ Γ₂ c post body l; exact forIter_succ_known global F n known ih nps ph c post body l
      execItems := by intro known F nps ph R M k Γ Γ' b l; exact execItems_succ_known global F n known ih nps ph b l
      runMods := by intro known F b mods l; exact runMods_succ_known global F n known ih b mods l
      callInternal := by intro known F d ps vs rs; exact callInternal_succ_known global F n known ih d vs rs
      callAddr := by intro F a v input requested; exact callAddr_succ global F n ih.toAt a v input requested
      enterInstance := by
        intro a sender v input mode code depth entry credited prior
        exact CallbackFrame.enter_history global n
          (fun F bytes state => ih.dispatch F bytes (L0 E) state)
          entry credited a sender v input mode code depth prior
      envLoop := by intro depth mode; exact envLoop_succ global n ih.toAt depth mode
      dispatch := by intro F input; exact dispatch_succ global F n ih.toAt input
      callLibrary := by intro F d ps values rs; exact callLibrary_succ_known global F n ih d values rs
    }

end Solidity.Lowering.Readonly.SourceHistory

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.all_known_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.all_known_at
