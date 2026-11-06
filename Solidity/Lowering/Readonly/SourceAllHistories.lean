import Solidity.Lowering.Readonly.SourceCallAddressEffects
import Solidity.Lowering.Readonly.SourceStatementEffects
import Solidity.Lowering.Readonly.SourceEnvironmentEffects
import Solidity.Lowering.Readonly.CallbackFrame

/-! Closed mutual Source journal-history induction. Only Source execution is
covered; no frontend/capture/native/target representation adequacy follows. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env}
theorem all_at (global : Glob E) (n : Nat) : At global n := by
  induction n with
  | zero => exact at_zero global
  | succ n ih =>
    exact {
      evalE := by intro F Γ τ e; exact evalE_succ global F n ih e
      evalPair := by intro F Γ σ τ a b; exact evalPair_succ global F n ih a b
      evalArgs := by intro F Γ τs es; exact evalArgs_succ global F n ih es
      evalConvArgs := by intro F Γ τs es; exact evalConvArgs_succ global F n ih es
      evalLoc := by intro F Γ τ l; exact evalLoc_succ global F n ih l
      evalBuiltin := by intro F Γ σs b args τ; exact evalBuiltin_succ global F n ih b args τ
      evalArgsRev := by intro F Γ τs es; exact evalArgsRev_succ global F n ih es
      pay := by intro F Γ a v; exact pay_succ global F n ih a v
      execS := by intro F nps ph R M k Γ Γ' s l; exact execS_succ global F n ih nps ph s l
      forIter := by intro F nps ph R M u Γ₁ Γ₂ c post body l; exact forIter_succ global F n ih nps ph c post body l
      execItems := by intro F nps ph R M k Γ Γ' b l; exact execItems_succ global F n ih nps ph b l
      runMods := by intro F b mods l; exact runMods_succ global F n ih b mods l
      callInternal := by intro F d ps vs rs; exact callInternal_succ global F n ih d vs rs
      callAddr := by intro F a v input requested; exact callAddr_succ global F n ih a v input requested
      enterInstance := by
        intro a sender v input mode code depth entry credited prior
        exact CallbackFrame.enter_history global n
          (fun F bytes state => ih.dispatch F bytes (L0 E) state)
          entry credited a sender v input mode code depth prior
      envLoop := by intro depth mode; exact envLoop_succ global n ih depth mode
      dispatch := by intro F input; exact dispatch_succ global F n ih input
    }

/-- Actual admitted callbacks, with their credit and live child checkpoint,
are now produced rather than postulated. -/
theorem all_callbacks (global : Glob E) (mode : Bool) (bound : Nat) :
    EnvironmentHistory.CallbackHistories global mode bound := by
  apply CallbackFrame.callbacks
  intro n _below F input state
  exact (all_at global n).dispatch F input (L0 E) state

/-- All actual source calls in effective static mode preserve typed storage.
Balances, ledger, logs, memory and return bytes are not concluded equal. -/
theorem static_call_storage (global : Glob E) (frame : Fr) (n : Nat)
    (receiver : Solidity.Roadmap.Address) (value : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (requested : Bool) (state : St E)
    (static : (requested || frame.static) = true) :
    StaticJournal.SameStorage
      ((callAddr global frame n receiver value input requested).run (L0 E,state)).2.2.ex state.ex :=
  ((all_at global n).callAddr frame receiver value input requested (L0 E) state).storage static
end Solidity.Lowering.Readonly.SourceHistory
