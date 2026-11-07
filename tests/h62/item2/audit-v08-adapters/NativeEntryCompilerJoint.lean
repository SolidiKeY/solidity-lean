import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Lowering.V08.Controls

/-! Regression: an explicitly supplied V08 entry body still needs actual native
compiler acceptance and inhabited machine premises. Reuse the published generic
totality result on the existing two-write body, not a new accepted-code table.
This is intrinsic/native compiler backfill, not independent Source admission,
entry dispatch/payment compilation or a full H68 world-phase certificate. -/
namespace H62.AuditV08Adapters.NativeEntryCompilerJoint
open Solidity
open Solidity.Evm
open Solidity.Backend.AbiWorld.PublicCompilerTotal
open Solidity.Lowering.V08

/-- The existing V08 body, with both actual storage roots, is in the published domain. -/
theorem body_supported : ProgOk [] Controls.entry.body := by
  exact .cons (.assign (.root _ _) (.lit _ _))
    (.cons (.assign (.root _ _) (.lit _ _)) .nil)

/-- Actual public compiler acceptance at every base, without an acceptance premise. -/
theorem accepted (base : Nat) :
    (Compiler.compile base (Frag.init []) Controls.entry.body).isSome = true :=
  compile_init base body_supported

theorem not_reject_all (base : Nat) :
    Compiler.compile base (Frag.init []) Controls.entry.body ≠ none := by
  intro rejected
  have yes := accepted base
  rw [rejected] at yes
  cases yes

/-- The public observation is reached from the published genuine fresh Sim,
not assumed as a favourable target execution equation. -/
theorem agrees_fresh :
    ∃ result, Compiler.compile 0 (Frag.init []) Controls.entry.body = some result ∧
      ∀ (frame : Nat) (base : Nat → Fin W), result.Agrees 1 frame base
        (freshT Controls.Cell 0 W_pos ⟨0,W_pos⟩)
        (Machine.init (fun _ => 0) ⟨0,W_pos⟩) := by
  obtain ⟨result, accepted, agrees⟩ := compile_agrees 0 (Matches.init []) body_supported
  exact ⟨result, accepted, fun frame base =>
    agrees 1 frame base _ _
      (Sim.init Controls.Cell 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl)
      (by unfold Lmax; decide +kernel)⟩

#print axioms body_supported
#print axioms accepted
#print axioms not_reject_all
#print axioms agrees_fresh
end H62.AuditV08Adapters.NativeEntryCompilerJoint
