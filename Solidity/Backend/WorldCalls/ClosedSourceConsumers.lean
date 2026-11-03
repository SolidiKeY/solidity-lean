import Solidity.Backend.WorldCalls.ClosedSourceFrame

/-! Consumers of closed Source histories. Target Step/execution/correspondence
remain producer inputs; this adapter supplies only the proved Source P2 history.
No original-site, native, target-world or Core representation is inferred. -/
namespace Solidity.Backend.WorldCalls.ClosedSourceConsumers
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

/-- Existing target/source producer inputs, without an independent history premise.
Step may still be empty: this constructor is not a target completeness theorem. -/
def premises (i : InvocationFrame.Invocation E Γ dn ps rs) (code : Code)
    (Observed : Identity → Evm.Machine → Evm.Out → Except Halt Outcome → Prop)
    (Step : Identity → Evm.Machine → Except Halt Outcome → St E → Evm.Out → Prop)
    (bound : ∀ key initial raw final target, Step key initial raw final target → key = identity i)
    (execution : ∀ key initial raw final target, Step key initial raw final target → Evm.run code.full initial = target)
    (observed : ∀ key initial raw final target, Step key initial raw final target → Observed key initial target raw)
    (phaseRun : ∀ key initial raw final target, Step key initial raw final target →
      (Solidity.Lowering.V08.SourceCallPhase.raw i.global i.frame i.horizon
        (SourceBridge.request i)).run i.after = (raw, (i.after.1, final))) : Premises i :=
  SourceBridge.premises i code Observed Step bound execution observed phaseRun
    (fun key initial raw final target step =>
      ClosedSourceFrame.history_of_raw i raw final
        ((SourceBridge.raw_iff i raw final).mp (phaseRun key initial raw final target step)))

/-- Explicit functional Source/Core storage representation remains required. -/
theorem typed_storage (i : InvocationFrame.Invocation E Γ dn ps rs)
    (raw : Except Halt Outcome) (final : St E) (actual : i.RawAt raw final)
    (mode : i.mode = true) {C : Contract}
    (rep : InvocationFrame.StorageRepresentation E C i.frame.this)
    (before after : Solidity.Storage C)
    (entry : rep.relates (i.after.2.ex.world.accounts i.frame.this).storage before)
    (exit : rep.relates (final.ex.world.accounts i.frame.this).storage after) : after = before :=
  InvocationFrame.typed_storage i raw final actual
    (ClosedSourceFrame.frames_of_raw i raw final actual mode) rep before after entry exit

/-- Actual Source callbacks at every bound; not a target execution theorem. -/
theorem source_environment (global : Glob E) (mode : Bool) (n depth : Nat) (state : St E) :
    StaticJournal.History state.ex mode
      ((envLoop global n depth mode).run (L0 E,state)).2.2.ex :=
  (SourceHistory.all_at global n).envLoop depth mode (L0 E) state
end Solidity.Backend.WorldCalls.ClosedSourceConsumers
