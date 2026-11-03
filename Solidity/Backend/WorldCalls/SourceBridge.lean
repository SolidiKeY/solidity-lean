import Solidity.Backend.WorldCalls.Premises
import Solidity.Lowering.V08.SourceCallPhase

/-! Same-capture P3 bridge to the actual Source raw phase. P2 histories and
actual target execution/observation remain explicit, independently checked
producer inputs; they are not inferred from successful decoding or labels. -/
namespace Solidity.Backend.WorldCalls.SourceBridge
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
namespace Phase
abbrev API := Solidity.Lowering.V08.SourceCallPhase.Request
end Phase
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

def point (i : InvocationFrame.Invocation E Γ dn ps rs) :
    Solidity.Lowering.V08.SourceCallPhase.Point E Γ :=
  ⟨i.frame, i.after.1, i.after.2⟩

def request (i : InvocationFrame.Invocation E Γ dn ps rs) : Phase.API :=
  ⟨i.captured.receiver, i.captured.value, i.captured.input, i.requested⟩

/-- The raw request uses the live post-argument state and exact captured values. -/
theorem raw_iff (i : InvocationFrame.Invocation E Γ dn ps rs)
    (raw : Except Halt Outcome) (final : St E) :
    (Solidity.Lowering.V08.SourceCallPhase.raw i.global i.frame i.horizon (request i)).run i.after =
      (raw, (i.after.1, final)) ↔ i.RawAt raw final := by
  have phase := Solidity.Lowering.V08.SourceCallPhase.raw_run i.global (point i) i.horizon (request i)
  dsimp only [point] at phase
  simp only [Prod.eta] at phase
  rw [phase]
  unfold InvocationFrame.Invocation.RawAt
  cases h : (callAddr i.global i.frame i.horizon i.captured.receiver i.captured.value
    i.captured.input i.requested).run (L0 E, i.after.2) with
  | mk result reached =>
    rcases reached with ⟨locals, state⟩
    cases locals
    cases result <;> cases raw <;> simp only [request, L0, h]
    all_goals constructor <;> intro eq <;> cases eq <;> rfl

/-- Actual evaluation, not an arbitrary raw outcome supplied by a client. -/
def evaluated (i : InvocationFrame.Invocation E Γ dn ps rs) : Except Halt Outcome × St E :=
  let reached := (callAddr i.global i.frame i.horizon i.captured.receiver i.captured.value
    i.captured.input i.requested).run (L0 E, i.after.2)
  (reached.1, reached.2.2)

/-- Every invocation has its exact deterministic pre-decoder result, including halts. -/
theorem evaluated_raw (i : InvocationFrame.Invocation E Γ dn ps rs) :
    i.RawAt (evaluated i).1 (evaluated i).2 := by
  unfold InvocationFrame.Invocation.RawAt evaluated
  cases h : (callAddr i.global i.frame i.horizon i.captured.receiver i.captured.value
    i.captured.input i.requested).run (L0 E, i.after.2) with
  | mk raw reached =>
    rcases reached with ⟨locals, state⟩
    cases locals
    rfl

theorem evaluated_phase (i : InvocationFrame.Invocation E Γ dn ps rs) :
    (Solidity.Lowering.V08.SourceCallPhase.raw i.global i.frame i.horizon (request i)).run i.after =
      ((evaluated i).1, (i.after.1, (evaluated i).2)) :=
  (raw_iff i _ _).mpr (evaluated_raw i)

/-- A completed capture is tied to the same actual raw execution, before decoding. -/
theorem captured (i : InvocationFrame.Invocation E Γ dn ps rs) (out : Outcome) (final : St E)
    (run : (Solidity.Lowering.V08.SourceCallPhase.raw i.global i.frame i.horizon (request i)).run i.after =
      (.ok out, (i.after.1, final))) :
    (Solidity.Lowering.V08.SourceCallPhase.capture i.global i.frame i.horizon (request i)).run i.after =
      (.ok (out, final), (i.after.1, final)) := by
  have phase := Solidity.Lowering.V08.SourceCallPhase.capture_run i.global (point i) i.horizon (request i)
  dsimp only [point] at phase
  simp only [Prod.eta] at phase
  rw [phase, run]

/-- Construct the compiler consumer boundary from actual same-invocation raw
phase equations. No P1 or P10 execution implementation is invented here. -/
def premises (i : InvocationFrame.Invocation E Γ dn ps rs) (code : Code)
    (Observed : Identity → Evm.Machine → Evm.Out → Except Halt Outcome → Prop)
    (Step : Identity → Evm.Machine → Except Halt Outcome → St E → Evm.Out → Prop)
    (bound : ∀ key initial raw final target, Step key initial raw final target → key = identity i)
    (execution : ∀ key initial raw final target, Step key initial raw final target → Evm.run code.full initial = target)
    (observed : ∀ key initial raw final target, Step key initial raw final target → Observed key initial target raw)
    (phaseRun : ∀ key initial raw final target, Step key initial raw final target →
      (Solidity.Lowering.V08.SourceCallPhase.raw i.global i.frame i.horizon (request i)).run i.after =
        (raw, (i.after.1, final)))
    (history : ∀ key initial raw final target, Step key initial raw final target →
      StaticJournal.History i.after.2.ex i.mode final.ex) : Premises i where
  code := code
  Observed := Observed
  Step := Step
  bound := bound
  execution := execution
  observed := observed
  sourceRaw := fun key initial raw final target step => (raw_iff i raw final).mp (phaseRun key initial raw final target step)
  p2History := history

/-- The P3 raw producer plus an independently supplied P2 history transports
only persistent storage through the explicit functional representation. -/
theorem static_storage (i : InvocationFrame.Invocation E Γ dn ps rs)
    (raw : Except Halt Outcome) (final : St E)
    (run : (Solidity.Lowering.V08.SourceCallPhase.raw i.global i.frame i.horizon (request i)).run i.after =
      (raw, (i.after.1, final)))
    (frames : i.RuntimeFrames final) {C : Contract}
    (rep : InvocationFrame.StorageRepresentation E C i.frame.this)
    (before after : Solidity.Storage C)
    (entry : rep.relates (i.after.2.ex.world.accounts i.frame.this).storage before)
    (exit : rep.relates (final.ex.world.accounts i.frame.this).storage after) : after = before :=
  InvocationFrame.typed_storage i raw final ((raw_iff i raw final).mp run) frames rep before after entry exit

end Solidity.Backend.WorldCalls.SourceBridge
