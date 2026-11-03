import Solidity.Yul.World.CallbackSuccessChecks

/-! Arbitrary caller-state boundary for the actual selected source fallback.
The program input is explicit; no general dispatch adequacy is assumed. -/
namespace Solidity.Yul.World.InstanceBoundary
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Roadmap (Outcome)
open Solidity.Yul.World.CallbackSuccess

theorem dispatch_exact (G : Glob env) (out : Outcome) (s : Source.EMState env []) :
    (Source.dispatch (callbackGlob G out)
      {this:=CallerFrameChecks.receiver,sender:=CallerFrameChecks.target,value:=7,static:=false,contract:="Finite",checked:=true,depth:=2,cd:=[]} 10 []).run s =
      (.ok [],s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem instance_exact (G : Glob env) (out : Outcome) {Γ} (s : Source.EMState env Γ) :
    CallerFrame.runInstance (callbackGlob G out) s 10 CallerFrameChecks.receiver CallerFrameChecks.target
      7 [] false "Finite" 2 = (.ok (.success [],Source.L0 env),s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

/-- Already-entered instance body: value transfer/credit belongs to the caller
entry path. This body performs no such transfer and has no LOG/emit. -/
theorem full_carrier (G : Glob env) (out : Outcome) {Γ}
    (c : PhysicalCompletion.Carrier env Γ) :
    (let run := CallerFrame.runInstance (callbackGlob G out) c.1.1 10 CallerFrameChecks.receiver
      CallerFrameChecks.target 7 [] false "Finite" 2
     (run.1.map Prod.fst,(⟨⟨run.2,c.1.2⟩,c.2⟩ : PhysicalCompletion.Carrier env Γ))) =
      (.ok (.success []),c) := by
  rw [instance_exact]
  cases c with | mk body enc => cases body; rfl

theorem instance_timeout_exact (G : Glob env) (out : Outcome) {Γ} (s : Source.EMState env Γ) :
    CallerFrame.runInstance (callbackGlob G out) s 4 CallerFrameChecks.receiver CallerFrameChecks.target
      7 [] false "Finite" 2 = (.error .timeout,s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

/-- Commit of this actual unchanged body preserves the whole physical carrier
and ordered trace; only the completed empty return buffer is installed. -/
theorem completed (G : Glob env) (out : Outcome) {Γ}
    (c : PhysicalCompletion.Carrier env Γ) (o : ObservedEffects env.layout env.lay env.lay)
    (f : ResidualFrame) :
    (let run := CallerFrame.runInstance (callbackGlob G out) c.1.1 10 CallerFrameChecks.receiver
      CallerFrameChecks.target 7 [] false "Finite" 2
     PhysicalCompletion.finish c.1.1 c.2 o f ⟨⟨run.2,c.1.2⟩,c.2⟩ [] (.success [])) =
      (c,⟨⟨c.1.1.2.ex,committedLogs o.trace,[]⟩,o.trace,rfl⟩) := by
  rw [instance_exact]
  simp only [PhysicalCompletion.finish_success,List.append_nil]

theorem nonempty_instance (G : Glob env) out :
    CallerFrame.runInstance (callbackGlob G out) caller 10 CallerFrameChecks.receiver CallerFrameChecks.target
      7 [] false "Finite" 2 = (.ok (.success [],Source.L0 env),caller) := instance_exact G out caller

end Solidity.Yul.World.InstanceBoundary
