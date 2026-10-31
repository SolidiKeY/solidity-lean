import Solidity.Backend.Executable.SourceInitializers
import Solidity.Source.SemanticsExamples

/-! Nonempty existing inheritance-initializer fixture, exact source state
cuts/failure and standalone typed base-argument controls. No source derivation,
new admission, lowering or byte execution is inferred from standalone metadata. -/
namespace Solidity.Backend.Executable.SourceInitializerChecks
open Solidity.Source SourceInitializers
open Solidity.Source.SemanticsExamples (EAB GAB dA dB litAB uint thisC user word)

def frame : Fr := {this := thisC, sender := user, value := word 0, static := false, contract := "B"}
def input : Locals EAB.layout [] × St EAB := (.nil, St.init EAB)
def first := (GAB .legacy).prog.inits "A"
def rest := (GAB .legacy).prog.inits "B"
def headRun := (runInits (GAB .legacy) frame 20 first).run input
def forward := (runInits (GAB .legacy) frame 20 (first ++ rest)).run input
def reverse := (runInits (GAB .legacy) frame 20 (rest ++ first)).run input

private theorem exact_status {α σ : Type} (r : Except Halt α × σ) (status : Except Halt α)
    (observed : r.1 = status) : r = (status,r.2) := by cases r; cases observed; rfl

private def errorOf {α : Type} : Except Halt α → Option Halt
  | .ok _ => none | .error halt => some halt
private theorem recover_error {α : Type} (r : Except Halt α) (halt : Halt)
    (observed : errorOf r = some halt) : r = .error halt := by
  cases r with | ok value => cases observed | error e => cases Option.some.inj observed; rfl

private theorem recover_unit (r : Except Halt Unit) (present : r.isOk = true) : r = .ok () := by
  cases r with | error e => cases present | ok value => cases value; rfl

theorem first_success : headRun = (.ok (),headRun.2) := exact_status _ _ (recover_unit _ (by decide +kernel))
theorem actual_initializer_cut : forward = (runInits (GAB .legacy) frame 20 rest).run headRun.2 :=
  inits_success (GAB .legacy) frame 20 first rest input headRun.2 first_success

private def values (state : St EAB) : Option Int × Option Int :=
  ((match (state.ex.world.accounts thisC).storage.read dA.path with | some (.int n _) => some n | _ => none),
   (match (state.ex.world.accounts thisC).storage.read dB.path with | some (.int n _) => some n | _ => none))
example : first.length = 1 ∧ rest.length = 1 := ⟨rfl,rfl⟩
theorem forward_values : values forward.2.2 = (some 1,some 1) := by decide +kernel
theorem reverse_values : values reverse.2.2 = (some 1,some 0) := by decide +kernel
example : values forward.2.2 ≠ values reverse.2.2 := by rw [forward_values, reverse_values]; decide

def deployment (pipeline : Solidity.Roadmap.Pipeline) :=
  runAt (fun n => deploy (GAB pipeline) n "B" thisC user (word 0) []) (St.init EAB) 20
private def successBytes : Except Halt Solidity.Roadmap.Outcome → Option Solidity.Roadmap.Bytes
  | .ok (.success bytes) => some bytes | _ => none
private theorem recover_deployment (r : Except Halt Solidity.Roadmap.Outcome)
    (observed : successBytes r = some []) : r = .ok (.success []) := by
  cases r with
  | error e => cases observed
  | ok result =>
    cases result with
    | revert bytes => cases observed
    | success bytes => cases Option.some.inj observed; rfl

theorem actual_deployment_success :
    (deployment .legacy).1 = .ok (.success []) ∧ (deployment .viaIR).1 = .ok (.success []) :=
  ⟨recover_deployment _ (by decide +kernel), recover_deployment _ (by decide +kernel)⟩
example : ((deployment .legacy).2.ex.world.accounts thisC).code = some 1 ∧
    ((deployment .viaIR).2.ex.world.accounts thisC).nonce = 1 := by decide +kernel

/-- Existing storage observations, with successful deployment tags proved above,
show constructor-body order also matters
between the admitted legacy/viaIR pipelines; no order is changed here. -/
example : SemanticsExamples.deployB .legacy ≠ SemanticsExamples.deployB .viaIR := by
  rw [SemanticsExamples.ctor_order_legacy, SemanticsExamples.ctor_order_viaIR]
  decide

def staticFrame : Fr := {frame with static := true}
def failedHead := (runInits (GAB .legacy) staticFrame 20 first).run input
theorem static_failure : failedHead = (.error (.revert []),failedHead.2) := exact_status _ _ (recover_error _ _ (by decide +kernel))
theorem static_stops_tail :
    (runInits (GAB .legacy) staticFrame 20 (first ++ rest)).run input = failedHead :=
  (inits_failure (GAB .legacy) staticFrame 20 first rest input failedHead.2 (.revert []) static_failure).trans static_failure.symm
example : values failedHead.2.2 = (some 0,some 0) := by decide +kernel

/-- Standalone typed component metadata: a no-parameter base is recorded once.
This is not asserted to be the prog.baseArgs list or Program.Derived evidence. -/
def baseArg : RBaseArg EAB [] := ⟨"A",[],.nil⟩
def argRun := (giveArgs (GAB .legacy) frame 20 "B" .nil [baseArg] []).run input
def twiceRun := (giveArgs (GAB .legacy) frame 20 "B" .nil [baseArg,baseArg] []).run input
theorem argument_success : argRun = (.ok [⟨"A",.nil⟩],input) := by rfl
example : twiceRun = argRun := by rfl
example : giveArgs (GAB .legacy) frame 20 "B" .nil [baseArg,baseArg] [] =
    (giveArgs (GAB .legacy) frame 20 "B" .nil [baseArg] [] >>= fun middle =>
      giveArgs (GAB .legacy) frame 20 "B" .nil [baseArg] middle) :=
  arguments_append (GAB .legacy) frame 20 "B" .nil [baseArg] [baseArg] []

example : collectArgs (GAB .legacy) frame 20 ["B","A"] [⟨"B",.nil⟩] =
    (collectArgs (GAB .legacy) frame 20 ["B"] [⟨"B",.nil⟩] >>= fun middle =>
      collectArgs (GAB .legacy) frame 20 ["A"] middle) :=
  collect_append (GAB .legacy) frame 20 ["B"] ["A"] [⟨"B",.nil⟩]

/-- Argument evaluation failure precedes the later parameter-shape refusal in
this deliberately bad-arity standalone negative metadata. No source admission
or constructor lowering is claimed for this negative. -/
def badArg : RBaseArg EAB [] := ⟨"A",[uint],.cons (.binary .div (litAB 1) (litAB 0)) (by decide) .nil⟩
def failedArgs := (giveArgs (GAB .legacy) frame 20 "B" .nil [badArg] []).run input
theorem argument_failure : failedArgs = (.error (.revert (panicData .divZero)),failedArgs.2) :=
  exact_status _ _ (recover_error _ _ (by decide +kernel))
theorem argument_stops_tail :
    (giveArgs (GAB .legacy) frame 20 "B" .nil [badArg,baseArg] []).run input = failedArgs :=
  (arguments_failure (GAB .legacy) frame 20 "B" .nil [badArg] [baseArg] [] input failedArgs.2
    (.revert (panicData .divZero)) argument_failure).trans argument_failure.symm

/-- info: 'Solidity.Backend.Executable.SourceInitializerChecks.actual_initializer_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_initializer_cut
/-- info: 'Solidity.Backend.Executable.SourceInitializerChecks.actual_deployment_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_deployment_success
/-- info: 'Solidity.Backend.Executable.SourceInitializerChecks.static_stops_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms static_stops_tail
/-- info: 'Solidity.Backend.Executable.SourceInitializerChecks.argument_stops_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_stops_tail
end Solidity.Backend.Executable.SourceInitializerChecks
