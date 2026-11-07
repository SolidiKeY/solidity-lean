import Solidity.Examples.Roadmap.V16.CallbackConsumers

/-! Inhabited consumers and negatives over existing typed callback executions. -/
namespace Solidity.Roadmap.V16.CallbackControls

def contract : Contract := default
def start : State contract [] := State.init contract
def nilOut : Out contract start.H [] := ⟨start, List.prefix_refl _⟩

theorem nil_callback_box :
    holdsC (.tt : Fml contract []) true start (.modal .box .nil .nil .tt) :=
  (holdsC_iff_holds _ rfl start).2 (by
    change Modality.box.afterRunTR (fun _ : State contract [] => True) (.ok start)
    exact (afterRunTR_ok .box _ start).2 trivial)

theorem nil_callback_post : holdsC (.tt : Fml contract []) true nilOut.st .tt :=
  callback_post nil_callback_box ExecP.nil ExecF.nil

/-- A false postcondition is rejected by NEW callback transport at an actual run. -/
theorem wrong_callback_post :
    ¬ holdsC (.tt : Fml contract []) true start (.modal .box .nil .nil (.not .tt)) := by
  intro h
  exact (callback_post h ExecP.nil ExecF.nil) trivial

def payment : Prog contract [] [] :=
  .cons (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 0 rfl))) .nil

/-- An actual zero-value transfer exits with a deliberately false invariant.
This is a negative input, not a new admissibility profile or a repaired rule. -/
theorem broken_callback_execution :
    ExecP ((Fml.not (.tt : Fml contract [])).stateInv true) start payment .violated :=
  ExecP.violated (ExecS.transferViolated rfl rfl (fun h => h trivial))

theorem broken_callback_box :
    ¬ holdsC (Fml.not (.tt : Fml contract [])) true start (.modal .box payment .nil .tt) :=
  fun h => callback_no_violation h broken_callback_execution

/-- An actual allowed callback resumption changes the self balance. This is
an intrinsic callback run, not a bytecode or external-world correspondence. -/
def resumed : State contract [] :=
  (start.pay ⟨9, rfl⟩ 0).havoc (Storage.init contract) [] ⟨1, rfl⟩

def resumedOut : Out contract start.H [] := ⟨resumed, List.prefix_refl _⟩

theorem callback_resumes :
    ExecP ((.tt : Fml contract []).stateInv true) start payment (.ok resumedOut) :=
  ExecP.cons (ExecS.transferResume (J := (.tt : Fml contract []).stateInv true)
    (σ := start) (r := .simple (.lit 9 rfl)) (a := .simple (.lit 0 rfl))
    (st := Storage.init contract) (nt := [])
    (sb := ⟨1, rfl⟩) rfl rfl trivial trivial) ExecP.nil

theorem resumption_changes_balance : resumed.selfBalance.1 = 1 ∧ start.selfBalance.1 = 0 :=
  ⟨rfl, rfl⟩

/-- NEW transport at the actual resumed run. The callback modality is still
an explicit premise, not a constructed runtime specification. -/
theorem resumed_post_if_modal {φ : Fml contract []}
    (modal : holdsC (.tt : Fml contract []) true start (.modal .box payment .nil φ)) :
    holdsC (.tt : Fml contract []) true resumed φ :=
  callback_post modal callback_resumes ExecF.nil

end Solidity.Roadmap.V16.CallbackControls
