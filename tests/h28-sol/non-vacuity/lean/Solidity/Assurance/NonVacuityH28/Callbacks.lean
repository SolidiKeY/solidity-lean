import Solidity.Theorems

/-! An inhabited callback-sensitive payment whose entry invariant holds. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

variable (C : Contract)

def funded : State C [] := { State.init C with selfBalance := ⟨10, rfl⟩ }
def paymentInvariant : StateInv C :=
  ⟨fun σ => (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) σ.net).getD 0 = 0, true⟩

theorem callback_violation :
    (paymentInvariant C).at (funded C) ∧
      ExecS (paymentInvariant C) (funded C)
        (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))) .violated := by
  refine ⟨rfl, ExecS.transferViolated
    (o₁ := ⟨(funded C).pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩) rfl rfl ?_⟩
  change ¬ (-5 : Int) = 0
  decide +kernel

def openPolicy (pay : Bool) : StateInv C := ⟨fun _ => True, pay⟩
def paid : State C [] := (funded C).pay ⟨9, rfl⟩ 5
def resumed : State C [] :=
  (paid C).havoc (Storage.init C) [(⟨9, rfl⟩, -7)] ⟨0, rfl⟩

theorem callback_resume :
    ExecS (openPolicy C true) (funded C)
      (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)))
      (.ok ⟨resumed C, List.prefix_refl _⟩) :=
  ExecS.transferResume (J := openPolicy C true) (σ := funded C)
    (r := .simple (.lit 9 rfl)) (a := .simple (.lit 5 rfl)) (st := Storage.init C)
    (nt := [(⟨9, rfl⟩, -7)]) (sb := ⟨0, rfl⟩) (o₁ := ⟨paid C, List.prefix_refl _⟩) rfl rfl True.intro True.intro

theorem noCallback_transfer :
    ExecS (openPolicy C false) (funded C)
      (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)))
      (.ok ⟨paid C, List.prefix_refl _⟩) := .det rfl

theorem callback_revert :
    ExecS (openPolicy C true) (State.init C)
      (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))) (.halt .revert) :=
  .transferHalt rfl rfl

/-- A resumed callback's ledger cannot be erased to the deterministic ledger. -/
theorem callback_observations :
    lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) (paid C).net = some (-5) ∧
      lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) (resumed C).net = some (-7) := ⟨rfl, rfl⟩

theorem callback_observation_erasure_rejected : (resumed C).net ≠ (paid C).net := by
  intro h
  have heq : (some (-7 : Int)) = some (-5) :=
    congrArg (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote)) h
  cases heq

theorem noCallback_unique {o : COut C [] []}
    (h : ExecS (openPolicy C false) (funded C)
      (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))) o) :
    o = .ok ⟨paid C, List.prefix_refl _⟩ :=
  Stmt.eq_run (openPolicy C false) _ rfl h

theorem noCallback_excludes_resume :
    ¬ ExecS (openPolicy C false) (funded C)
      (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)))
      (.ok ⟨resumed C, List.prefix_refl _⟩) := by
  intro h
  have heq : (COut.ok ⟨resumed C, List.prefix_refl _⟩ : COut C [] []) =
      .ok ⟨paid C, List.prefix_refl _⟩ := noCallback_unique C h
  have hnet : (resumed C).net = (paid C).net :=
    congrArg (fun outcome : COut C [] [] => match outcome with
      | .ok o => o.st.net | _ => []) heq
  exact callback_observation_erasure_rejected C hnet

def paymentSpec : Spec C [] :=
  .box (.cons (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))) .nil) .tt

theorem payment_derivation :
    ProvesC (Invariant.top (C := C)).fml true [] .nil (paymentSpec C).toFml := by
  apply ProvesC.callback .transferWithCallbackBox
  · exact .plain (.updIntro (.updIntro (.closeTrue rfl))) rfl
  · exact .plain (.closeTrue rfl) rfl

theorem payment_headline : Spec.ValidC (Invariant.top (C := C)) (paymentSpec C) true :=
  Main.callback_soundness (payment_derivation C)

theorem top_callback_policy (pay : Bool) :
    (Invariant.top (C := C)).fml.stateInv pay = openPolicy C pay := rfl

def callbackProgram : Prog C [] [] :=
  .cons (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))) .nil

theorem callback_program_resume :
    ExecP (openPolicy C true) (funded C) (callbackProgram C)
      (.ok ⟨resumed C, List.prefix_refl _⟩) := .cons (callback_resume C) .nil

theorem callback_program_noCallback :
    ExecP (openPolicy C false) (funded C) (callbackProgram C)
      (.ok ⟨paid C, List.prefix_refl _⟩) := .cons (noCallback_transfer C) .nil

theorem callback_program_revert :
    ExecP (openPolicy C true) (State.init C) (callbackProgram C) (.halt .revert) :=
  .halt (callback_revert C)

theorem callback_program_violation :
    (paymentInvariant C).at (funded C) ∧
      ExecP (paymentInvariant C) (funded C) (callbackProgram C) .violated :=
  ⟨(callback_violation C).1, .violated (callback_violation C).2⟩

theorem noCallback_payment_derivation :
    ProvesC (Invariant.top (C := C)).fml false [] .nil (paymentSpec C).toFml := by
  apply ProvesC.callback .transferWithCallbackBox
  · exact .plain (.updIntro (.updIntro (.closeTrue rfl))) rfl
  · exact .plain (.closeTrue rfl) rfl

theorem noCallback_payment_headline : Spec.ValidC (Invariant.top (C := C)) (paymentSpec C) false :=
  Main.noCallback_soundness (noCallback_payment_derivation C)

end Solidity.Assurance.NonVacuityH28
