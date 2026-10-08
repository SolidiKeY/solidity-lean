import Solidity.Calculus.Core.Spec
import Solidity.Calculus.Core.Close
import Solidity.Calculus.Core.SoundKit

/-!
# A scoped constructor obligation, read at the deployment

`Calculus/Problem.lean`'s `Problem.text` and `Problem.deploy_of_valid_nil`
for the scoped obligation (`Problem.ctorFml`, `cproblem!{constructor}`,
`problem!{constructor}` under `open scoped Solidity.Core.Surface`):

* `Problem.text` prints the KeY problem file of its erasure, which is
  today's obligation (`Problem.ofLegacy` reads today's back);
* `Problem.deploy_of_valid_nil`: a valid obligation of no parameters is a
  theorem about `Contract.deploy`, run on the erasure of its program.  The
  scoped run from the deployment's state and the run of the erasure agree
  (`Prog.run_rel`, a fresh program), and the deployment update leaves that
  state as it is.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- solkey's problem file of a scoped obligation: its erasure's
(`Solidity.Problem.text`). -/
def Problem.text (contract fn : String) (φ : Fml C []) : String :=
  Solidity.Problem.text contract fn (φ.erase [])

/-- The typed state a deployment starts in (`Contract.deployState`): the
empty storage, no memory, a ledger holding the deployer's payment, and the
value sent as the contract's funds. -/
def TState.deploy (C : Contract) (tx : TTx) : TState C [] :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := (),
    net := [(tx.msgSender.1, tx.msgValue.1)], selfBalance := tx.msgValue, tx := tx }

theorem TState.deploy_erase (C : Contract) (tx : TTx) :
    (TState.deploy C tx).erase = State.ofSem (C.deployState tx.erase) := by
  simp only [TState.erase, TState.deploy, Storage.init_erase]
  rfl

/-- The deployment update leaves the deployment's state as it is. -/
theorem Problem.deployUpd_deploy (C : Contract) (tx : TTx) :
    (Problem.deployUpd C).apply (TState.deploy C tx).erase = .ok (TState.deploy C tx).erase := by
  rw [TState.deploy_erase]
  rfl

/-- **A derived constructor obligation of no parameters holds of the typed
deployment**: its program runs under `m` from `TState.deploy`, and does not
panic. -/
theorem Problem.deploy_of_valid_typed {m : Modality} {Γ' : Ctx} {P : Prog C [] Γ'}
    (h : Valid (Problem.ctorFml m [] P)) (tx : TTx) :
    m.afterRunTR (fun _ => True) (Prog.trunFrames (TState.deploy C tx) P .nil) := by
  have hσ : m.afterC (fun τ => ∀ σ' : TState C [], σ'.erase = τ →
      (TState.deploy C tx).H <+: σ'.H → holds σ' (.modal m P .nil .tt))
      ((Problem.deployUpd C).apply (TState.deploy C tx).erase) := h (TState.deploy C tx)
  rw [Problem.deployUpd_deploy] at hσ
  exact hσ _ rfl (List.prefix_refl _)

/-- **A derived constructor obligation of no parameters holds of the
deployment** (`Solidity.Problem.deploy_of_valid_nil`): the erasure of its
program runs under `m` from `Contract.deploy`'s start, and does not panic;
a constructor that is not `payable` is sent no value.  The typed run must
end (`hX`, `TRes.Ends`): it diverges on a loop with no last iteration and is
exhausted on a push at the bound (decision 15), which both modalities
accept, and against either the untyped run may do anything.  A straight
program ends (`Prog.trun_ends`). -/
theorem Problem.deploy_of_valid_nil {m : Modality} {Γ' : Ctx} {P : Prog C [] Γ'}
    (h : Valid (Problem.ctorFml m [] P)) (hP : P.Fresh [] []) (tx : TTx)
    (hpay : (C.ctor.map (·.payable)).getD false = true ∨ tx.msgValue.1 = 0)
    (hX : (Prog.trunFrames (TState.deploy C tx) P .nil).Ends) :
    m.afterRun (fun _ => True) (C.deploy (P.erase []) tx.erase) := by
  have hrun : C.deploy (P.erase []) tx.erase =
      Solidity.Prog.run (C.deployState tx.erase) (P.erase []) := by
    rcases hpay with hp | hv
    · simp only [Contract.deploy, hp, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    · have hv' : tx.erase.msgValue = 0 := hv
      simp only [Contract.deploy, hv', bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
        if_false]
  rw [hrun]
  let σ := TState.deploy C tx
  have hT := Problem.deploy_of_valid_typed h tx
  have hA := Prog.trunFrames_erase σ P .nil
  have hR := Prog.run_rel (Agree.nil σ.erase) P hP
  rw [TState.deploy_erase] at hR hA
  have e0 : withLocals (State.ofSem (C := C) (C.deployState tx.erase)).glob [] =
      C.deployState tx.erase := rfl
  rw [e0] at hR
  simp only [Frames.run, bind_pure] at hA
  cases hr : Prog.trunFrames σ P .nil with
  | ok a =>
    rw [hr] at hA
    rw [show Prog.run (State.ofSem (C.deployState tx.erase)) P = .ok a.erase from hA] at hR
    revert hR
    cases Solidity.Prog.run (C.deployState tx.erase) (P.erase []) with
    | ok _ => intro _; exact ⟨by cases m <;> trivial, nofun⟩
    | error => exact False.elim
  | error e =>
    rw [hr] at hA hT hX
    cases e with
    | revert =>
      rw [show Prog.run (State.ofSem (C.deployState tx.erase)) P = .error .revert from hA] at hR
      revert hR
      cases Solidity.Prog.run (C.deployState tx.erase) (P.erase []) with
      | ok _ => exact False.elim
      | error e' =>
        intro hR
        cases (hR : Semantics.Halt.revert = e')
        cases m with
        | box => exact ⟨trivial, nofun⟩
        | diamond => exact absurd hT.1 nofun
    | panic => exact absurd rfl hT.2
    | diverge => exact absurd rfl hX.1
    | exhausted => exact absurd rfl hX.2

end Solidity.Core
