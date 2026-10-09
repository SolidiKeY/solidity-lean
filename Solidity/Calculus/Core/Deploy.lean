import Solidity.Calculus.Core.Spec
import Solidity.Calculus.Core.Close
import Solidity.Calculus.Core.SoundKit

/-!
# A scoped constructor obligation, read at the deployment

`Calculus/Problem.lean`'s `Problem.text` and `Problem.deploy_of_valid`
for the scoped obligation (`Problem.ctorFml`, `cproblem!{constructor}`,
`problem!{constructor}` under `open scoped Solidity.Core.Surface`):

* `Problem.text` prints the KeY problem file of its erasure, which is
  today's obligation (`Problem.ofLegacy` reads today's back);
* `Problem.deploy_of_valid_typed`: a valid obligation of no parameters is a
  theorem about the typed run of its program from the typed deployment
  state (`TState.deploy`), which the deployment update leaves as it is;
* `Problem.deploy_of_valid_nil`: the same, read at the typed deployment
  (`Contract.deployT`, `Contract.deploy`'s guard over the typed run): a
  constructor that is not `payable` is sent no value.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- solkey's problem file of a scoped obligation: its erasure's
(`Solidity.Problem.text`). -/
def Problem.text (contract fn : String) (φ : Fml C []) : String :=
  Surface.Problem.text contract fn (φ.eraseS [])

/-- The typed state a deployment starts in (`Contract.deployState`): the
empty storage, no memory, a ledger holding the deployer's payment, and the
value sent as the contract's funds. -/
def TState.deploy (C : Contract) (tx : TTx) : TState C [] :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := (),
    net := [(tx.msgSender.1, tx.msgValue.1)], selfBalance := tx.msgValue, tx := tx }

theorem TState.deploy_erase (C : Contract) (tx : TTx) :
    (TState.deploy C tx).erase = EState.ofSem (C.deployState tx.erase) := by
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

/-- **The typed deployment** (`Contract.deploy`, over the typed run): a
constructor that is not `payable`, the implicit one too, refuses value, as
solc's creation code does; otherwise its program runs from
`TState.deploy`. -/
def Contract.deployT (C : Contract) {Γ' : Ctx} (P : Prog C [] Γ') (tx : TTx) :
    TRes (TState C Γ') :=
  if !((C.ctor.map (·.payable)).getD false) && tx.msgValue.1 != 0 then .error .revert
  else Prog.trunFrames (TState.deploy C tx) P .nil

/-- Value sent to a constructor that is not `payable` reverts the
deployment. -/
theorem Contract.deployT_refuses (C : Contract) {Γ' : Ctx} (P : Prog C [] Γ') (tx : TTx)
    (hp : (C.ctor.map (·.payable)).getD false = false) (hv : tx.msgValue.1 ≠ 0) :
    Contract.deployT C P tx = .error .revert := by
  simp only [Contract.deployT, hp, Bool.not_false, Bool.true_and, bne_iff_ne.2 hv, if_true]

/-- **A derived constructor obligation of no parameters holds of the
deployment**: its program runs under `m` at `Contract.deployT`, and does not
panic; a constructor that is not `payable` is sent no value. -/
theorem Problem.deploy_of_valid_nil {m : Modality} {Γ' : Ctx} {P : Prog C [] Γ'}
    (h : Valid (Problem.ctorFml m [] P)) (tx : TTx)
    (hpay : (C.ctor.map (·.payable)).getD false = true ∨ tx.msgValue.1 = 0) :
    m.afterRunTR (fun _ => True) (Contract.deployT C P tx) := by
  have e : Contract.deployT C P tx = Prog.trunFrames (TState.deploy C tx) P .nil := by
    rcases hpay with hp | hv
    · simp only [Contract.deployT, hp, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        if_false]
    · simp only [Contract.deployT, hv, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
        if_false]
  rw [e]
  exact Problem.deploy_of_valid_typed h tx

end Solidity.Core
