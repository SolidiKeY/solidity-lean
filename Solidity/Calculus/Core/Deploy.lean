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
  state (`TState.deploy`), which the deployment update leaves as it is.
  (Its reading on `Contract.deploy`, the erasure run by the untyped
  interpreter, went with the untyped run's bridge at W4 `sem-del`.)
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

end Solidity.Core
