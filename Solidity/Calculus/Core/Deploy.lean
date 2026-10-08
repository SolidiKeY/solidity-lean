import Solidity.Calculus.Core.Spec
import Solidity.Calculus.Core.Close

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

/-- What a modality says of a run, weakened to its outcome. -/
theorem _root_.Solidity.Modality.afterRunC_true {α : Type} {m : Modality} {p : α → Prop}
    {r : Semantics.Res α} (h : m.afterRunC p r) : m.afterRunC (fun _ => True) r := by
  cases r with
  | ok _ => exact ⟨by cases m <;> trivial, h.2⟩
  | error e => exact h

/-- **A derived constructor obligation of no parameters holds of the
deployment** (`Solidity.Problem.deploy_of_valid_nil`): the erasure of its
program runs under `m` from `Contract.deploy`'s start, and does not panic;
a constructor that is not `payable` is sent no value. -/
theorem Problem.deploy_of_valid_nil {m : Modality} {Γ' : Ctx} {P : Prog C [] Γ'}
    (h : Valid (Problem.ctorFml m [] P)) (hP : P.Fresh [] []) (tx : Semantics.TxEnv)
    (hpay : (C.ctor.map (·.payable)).getD false = true ∨ tx.msgValue = 0) :
    m.afterRun (fun _ => True) (C.deploy (P.erase []) tx) := by
  have hrun : C.deploy (P.erase []) tx = Solidity.Prog.run (C.deployState tx) (P.erase []) := by
    rcases hpay with hp | hv
    · simp only [Contract.deploy, hp, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    · simp only [Contract.deploy, hv, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
        if_false]
  rw [hrun]
  let σ : State C [] := State.ofSem (C.deployState tx)
  have hT : σ.BoolOK := trivial
  have hσ : holds σ (.upd m (Problem.deployUpd C) (.modal m P .nil .tt)) := h σ
  -- the deployment update leaves the deployment's state as it is (by `rfl`)
  have hm : holds σ (.modal m P .nil .tt) := by
    simp only [holds] at hσ
    cases m with
    | box => exact hσ
    | diamond => exact (hσ hT).2
  have hr : m.afterRunC (fun _ => True) (Prog.run σ P) := by
    have h' := (Modality.afterRunT_iff.1 hm) fun _ => hT
    simp only [Frames.run, bind_pure] at h'
    exact Modality.afterRunC_true h'
  have hrel := Prog.run_rel (Agree.nil σ) P hP
  exact (Modality.afterRunC_rel m hrel fun _ _ _ => Iff.rfl).1 hr

end Solidity.Core
