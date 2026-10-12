import Solidity.Calculus.Spec
import Solidity.Calculus.Logic
import Solidity.Calculus.Closable
import Solidity.Semantics.StateErase
import Solidity.Calculus.NFmlClose
import Solidity.Calculus.SoundKit

/-!
# A scoped constructor obligation, read at the deployment

The constructor obligation (`Problem.ctorFml`, `problem!{constructor}`,
`Calculus/Problem.lean`), read at the deployment, as master's
`Problem.deploy_of_valid` read the unscoped one:

* `Problem.deploy_of_valid`: a valid obligation is a theorem about the typed
  run of its program from the typed deployment state (`State.deploy`) with
  any values of its parameters, which the deployment update leaves as it
  is; `Problem.deploy_of_valid_typed` is the case of no parameters;
* `Problem.deploy_of_valid_nil`: the same, read at the typed deployment
  (`Contract.deployT`, master's `Contract.deploy` guard over the typed
  run): a constructor that is not `payable` is sent no value.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-- The typed state a deployment starts in (`Contract.deployState`): the
empty storage, no memory, a ledger holding the deployer's payment, and the
value sent as the contract's funds. -/
def State.deploy (C : Contract) (tx : TTx) : State C [] :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := (),
    net := [(tx.msgSender.1, tx.msgValue.1)], selfBalance := tx.msgValue, tx := tx }

theorem State.deploy_erase (C : Contract) (tx : TTx) :
    (State.deploy C tx).erase = EState.ofSem (C.deployState tx.erase) := by
  simp only [State.erase, State.deploy, Storage.init_erase]
  rfl

/-- The deployment update leaves the deployment's state as it is. -/
theorem Problem.deployUpd_deploy (C : Contract) (tx : TTx) :
    (Problem.deployUpd C).apply (State.deploy C tx).erase = .ok (State.deploy C tx).erase := by
  rw [State.deploy_erase]
  rfl

/-- The same, with the constructor's parameters bound: the update reads
none of them. -/
theorem Problem.deployUpd_deployEnv (C : Contract) (tx : TTx) {Δ : Ctx}
    (e : TEnv C (State.deploy C tx).H Δ) :
    (Problem.deployUpd C).apply ((State.deploy C tx).withEnv e).erase =
      .ok ((State.deploy C tx).withEnv e).erase := by
  rw [State.withEnv_erase, State.deploy_erase]
  rfl

/-- A closed formula holds of a state with every value of the locals it
closes over (`Fml.closeN`; a hidden binder reads every value too). -/
theorem holds_closeN {σ : State C []} {useAll : Bool} :
    (Γ : NCtx) → {φ : Fml C Γ.ctx} → holds σ (Fml.closeN useAll Γ φ) →
      ∀ e : TEnv C σ.H Γ.ctx, holds (σ.withEnv e) φ
  | [], _, h, () => h
  | (x, .val p) :: Γ, φ, h, (v, e) => by
    cases useAll
    · exact holds_closeN (φ := .bind .box x (.val p) φ) Γ h e v
    · exact holds_closeN (φ := .all x p φ) Γ h e v
  | (x, .alias R) :: Γ, φ, h, (v, e) => holds_closeN (φ := .bind .box x (.alias R) φ) Γ h e v
  | (x, .mem R) :: Γ, φ, h, (v, e) => holds_closeN (φ := .bind .box x (.mem R) φ) Γ h e v
  | (x, .old) :: Γ, φ, h, (v, e) => holds_closeN (φ := .bind .box x .old φ) Γ h e v
  | (x, .oldNet) :: Γ, φ, h, (v, e) => holds_closeN (φ := .bind .box x .oldNet φ) Γ h e v

/-- **A derived constructor obligation holds of the typed deployment**:
for every value of its parameters, its program runs under `m` from
`State.deploy` with the parameters bound, and does not panic. -/
theorem Problem.deploy_of_valid {m : Modality} {xs : List (PrimTy × Var)} {Γ' : Ctx}
    {P : Prog C (paramsN xs).ctx Γ'} (h : Valid (Problem.ctorFml m xs P)) (tx : TTx)
    (e : TEnv C (State.deploy C tx).H (paramsN xs).ctx) :
    m.afterRunTR (fun _ => True) (Prog.runFrames ((State.deploy C tx).withEnv e) P .nil) := by
  have hσ := holds_closeN (paramsN xs) (h (State.deploy C tx)) e
  have hσ : m.afterC (fun τ => ∀ σ' : State C _, σ'.erase = τ →
      ((State.deploy C tx).withEnv e).H <+: σ'.H → holds σ' (.modal m P .nil .tt))
      ((Problem.deployUpd C).apply ((State.deploy C tx).withEnv e).erase) := hσ
  rw [Problem.deployUpd_deployEnv] at hσ
  exact hσ _ rfl (List.prefix_refl _)

/-- **A derived constructor obligation of no parameters holds of the typed
deployment**: its program runs under `m` from `State.deploy`, and does not
panic. -/
theorem Problem.deploy_of_valid_typed {m : Modality} {Γ' : Ctx} {P : Prog C [] Γ'}
    (h : Valid (Problem.ctorFml m [] P)) (tx : TTx) :
    m.afterRunTR (fun _ => True) (Prog.runFrames (State.deploy C tx) P .nil) := by
  have hσ : m.afterC (fun τ => ∀ σ' : State C [], σ'.erase = τ →
      (State.deploy C tx).H <+: σ'.H → holds σ' (.modal m P .nil .tt))
      ((Problem.deployUpd C).apply (State.deploy C tx).erase) := h (State.deploy C tx)
  rw [Problem.deployUpd_deploy] at hσ
  exact hσ _ rfl (List.prefix_refl _)

/-- **The typed deployment** (master's `Contract.deploy`, over the typed run): a
constructor that is not `payable`, the implicit one too, refuses value, as
solc's creation code does; otherwise its program runs from
`State.deploy`. -/
def Contract.deployT (C : Contract) {Γ' : Ctx} (P : Prog C [] Γ') (tx : TTx) :
    TRes (State C Γ') :=
  if !((C.ctor.map (·.payable)).getD false) && tx.msgValue.1 != 0 then .error .revert
  else Prog.runFrames (State.deploy C tx) P .nil

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
  have e : Contract.deployT C P tx = Prog.runFrames (State.deploy C tx) P .nil := by
    rcases hpay with hp | hv
    · simp only [Contract.deployT, hp, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        if_false]
    · simp only [Contract.deployT, hv, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
        if_false]
  rw [e]
  exact Problem.deploy_of_valid_typed h tx

end Solidity
