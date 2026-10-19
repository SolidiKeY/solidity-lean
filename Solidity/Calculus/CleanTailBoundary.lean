import Solidity.Typing.CleanTail
import Solidity.Semantics.Callback
import Solidity.Calculus.Logic

namespace Solidity

def StateInv.cleanTail (C : Contract) : StateInv C := { holds := fun σ => σ.storage.CleanTail }

theorem StateInv.cleanTail_at {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (StateInv.cleanTail C).at σ ↔ σ.storage.CleanTail := Iff.rfl

def Prog.CleanTailBoundaryAt {C : Contract} {Γ Γ' : Ctx} (P : Prog C Γ Γ')
    (σ : State C Γ) : Prop :=
  σ.storage.CleanTail →
    Modality.box.afterRunTR (fun o => o.st.storage.CleanTail) (Prog.run σ P)

def Prog.CleanTailBoundary {C : Contract} {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prop :=
  ∀ σ : State C Γ, P.CleanTailBoundaryAt σ

def Prog.CleanTailCallbackBoundary {C : Contract} {Γ Γ' : Ctx}
    (P : Prog C Γ Γ') : Prop :=
  ∀ σ : State C Γ, σ.storage.CleanTail →
    ∀ o, ExecP (StateInv.cleanTail C) σ P o →
      o.after .box (fun σ' => σ'.storage.CleanTail)

theorem State.init_cleanTail (C : Contract) : (State.init C).storage.CleanTail :=
  Storage.init_cleanTail C

theorem Prog.cleanTailBoundaryAt_of_runStorage {C : Contract} {Γ Γ' : Ctx}
    {P : Prog C Γ Γ'} {σ : State C Γ} {st : Storage C}
    (hrun : (Prog.run σ P).toOption.map (fun o => o.st.storage) = some st)
    (hclean : st.CleanTail) : P.CleanTailBoundaryAt σ := by
  intro _
  cases hr : Prog.run σ P with
  | error e => rw [hr] at hrun; cases hrun
  | ok o =>
    rw [hr] at hrun
    have hstorage : o.st.storage = st := Option.some.inj hrun
    have hs : o.st.storage.CleanTail := hstorage.symm ▸ hclean
    exact ⟨hs, nofun⟩

theorem Prog.cleanTailBoundary_exit {C : Contract} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hP : P.CleanTailBoundary) {σ : State C Γ} (hσ : σ.storage.CleanTail)
    {o : Out C σ.H Γ'} (ho : Prog.run σ P = .ok o) : o.st.storage.CleanTail := by
  have h := hP σ hσ
  rw [ho] at h
  exact h.1

theorem Prog.cleanTailCallbackBoundary_exit {C : Contract} {Γ Γ' : Ctx}
    {P : Prog C Γ Γ'} (hP : P.CleanTailCallbackBoundary) {σ : State C Γ}
    (hσ : σ.storage.CleanTail) {o : Out C σ.H Γ'}
    (ho : ExecP (StateInv.cleanTail C) σ P (.ok o)) : o.st.storage.CleanTail :=
  hP σ hσ (.ok o) ho

theorem Prog.cleanTailCallbackBoundary_noViolation {C : Contract} {Γ Γ' : Ctx}
    {P : Prog C Γ Γ'} (hP : P.CleanTailCallbackBoundary) {σ : State C Γ}
    (hσ : σ.storage.CleanTail) : ¬ ExecP (StateInv.cleanTail C) σ P .violated :=
  fun ho => hP σ hσ .violated ho

end Solidity
