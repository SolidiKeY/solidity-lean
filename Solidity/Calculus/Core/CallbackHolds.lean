import Solidity.Calculus.Core.Logic
import Solidity.Semantics.Core.Callback

/-!
# Formulas read with callbacks, over the typed state

The callback reading `holdsC` on scoped formulas and typed states
(`docs/intrinsic.md`, W2 lane `tree`, carried into W3): `holds`
(`Calculus/Core/Logic.lean`), but a modality ranges over every run with
callbacks (`ExecP`, then `ExecF` for its frames,
`Semantics/Core/Callback.lean`), and none of them may break the invariant.
The invariant is a closed formula `I : Fml C []`, kept by the runs as its
typed reading (`Fml.stateInv`, `StateInv := ⟨fun σ => holds σ I⟩`).

Proved: with no payment in a formula the two readings agree
(`holdsC_iff_holds`, from `ExecP.forall_iff` and `ExecF.forall_iff`), and
`pre → [ P ] post` true with callbacks is true without, when only `P` pays
(`holds_of_holdsC_modal`, `holds_of_holdsC_imp`, `valid_of_validC`, from
`Prog.exec_run` and `Frames.exec_run`).  `ProvesC`'s soundness against
`ValidC` (`Calculus/Core/Callback.lean`) is `Calculus/Core/CallbackSound.lean`'s
`ProvesC.valid`.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- The invariant `I` read on typed states: what a callback run keeps. -/
def Fml.stateInv (I : Fml C []) : StateInv C := ⟨fun σ => holds σ I⟩

/-- `p` after a callback run of a program `o`, then of its frames `κ`: of the
state the frames end in, `m.onTHalt` of a halt that is not a panic, and
never of a broken invariant. -/
def COut.thenF (J : StateInv C) {H : HTy} {Γ₁ Γ₀ : Ctx} (κ : Frames C Γ₁ Γ₀) (m : Modality)
    (p : TState C Γ₀ → Prop) : COut C H Γ₁ → Prop
  | .ok o => ∀ o', ExecF J o.st κ o' → o'.after m p
  | .halt e => m.onTHalt e ∧ e ≠ .panic
  | .violated => False

/-- **Whether `φ` holds in the typed state `σ` when every payment may call
back into a contract with invariant `I`**: `holds`, but a modality ranges
over every run with callbacks, and none of them may break `I`. -/
def holdsC (I : Fml C []) : {Γ : Ctx} → TState C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => holds σ (.eq a b)
  | _, σ, .defined t => holds σ (.defined t)
  | _, σ, .not φ => ¬ holdsC I σ φ
  | _, σ, .and φ ψ => holdsC I σ φ ∧ holdsC I σ ψ
  | _, σ, .imp φ ψ => holdsC I σ φ → holdsC I σ ψ
  | _, σ, .upd m U φ =>
    m.afterC (fun τ => ∀ σ' : TState C _, σ'.erase = τ → σ.H <+: σ'.H → holdsC I σ' φ)
      (U.apply σ.erase)
  | _, σ, .modal m P κ φ =>
    ∀ o, ExecP I.stateInv σ P o → o.thenF I.stateInv κ m (holdsC I · φ)
  | _, σ, .havoc φ => ∀ st nt, holdsC I (σ.havoc st nt) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, holdsC I (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => holdsC I (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holdsC I (σ.anon xs b) φ

/-- A contract invariant: a closed formula with no payment in it (solkey's
`CInv(storage, net)`). -/
structure Invariant (C : Contract) where
  fml : Fml C []
  noTransfer : fml.hasTransfer = false := by rfl

/-- Valid with callbacks: true in every typed state. -/
def ValidC (I : Invariant C) (φ : Fml C []) : Prop := ∀ σ : TState C [], holdsC I.fml σ φ

/-- The two semantics of `transfer` (KeY's `transferSemantics` option). -/
inductive TransferSem (C : Contract) where
  | noCallback
  | withCallback (I : Invariant C)

/-- **The judgement, parameterised by the transfer semantics**: `holds`
without callbacks, `holdsC` with them. -/
def holdsT : TransferSem C → {Γ : Ctx} → TState C Γ → Fml C Γ → Prop
  | .noCallback => holds
  | .withCallback I => holdsC I.fml

/-- Valid under a transfer semantics. -/
def ValidT (ts : TransferSem C) (φ : Fml C []) : Prop := ∀ σ : TState C [], holdsT ts σ φ

theorem validT_noCallback {φ : Fml C []} : ValidT .noCallback φ ↔ Valid φ := Iff.rfl

theorem validT_withCallback {I : Invariant C} {φ : Fml C []} :
    ValidT (.withCallback I) φ ↔ ValidC I φ := Iff.rfl

/-! ## The deterministic run, through the frames -/

section Frames

variable {Γ Γ₁ Γ₀ : Ctx}

theorem Prog.trunFrames_ok {σ : TState C Γ} {P : Prog C Γ Γ₁} {o : Out C σ.H Γ₁}
    (κ : Frames C Γ₁ Γ₀) (h : Prog.trun σ P = .ok o) :
    Prog.trunFrames σ P κ = (do let o' ← Frames.trun o.st κ; pure o'.st) := by
  unfold Prog.trunFrames
  rw [h]
  rfl

theorem Prog.trunFrames_error {σ : TState C Γ} {P : Prog C Γ Γ₁} {e : THalt}
    (κ : Frames C Γ₁ Γ₀) (h : Prog.trun σ P = .error e) :
    Prog.trunFrames σ P κ = .error e := by
  unfold Prog.trunFrames
  rw [h]
  rfl

theorem afterRunTR_error {α : Type} (m : Modality) (p : α → Prop) (e : THalt) :
    m.afterRunTR p (.error e : TRes α) ↔ m.onTHalt e ∧ e ≠ .panic := by
  simp only [Modality.afterRunTR, ne_eq, Except.error.injEq]

theorem afterRunTR_ok {α : Type} (m : Modality) (p : α → Prop) (a : α) :
    m.afterRunTR p (.ok a : TRes α) ↔ p a := by
  simp only [Modality.afterRunTR, ne_eq, reduceCtorEq, not_false_eq_true, and_true]

/-- The frames' outcome after a deterministic run of the program: `p` of the
state the frames end in. -/
theorem after_ofRes_frames (m : Modality) (p : TState C Γ₀ → Prop) {H : HTy}
    (r : TRes (Out C H Γ₀)) :
    (COut.ofRes r).after m p ↔ m.afterRunTR p (do let o' ← r; pure o'.st) := by
  cases r with
  | error e => exact (afterRunTR_error m p e).symm
  | ok o => exact (afterRunTR_ok m p o.st).symm

/-- **With no payment, the program and its frames read with callbacks are the
typed run**: `thenF` of every callback run is `afterRunTR` of `trunFrames`. -/
theorem after_frames_iff {J : StateInv C} {σ : TState C Γ} {P : Prog C Γ Γ₁}
    {κ : Frames C Γ₁ Γ₀} (hP : Prog.hasTransfer P = false) (hκ : κ.hasTransfer = false)
    (m : Modality) (p : TState C Γ₀ → Prop) :
    (∀ o, ExecP J σ P o → o.thenF J κ m p) ↔ m.afterRunTR p (Prog.trunFrames σ P κ) := by
  rw [ExecP.forall_iff hP]
  cases h : Prog.trun σ P with
  | error e =>
    rw [Prog.trunFrames_error κ h, afterRunTR_error]
    exact Iff.rfl
  | ok o =>
    rw [Prog.trunFrames_ok κ h]
    exact (ExecF.forall_iff hκ _).trans (after_ofRes_frames m p _)

end Frames

/-! ## The two readings -/

/-- **With no payment, the two readings agree.** -/
theorem holdsC_iff_holds {I : Fml C []} : {Γ : Ctx} → (φ : Fml C Γ) → φ.hasTransfer = false →
    ∀ σ : TState C Γ, (holdsC I σ φ ↔ holds σ φ)
  | _, .tt, _, _ => Iff.rfl
  | _, .eq _ _, _, _ | _, .defined _, _, _ => Iff.rfl
  | _, .not φ, h, σ => not_congr (holdsC_iff_holds φ h σ)
  | _, .and φ ψ, h, σ => by
    rw [Fml.hasTransfer_and, Bool.or_eq_false_iff] at h
    exact and_congr (holdsC_iff_holds φ h.1 σ) (holdsC_iff_holds ψ h.2 σ)
  | _, .imp φ ψ, h, σ => by
    rw [Fml.hasTransfer_imp, Bool.or_eq_false_iff] at h
    exact imp_congr (holdsC_iff_holds φ h.1 σ) (holdsC_iff_holds ψ h.2 σ)
  | _, .upd m U φ, h, σ => by
    have e : (fun τ => ∀ σ' : TState C _, σ'.erase = τ → σ.H <+: σ'.H → holdsC I σ' φ) =
        (fun τ => ∀ σ' : TState C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ) :=
      funext fun _ => propext (forall_congr' fun σ' => imp_congr_right fun _ =>
        imp_congr_right fun _ => holdsC_iff_holds φ h σ')
    show m.afterC _ _ ↔ m.afterC _ _
    rw [e]
  | _, .modal m P κ φ, h, σ => by
    rw [Fml.hasTransfer_modal, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h
    have e : (fun τ => holdsC I τ φ) = (fun τ => holds τ φ) :=
      funext fun τ => propext (holdsC_iff_holds φ h.2 τ)
    show (∀ o, ExecP I.stateInv σ P o → o.thenF I.stateInv κ m (fun τ => holdsC I τ φ)) ↔
      m.afterRunTR (fun τ => holds τ φ) (Prog.trunFrames σ P κ)
    rw [e]
    exact after_frames_iff h.1.1 h.1.2 m _
  | _, .havoc φ, h, σ =>
    forall_congr' fun _ => forall_congr' fun _ => holdsC_iff_holds φ h _
  | _, .all _ _ φ, h, σ => forall_congr' fun _ => holdsC_iff_holds φ h _
  | _, .bind m _ t φ, h, σ => by
    have e : (fun v : t.TDenote C σ.H => holdsC I (σ.push v) φ) =
        (fun v : t.TDenote C σ.H => holds (σ.push v) φ) :=
      funext fun v => propext (holdsC_iff_holds φ h (σ.push v))
    show m.forallB _ ↔ m.forallB _
    rw [e]
  | _, .anon _ φ, h, σ => forall_congr' fun _ => holdsC_iff_holds φ h _

/-- **A modal formula true with callbacks is true without**, when its
postcondition has no program paying: the deterministic run, through the
program and then its frames, is among the callback runs
(`Prog.exec_run`, `Frames.exec_run`), and none of those breaks the
invariant. -/
theorem holds_of_holdsC_modal {I : Fml C []} {Γ Γ₁ Γ₀ : Ctx} {σ : TState C Γ} {m : Modality}
    {P : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀} (H : holdsC I σ (.modal m P κ φ))
    (hφ : φ.hasTransfer = false) : holds σ (.modal m P κ φ) := by
  change ∀ o, ExecP I.stateInv σ P o → o.thenF I.stateInv κ m (holdsC I · φ) at H
  show m.afterRunTR (holds · φ) (Prog.trunFrames σ P κ)
  rcases Prog.exec_run I.stateInv P σ with he | he
  · have H₁ := H _ he
    cases hr : Prog.trun σ P with
    | error e =>
      rw [hr] at H₁
      rw [Prog.trunFrames_error κ hr, afterRunTR_error]
      exact H₁
    | ok o =>
      rw [hr] at H₁
      rw [Prog.trunFrames_ok κ hr]
      rcases Frames.exec_run I.stateInv κ o.st with hf | hf
      · have H₂ := H₁ _ hf
        cases hk : Frames.trun o.st κ with
        | error e =>
          rw [hk] at H₂
          exact (afterRunTR_error m _ e).2 H₂
        | ok o' =>
          rw [hk] at H₂
          exact (afterRunTR_ok m _ o'.st).2 ((holdsC_iff_holds φ hφ o'.st).1 H₂)
      · exact (H₁ _ hf).elim
  · exact (H _ he).elim

/-- A precondition and a modal formula, true with callbacks, are true without
(`holds_of_holdsC_modal`), when neither the precondition nor the
postcondition has a program paying. -/
theorem holds_of_holdsC_imp {I : Fml C []} {Γ Γ₁ Γ₀ : Ctx} {σ : TState C Γ} {a : Fml C Γ}
    {m : Modality} {P : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (H : holdsC I σ (.imp a (.modal m P κ φ))) (ha : a.hasTransfer = false)
    (hφ : φ.hasTransfer = false) : holds σ (.imp a (.modal m P κ φ)) :=
  fun h => holds_of_holdsC_modal (H ((holdsC_iff_holds a ha σ).2 h)) hφ

/-- **Valid with callbacks is valid without**, for `pre → [ P ] post`. -/
theorem valid_of_validC {I : Invariant C} {Γ₁ Γ₀ : Ctx} {a : Fml C []} {m : Modality}
    {P : Prog C [] Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀} (H : ValidC I (.imp a (.modal m P κ φ)))
    (ha : a.hasTransfer = false) (hφ : φ.hasTransfer = false) :
    Valid (.imp a (.modal m P κ φ)) :=
  fun σ => holds_of_holdsC_imp (H σ) ha hφ

end Solidity.Core
