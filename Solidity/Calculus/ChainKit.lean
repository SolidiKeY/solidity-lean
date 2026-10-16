import Solidity.Calculus.NotationResolve
import Solidity.Calculus.Taclet
import Solidity.Calculus.Sound
import Solidity.Calculus.Merge
import Solidity.Calculus.RewriteScoped
import Solidity.Calculus.RewriteLaws
import Solidity.Calculus.RewriteChains

/-!
# Chains on scoped formulas: the relations

The chains' relations on the scoped formulas of
`Calculus/Fml.lean` (W2 of `docs/intrinsic.md`): a step `φ ~> ψ`
(`Fml.OneStep`, `Fml.step`), a named step `φ ~[r]~> ψ` (`Fml.StepBy`),
several `φ ~*> ψ` (`Fml.Steps`), and a chain of them (`Fml.Via`), a
link a merge (`Link.merge`, `Calculus/Merge.lean`) or a rewrite of the
scoped line (`Link.rw`, `Calculus/RewriteScoped.lean`) too.
`Calculus/Chains.lean` elaborates and proves them.

**Naming a rule.**  The strategy is a function (`Stmt.step`) and the
rule table a relation over it, so a step does not carry its rule; the label
of `φ ~[r]~> ψ` is a derivation `d : Rule C k m s p` of the constructor `r`
on the statement `s` the step fires on (`StepRule.taclet`), or the empty
modality going through its frames (`StepRule.emptyModality`).  What ties
the label to the line is the statement it fires on: `Fml.stepFocusR`, the
strategy's step with the statement it chose beside the line it leaves
(`Focus`), whose line is `Fml.stepR`'s (`Fml.stepFocusR_snd`).

**A step over a postcondition** `φ : Post C Γ`: `Fml.stepFocusR` and
`Fml.maxIdx` are kernel recursions that cannot look into `φ`.  The lemmas
below take a line apart along its connectives instead, each a `rfl` of the
recursor: what the strategy does at a connective (`stepFocusR_upd` …), that a
formula with no modality takes no step (`stepFocusR_eq_none`), and the fresh
index of a line from its parts (`maxIdx_upd` …, `Post.noFresh`).
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-! ## The statement a step fires on -/

/-- What a step fires on: a statement, at the fresh index `k` and under the
modality `m`, or a finished program, which goes through its frames. -/
inductive Focus (C : Contract) : Type where
  | stmt (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ')
  | empty

/-- The modality `⟨ P κ ⟩ φ` one step on, with the statement it fires on
(`Fml.modalStep`). -/
def Fml.modalFocus (k : Nat) (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) : Option (Focus C × Fml C Γ) :=
  Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames C Γ₁ Γ₀ → Option (Focus C × Fml C Γ)) P
    (fun κ => some (.empty, κ.exit m φ))
    (fun s ω κ => some (.stmt k m s, (s.step k m).fml m ω κ φ)) κ

/-- `Fml.stepR` with the statement it fires on: the recursor, which the
kernel unfolds (Gate G0, condition 2).  Never run as compiled code. -/
noncomputable def Fml.stepFocusR (k : Nat) {Γ : Ctx} (φ : Fml C Γ) :
    Option (Focus C × Fml C Γ) :=
  Fml.rec (motive := fun Γ _ => Option (Focus C × Fml C Γ))
    (tt := none) (eq := fun _ _ => none) (defined := fun _ => none) (not := fun _ _ => none)
    (and := fun φ ψ ihφ ihψ => match ihφ with
      | some (f, φ') => some (f, .and φ' ψ)
      | none => ihψ.map fun (f, ψ') => (f, .and φ ψ'))
    (imp := fun a _ _ ih => ih.map fun (f, φ') => (f, .imp a φ'))
    (upd := fun m U _ ih => ih.map fun (f, φ') => (f, .upd m U φ'))
    (modal := fun m P κ φ _ => Fml.modalFocus k m P κ φ)
    (havoc := fun _ ih => ih.map fun (f, φ') => (f, .havoc φ'))
    (all := fun x p _ ih => ih.map fun (f, φ') => (f, .all x p φ'))
    (bind := fun m x t _ ih => ih.map fun (f, φ') => (f, .bind m x t φ'))
    (anon := fun xs _ ih => ih.map fun (f, φ') => (f, .anon xs φ')) φ

section Equations

variable {k : Nat} {Γ : Ctx}

theorem Fml.stepFocusR_and_left {φ ψ φ' : Fml C Γ} {f : Focus C}
    (h : φ.stepFocusR k = some (f, φ')) : (Fml.and φ ψ).stepFocusR k = some (f, .and φ' ψ) := by
  show (match φ.stepFocusR k with
    | some (f, φ') => some (f, Fml.and φ' ψ)
    | none => (ψ.stepFocusR k).map fun (f, ψ') => (f, Fml.and φ ψ')) = _
  rw [h]

theorem Fml.stepFocusR_and_right {φ ψ ψ' : Fml C Γ} {f : Focus C} (h : φ.stepFocusR k = none)
    (h' : ψ.stepFocusR k = some (f, ψ')) : (Fml.and φ ψ).stepFocusR k = some (f, .and φ ψ') := by
  show (match φ.stepFocusR k with
    | some (f, φ') => some (f, Fml.and φ' ψ)
    | none => (ψ.stepFocusR k).map fun (f, ψ') => (f, Fml.and φ ψ')) = _
  rw [h, h']
  rfl

theorem Fml.stepFocusR_imp {a φ φ' : Fml C Γ} {f : Focus C} (h : φ.stepFocusR k = some (f, φ')) :
    (Fml.imp a φ).stepFocusR k = some (f, .imp a φ') := by
  show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.imp a φ')) = _
  rw [h]
  rfl

theorem Fml.stepFocusR_upd {Γ' : Ctx} {m : Modality} {U : Upd C Γ Γ'} {φ φ' : Fml C Γ'}
    {f : Focus C} (h : φ.stepFocusR k = some (f, φ')) :
    (Fml.upd m U φ).stepFocusR k = some (f, .upd m U φ') := by
  show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.upd m U φ')) = _
  rw [h]
  rfl

theorem Fml.stepFocusR_havoc {φ φ' : Fml C Γ} {f : Focus C} (h : φ.stepFocusR k = some (f, φ')) :
    (Fml.havoc φ).stepFocusR k = some (f, .havoc φ') := by
  show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.havoc φ')) = _
  rw [h]
  rfl

theorem Fml.stepFocusR_all {x : Var} {p : PrimTy} {φ φ' : Fml C (.val p :: Γ)} {f : Focus C}
    (h : φ.stepFocusR k = some (f, φ')) : (Fml.all x p φ).stepFocusR k = some (f, .all x p φ') := by
  show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.all x p φ')) = _
  rw [h]
  rfl

theorem Fml.stepFocusR_bind {m : Modality} {x : Var} {t : LTy} {φ φ' : Fml C (t :: Γ)} {f : Focus C}
    (h : φ.stepFocusR k = some (f, φ')) :
    (Fml.bind m x t φ).stepFocusR k = some (f, .bind m x t φ') := by
  show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.bind m x t φ')) = _
  rw [h]
  rfl

theorem Fml.stepFocusR_anon {xs : List ((t : LTy) × Idx Γ t)} {φ φ' : Fml C Γ} {f : Focus C}
    (h : φ.stepFocusR k = some (f, φ')) : (Fml.anon xs φ).stepFocusR k = some (f, .anon xs φ') := by
  show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.anon xs φ')) = _
  rw [h]
  rfl

/-- A formula with no modality takes no step: a postcondition
(`Post.inactive`). -/
theorem Fml.stepFocusR_eq_none : {Γ : Ctx} → (φ : Fml C Γ) → φ.active = false →
    φ.stepFocusR k = none
  | _, .tt, _ | _, .eq .., _ | _, .defined _, _ | _, .not _, _ => rfl
  | _, .modal .., h => nomatch h
  | _, .and φ ψ, h => by
    have h' : φ.active = false ∧ ψ.active = false := by
      exact Bool.or_eq_false_iff.mp h
    show (match φ.stepFocusR k with
      | some (f, φ') => some (f, Fml.and φ' ψ)
      | none => (ψ.stepFocusR k).map fun (f, ψ') => (f, Fml.and φ ψ')) = _
    rw [Fml.stepFocusR_eq_none φ h'.1, Fml.stepFocusR_eq_none ψ h'.2]
    rfl
  | _, .imp a φ, h => by
    have h' : a.active = false ∧ φ.active = false := by
      exact Bool.or_eq_false_iff.mp h
    show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.imp a φ')) = _
    rw [Fml.stepFocusR_eq_none φ h'.2]; rfl
  | _, .upd m U φ, h => by
    show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.upd m U φ')) = _
    rw [Fml.stepFocusR_eq_none φ h]; rfl
  | _, .havoc φ, h => by
    show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.havoc φ')) = _
    rw [Fml.stepFocusR_eq_none φ h]; rfl
  | _, .all x p φ, h => by
    show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.all x p φ')) = _
    rw [Fml.stepFocusR_eq_none φ h]; rfl
  | _, .bind m x t φ, h => by
    show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.bind m x t φ')) = _
    rw [Fml.stepFocusR_eq_none φ h]; rfl
  | _, .anon xs φ, h => by
    show (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.anon xs φ')) = _
    rw [Fml.stepFocusR_eq_none φ h]; rfl

/-- The strategy's step is the line `stepFocusR` leaves. -/
theorem Fml.stepFocusR_snd {Γ : Ctx} (φ : Fml C Γ) :
    (φ.stepFocusR k).map Prod.snd = φ.stepR k := by
  induction φ with
  | tt | eq | defined | not => rfl
  | modal m P κ φ =>
    show (Fml.modalFocus k m P κ φ).map Prod.snd = Fml.modalStep k m P κ φ
    cases P with
    | nil => rfl
    | cons s ω => rfl
  | and φ ψ ihφ ihψ =>
    show (match φ.stepFocusR k with
      | some (f, φ') => some (f, Fml.and φ' ψ)
      | none => (ψ.stepFocusR k).map fun (f, ψ') => (f, Fml.and φ ψ')).map Prod.snd =
      (match Fml.stepR k φ with
      | some φ' => some (Fml.and φ' ψ)
      | none => (Fml.stepR k ψ).map (Fml.and φ))
    rw [← ihφ, ← ihψ]
    cases φ.stepFocusR k with
    | some p => rfl
    | none => cases ψ.stepFocusR k <;> rfl
  | imp a φ _ ih =>
    show ((φ.stepFocusR k).map fun (f, φ') => (f, Fml.imp a φ')).map Prod.snd =
      (Fml.stepR k φ).map (Fml.imp a)
    rw [← ih]; cases φ.stepFocusR k <;> rfl
  | upd m U φ ih =>
    show ((φ.stepFocusR k).map fun (f, φ') => (f, Fml.upd m U φ')).map Prod.snd =
      (Fml.stepR k φ).map (Fml.upd m U)
    rw [← ih]; cases φ.stepFocusR k <;> rfl
  | havoc φ ih =>
    show ((φ.stepFocusR k).map fun (f, φ') => (f, Fml.havoc φ')).map Prod.snd =
      (Fml.stepR k φ).map Fml.havoc
    rw [← ih]; cases φ.stepFocusR k <;> rfl
  | all x p φ ih =>
    show ((φ.stepFocusR k).map fun (f, φ') => (f, Fml.all x p φ')).map Prod.snd =
      (Fml.stepR k φ).map (Fml.all x p)
    rw [← ih]; cases φ.stepFocusR k <;> rfl
  | bind m x t φ ih =>
    show ((φ.stepFocusR k).map fun (f, φ') => (f, Fml.bind m x t φ')).map Prod.snd =
      (Fml.stepR k φ).map (Fml.bind m x t)
    rw [← ih]; cases φ.stepFocusR k <;> rfl
  | anon xs φ ih =>
    show ((φ.stepFocusR k).map fun (f, φ') => (f, Fml.anon xs φ')).map Prod.snd =
      (Fml.stepR k φ).map (Fml.anon xs)
    rw [← ih]; cases φ.stepFocusR k <;> rfl

/-! ### `Fml.active` and `Fml.maxIdx` along the connectives

`Fml.active` and `Fml.maxIdx` are `casesOn` definitions, which have no
equation lemmas: a proof over a line is put together from these, each the
recursor's own unfolding, with the parts' values computed by the kernel. -/

theorem Fml.active_and_false {φ ψ : Fml C Γ} (h : φ.active = false) (h' : ψ.active = false) :
    (Fml.and φ ψ).active = false := by
  show (φ.active || ψ.active) = false
  rw [h, h']; rfl

theorem Fml.active_imp_false {a φ : Fml C Γ} (h : a.active = false) (h' : φ.active = false) :
    (Fml.imp a φ).active = false := by
  show (a.active || φ.active) = false
  rw [h, h']; rfl

theorem Fml.active_not_false {φ : Fml C Γ} (h : φ.active = false) : (Fml.not φ).active = false := h

theorem Fml.active_upd_false {Γ' : Ctx} {m : Modality} {U : Upd C Γ Γ'} {φ : Fml C Γ'}
    (h : φ.active = false) : (Fml.upd m U φ).active = false := h

theorem Fml.active_havoc_false {φ : Fml C Γ} (h : φ.active = false) :
    (Fml.havoc φ).active = false := h

theorem Fml.active_all_false {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
    (h : φ.active = false) : (Fml.all x p φ).active = false := h

theorem Fml.active_bind_false {m : Modality} {x : Var} {t : LTy} {φ : Fml C (t :: Γ)}
    (h : φ.active = false) : (Fml.bind m x t φ).active = false := h

theorem Fml.active_anon_false {xs : List ((t : LTy) × Idx Γ t)} {φ : Fml C Γ}
    (h : φ.active = false) : (Fml.anon xs φ).active = false := h

theorem Fml.maxIdx_not_eq {φ : Fml C Γ} {a : Nat} (h : φ.maxIdx = a) : (Fml.not φ).maxIdx = a := h

theorem Fml.maxIdx_and_eq {φ ψ : Fml C Γ} {a b : Nat} (h : φ.maxIdx = a) (h' : ψ.maxIdx = b) :
    (Fml.and φ ψ).maxIdx = max a b := by
  show max φ.maxIdx ψ.maxIdx = _
  rw [h, h']

theorem Fml.maxIdx_imp_eq {φ ψ : Fml C Γ} {a b : Nat} (h : φ.maxIdx = a) (h' : ψ.maxIdx = b) :
    (Fml.imp φ ψ).maxIdx = max a b := by
  show max φ.maxIdx ψ.maxIdx = _
  rw [h, h']

theorem Fml.maxIdx_upd_eq {Γ' : Ctx} {m : Modality} {U : Upd C Γ Γ'} {φ : Fml C Γ'} {a b : Nat}
    (h : U.maxIdx = a) (h' : φ.maxIdx = b) : (Fml.upd m U φ).maxIdx = max a b := by
  show max U.maxIdx φ.maxIdx = _
  rw [h, h']

theorem Fml.maxIdx_modal_eq {Γ₁ Γ₀ : Ctx} {m : Modality} {P : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀}
    {φ : Fml C Γ₀} {a b : Nat} (h : max P.maxIdx κ.maxIdx = a) (h' : φ.maxIdx = b) :
    (Fml.modal m P κ φ).maxIdx = max a b := by
  show max (max P.maxIdx κ.maxIdx) φ.maxIdx = _
  rw [h, h']

theorem Fml.maxIdx_havoc_eq {φ : Fml C Γ} {a : Nat} (h : φ.maxIdx = a) :
    (Fml.havoc φ).maxIdx = a := h

theorem Fml.maxIdx_all_eq {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)} {a : Nat}
    (h : φ.maxIdx = a) : (Fml.all x p φ).maxIdx = max x.idx a := by
  show max x.idx φ.maxIdx = _
  rw [h]

theorem Fml.maxIdx_bind_eq {m : Modality} {x : Var} {t : LTy} {φ : Fml C (t :: Γ)} {a : Nat}
    (h : φ.maxIdx = a) : (Fml.bind m x t φ).maxIdx = max x.idx a := by
  show max x.idx φ.maxIdx = _
  rw [h]

theorem Fml.maxIdx_anon_eq {xs : List ((t : LTy) × Idx Γ t)} {φ : Fml C Γ} {a : Nat}
    (h : φ.maxIdx = a) : (Fml.anon xs φ).maxIdx = a := h

end Equations

/-! ## The relations -/

/-- A rule as a chain names it: a derivation of a taclet at the fresh index
`k` under `m` on the statement `s`, or the empty modality going through its
frames (`emptyModality`). -/
inductive StepRule (C : Contract) : Type where
  | taclet (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
      (d : Rule C k m s p)
  | emptyModality

/-- The statement the rule fires on. -/
def StepRule.focus : StepRule C → Focus C
  | .taclet k m s _ _ => .stmt k m s
  | .emptyModality => .empty

section Relations

variable {Γ : Ctx}

/-- `φ ~> ψ`: the strategy's step turns `φ` into `ψ`. -/
def Fml.OneStep (φ ψ : Fml C Γ) : Prop := φ.step = some ψ

/-- `φ ~[r]~> ψ`: the step fires `r`'s statement, and leaves `ψ`. -/
def Fml.StepBy (r : StepRule C) (φ ψ : Fml C Γ) : Prop :=
  φ.stepFocusR φ.fresh = some (r.focus, ψ)

/-- `φ ~*> ψ`: zero or more steps, the derivation as a value. -/
inductive Fml.Steps : Fml C Γ → Fml C Γ → Type where
  | refl (φ : Fml C Γ) : Fml.Steps φ φ
  | cons {φ ψ χ : Fml C Γ} : Fml.OneStep φ ψ → Fml.Steps ψ χ → Fml.Steps φ χ

/-- An arrow of a chain on scoped lines. -/
inductive Link (C : Contract) : Type where
  /-- `~>` -/
  | one
  /-- `~*>` -/
  | many
  /-- `~[r]~>`, a rule of the strategy. -/
  | rule (r : StepRule C)
  /-- `~[sequentialToParallel]~>` while the program is open: the `n + 1`
  updates from position `k` of the spine merged (`Calculus/Merge.lean`). -/
  | merge (k n : Nat)
  /-- `~[n]~>` while the program is open: a rewrite of the scoped line
  (`Calculus/RewriteScoped.lean`), named `n` as the chain writes it. -/
  | rw (n : String) (r : FmlRw C)

/-- The relation an arrow stands for. -/
@[reducible] def Link.Rel : Link C → Fml C Γ → Fml C Γ → Prop
  | .one => Fml.OneStep
  | .many => fun φ ψ => Nonempty (Fml.Steps φ ψ)
  | .rule r => Fml.StepBy r
  | .merge k n => Fml.MergeBy k n
  | .rw n r => Fml.RwBy n r

/-- `φ ~> φ₁ ~*> φ₂ …`: every link of a chain that starts at `φ` holds. -/
@[reducible] def Fml.Via : Fml C Γ → List (Link C × Fml C Γ) → Prop
  | _, [] => True
  | φ, [(l, ψ)] => l.Rel φ ψ
  | φ, (l, ψ) :: w :: ws => l.Rel φ ψ ∧ Fml.Via ψ (w :: ws)

/-- The last line of a chain. -/
def Fml.Via.last : Fml C Γ → List (Link C × Fml C Γ) → Fml C Γ
  | φ, [] => φ
  | _, (_, ψ) :: ws => Fml.Via.last ψ ws

end Relations

section Build

variable {Γ : Ctx} {φ ψ : Fml C Γ} {k : Nat} {f : Focus C}

/-- A step at the index its fresh names start from. -/
theorem Fml.OneStep.ofFocus (hk : φ.fresh = k) (h : φ.stepFocusR k = some (f, ψ)) :
    Fml.OneStep φ ψ := by
  unfold Fml.OneStep Fml.step
  rw [hk, ← Fml.stepFocusR_snd, h]
  rfl

/-- A named step at the index its fresh names start from. -/
theorem Fml.StepBy.ofFocus {r : StepRule C} (hk : φ.fresh = k)
    (h : φ.stepFocusR k = some (r.focus, ψ)) : Fml.StepBy r φ ψ := by
  unfold Fml.StepBy
  rw [hk]
  exact h

theorem Fml.StepBy.oneStep {r : StepRule C} (h : Fml.StepBy r φ ψ) : Fml.OneStep φ ψ :=
  Fml.OneStep.ofFocus rfl h

/-- The fresh index is above the formula and contract-root indices. -/
theorem Fml.fresh_eq {n r : Nat} (h : φ.maxIdx = n) (hr : C.rootMaxIdx = r) :
    φ.fresh = max n r + 1 := by
  unfold Fml.fresh
  rw [h, hr]

theorem Fml.OneStep.unique {χ : Fml C Γ} (s : Fml.OneStep φ ψ) (t : Fml.OneStep φ χ) : ψ = χ :=
  Option.some.inj (s.symm.trans t)

end Build

/-! ## Soundness

A step is sound: the line it leaves gives the line it came from, in every
state (`Fml.stepFocusR_sound`), from `Stmt.sound` at the statement it fires
on and `holds_exit` for a finished program, through the connectives the
strategy looks through. -/

section Sound

/-- The connectives the strategy looks through keep a step sound. -/
theorem Fml.stepFocusR_sound {k : Nat} : {Γ : Ctx} → (φ : Fml C Γ) → ∀ {f : Focus C} {ψ : Fml C Γ},
    φ.stepFocusR k = some (f, ψ) → ∀ σ, holds σ ψ → holds σ φ
  | _, .tt, _, _, h, _, _ | _, .eq .., _, _, h, _, _ | _, .defined _, _, _, h, _, _
  | _, .not _, _, _, h, _, _ => nomatch h
  | _, .modal m P κ φ, f, ψ, h, σ, hψ => by
    have h : Fml.modalFocus k m P κ φ = some (f, ψ) := h
    cases P with
    | nil =>
      cases h
      exact holds_exit m κ φ σ hψ
    | cons s ω =>
      have h : some (Focus.stmt k m s, (s.step k m).fml m ω κ φ) = some (f, ψ) := h
      cases h
      exact Stmt.sound k m s _ rfl σ ω κ φ hψ
  | _, .and φ₁ φ₂, f, ψ, h, σ, hψ => by
    have h : (match φ₁.stepFocusR k with
      | some (f, φ') => some (f, Fml.and φ' φ₂)
      | none => (φ₂.stepFocusR k).map fun (f, ψ') => (f, Fml.and φ₁ ψ')) = some (f, ψ) := h
    cases h₁ : φ₁.stepFocusR k with
    | some q =>
      rw [h₁] at h
      obtain ⟨f', φ'⟩ := q
      cases h
      exact ⟨Fml.stepFocusR_sound φ₁ h₁ σ hψ.1, hψ.2⟩
    | none =>
      rw [h₁] at h
      cases h₂ : φ₂.stepFocusR k with
      | none => rw [h₂] at h; cases h
      | some q =>
        rw [h₂] at h
        obtain ⟨f', φ'⟩ := q
        cases h
        exact ⟨hψ.1, Fml.stepFocusR_sound φ₂ h₂ σ hψ.2⟩
  | _, .imp a φ, f, ψ, h, σ, hψ => by
    have h : (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.imp a φ')) = some (f, ψ) := h
    cases h₁ : φ.stepFocusR k with
    | none => rw [h₁] at h; cases h
    | some q =>
      rw [h₁] at h
      obtain ⟨f', φ'⟩ := q
      cases h
      exact fun ha => Fml.stepFocusR_sound φ h₁ σ (hψ ha)
  | _, .upd m U φ, f, ψ, h, σ, hψ => by
    have h : (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.upd m U φ')) = some (f, ψ) := h
    cases h₁ : φ.stepFocusR k with
    | none => rw [h₁] at h; cases h
    | some q =>
      rw [h₁] at h
      obtain ⟨f', φ'⟩ := q
      cases h
      exact Upd.afterT_imp hψ fun σ' a => Fml.stepFocusR_sound φ h₁ σ' a
  | _, .havoc φ, f, ψ, h, σ, hψ => by
    have h : (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.havoc φ')) = some (f, ψ) := h
    cases h₁ : φ.stepFocusR k with
    | none => rw [h₁] at h; cases h
    | some q =>
      rw [h₁] at h
      obtain ⟨f', φ'⟩ := q
      cases h
      exact fun st nt => Fml.stepFocusR_sound φ h₁ _ (hψ st nt)
  | _, .all x p φ, f, ψ, h, σ, hψ => by
    have h : (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.all x p φ')) = some (f, ψ) := h
    cases h₁ : φ.stepFocusR k with
    | none => rw [h₁] at h; cases h
    | some q =>
      rw [h₁] at h
      obtain ⟨f', φ'⟩ := q
      cases h
      exact fun v => Fml.stepFocusR_sound φ h₁ _ (hψ v)
  | _, .bind m x t φ, f, ψ, h, σ, hψ => by
    have h : (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.bind m x t φ')) = some (f, ψ) := h
    cases h₁ : φ.stepFocusR k with
    | none => rw [h₁] at h; cases h
    | some q =>
      rw [h₁] at h
      obtain ⟨f', φ'⟩ := q
      cases h
      exact Modality.forallB_imp (fun v => Fml.stepFocusR_sound φ h₁ _) hψ
  | _, .anon xs φ, f, ψ, h, σ, hψ => by
    have h : (φ.stepFocusR k).map (fun (f, φ') => (f, Fml.anon xs φ')) = some (f, ψ) := h
    cases h₁ : φ.stepFocusR k with
    | none => rw [h₁] at h; cases h
    | some q =>
      rw [h₁] at h
      obtain ⟨f', φ'⟩ := q
      cases h
      exact fun b => Fml.stepFocusR_sound φ h₁ _ (hψ b)

variable {Γ : Ctx} {φ ψ : Fml C Γ}

/-- Wherever `ψ` holds, `φ` does: what a chain composes to (`φ ~~> ψ`). -/
def Fml.Leads (φ ψ : Fml C Γ) : Prop := ∀ σ, holds σ ψ → holds σ φ

theorem Fml.OneStep.sound (s : Fml.OneStep φ ψ) : Fml.Leads φ ψ := by
  have h : φ.stepR φ.fresh = some ψ := s
  rw [← Fml.stepFocusR_snd] at h
  cases h₁ : φ.stepFocusR φ.fresh with
  | none => rw [h₁] at h; cases h
  | some q =>
    rw [h₁] at h
    cases h
    exact Fml.stepFocusR_sound φ h₁

theorem Fml.StepBy.sound {r : StepRule C} (h : Fml.StepBy r φ ψ) : Fml.Leads φ ψ :=
  h.oneStep.sound

theorem Fml.Steps.sound : {φ ψ : Fml C Γ} → Fml.Steps φ ψ → Fml.Leads φ ψ
  | _, _, .refl _ => fun _ h => h
  | _, _, .cons s c => fun σ h => s.sound σ (Fml.Steps.sound c σ h)

theorem Fml.Leads.comp {χ : Fml C Γ} (h₁ : Fml.Leads φ ψ) (h₂ : Fml.Leads ψ χ) : Fml.Leads φ χ :=
  fun σ h => h₁ σ (h₂ σ h)

theorem Link.Rel.sound : {l : Link C} → l.Rel φ ψ → Fml.Leads φ ψ
  | .one, h => Fml.OneStep.sound h
  | .many, ⟨c⟩ => c.sound
  | .rule _, h => Fml.StepBy.sound h
  | .merge k n, h => Fml.mergeRun_leads k n _ h
  | .rw _ r, h => r.sound h

/-- **A chain leads from its first line to its last.** -/
theorem Fml.Via.leads : {φ : Fml C Γ} → {ws : List (Link C × Fml C Γ)} → Fml.Via φ ws →
    Fml.Leads φ (Fml.Via.last φ ws)
  | _, [], _ => fun _ h => h
  | _, [(_, _)], v => Link.Rel.sound v
  | _, (_, _) :: _ :: _, v => (Link.Rel.sound v.1).comp (Fml.Via.leads v.2)

/-- A chain whose last line is valid has a valid first line. -/
theorem Fml.Via.valid {φ : Fml C []} {ws : List (Link C × Fml C [])} (v : Fml.Via φ ws)
    (h : Valid (Fml.Via.last φ ws)) : Valid φ :=
  fun σ => v.leads σ (h σ)

theorem Fml.Steps.valid {φ ψ : Fml C []} (c : Fml.Steps φ ψ) (h : Valid ψ) : Valid φ :=
  fun σ => c.sound σ (h σ)

theorem Fml.OneStep.valid {φ ψ : Fml C []} (s : Fml.OneStep φ ψ) (h : Valid ψ) : Valid φ :=
  fun σ => s.sound σ (h σ)

theorem Fml.StepBy.valid {r : StepRule C} {φ ψ : Fml C []} (s : Fml.StepBy r φ ψ) (h : Valid ψ) :
    Valid φ :=
  fun σ => s.sound σ (h σ)

/-! ## Composing: `~~>`, segments, `calc`

`φ ~~> ψ` on scoped lines is `Fml.Leads` (wherever `ψ` holds, `φ` does):
what a chain composes to, and a segment's link to the next
(`(seg₁ ..).leads.via (seg₂ ..)`).  Past the program the line written is
read where it stands and names the line the chain reaches up to its
binders' names (`Fml.LeadsK φ L`). -/

theorem Fml.Leads.self (φ : Fml C Γ) : Fml.Leads φ φ := fun _ h => h

/-- A chain goes on with a segment that starts where it ends. -/
theorem Fml.Leads.via {ψ : Fml C Γ} {ws : List (Link C × Fml C Γ)} (h : Fml.Leads φ ψ)
    (v : Fml.Via ψ ws) : Fml.Leads φ (Fml.Via.last ψ ws) :=
  h.comp v.leads

theorem Fml.Leads.valid {φ ψ : Fml C []} (h : Fml.Leads φ ψ) (hψ : Valid ψ) : Valid φ :=
  fun σ => h σ (hψ σ)

/-! ### Binder names

A binder's name (`∀ uint x;`, a hidden binder, an update's declaration) is
for printing: a local is read by its position.  Two lines that differ in
their binders' names alone hold alike (`holds_eraseNames`), which is how the
line written past the program names the line a chain reaches. -/

/-- The update with its declarations' names blanked. -/
def Upd.eraseNames {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => .snoc (Upd.eraseNames U) e
  | _, .decl U _ r => .decl (Upd.eraseNames U) (.user "_") r
  | _, .pop U h => .pop (Upd.eraseNames U) h
  | _, .drop U h => .drop (Upd.eraseNames U) h

/-- The formula with its binders' names blanked; a modality's program is
kept as it is. -/
def Fml.eraseNames : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .not φ => .not (Fml.eraseNames φ)
  | _, .and φ ψ => .and (Fml.eraseNames φ) (Fml.eraseNames ψ)
  | _, .imp φ ψ => .imp (Fml.eraseNames φ) (Fml.eraseNames ψ)
  | _, .upd m U φ => .upd m U.eraseNames (Fml.eraseNames φ)
  | _, .havoc φ => .havoc (Fml.eraseNames φ)
  | _, .all _ p φ => .all (.user "_") p (Fml.eraseNames φ)
  | _, .bind m _ t φ => .bind m (.user "_") t (Fml.eraseNames φ)
  | _, .anon xs φ => .anon xs (Fml.eraseNames φ)
  | _, φ => φ

theorem Upd.exhAny_eraseNames {Γ : Ctx} (σ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.eraseNames.exhAny σ = U.exhAny σ
  | _, .nil => rfl
  | _, .snoc U e => by simp only [Upd.eraseNames, Upd.exhAny, Upd.exhAny_eraseNames σ U]
  | _, .decl U _ r => by simp only [Upd.eraseNames, Upd.exhAny, Upd.exhAny_eraseNames σ U]
  | _, .pop U _ => Upd.exhAny_eraseNames σ U
  | _, .drop U _ => Upd.exhAny_eraseNames σ U

theorem Upd.exhOk_eraseNames {Γ : Ctx} (σ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.eraseNames.exhOk σ = U.exhOk σ
  | _, .nil => rfl
  | _, .snoc U e => by simp only [Upd.eraseNames, Upd.exhOk, Upd.exhOk_eraseNames σ U]
  | _, .decl U _ r => by simp only [Upd.eraseNames, Upd.exhOk, Upd.exhOk_eraseNames σ U]
  | _, .pop U _ => Upd.exhOk_eraseNames σ U
  | _, .drop U _ => Upd.exhOk_eraseNames σ U

theorem Upd.exh_eraseNames {Γ Δ : Ctx} (σ : State C Γ) (U : Upd C Γ Δ) :
    U.eraseNames.exh σ = U.exh σ := by
  simp only [Upd.exh, Upd.exhAny_eraseNames, Upd.exhOk_eraseNames]

theorem Upd.globT_eraseNames {Γ : Ctx} (σ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.eraseNames.globT σ = U.globT σ
  | _, .nil => rfl
  | _, .snoc U e => by
    show (U.eraseNames.globT σ).bind (e.globT σ) = (U.globT σ).bind (e.globT σ)
    rw [Upd.globT_eraseNames σ U]
  | _, .decl U _ r => by
    show (U.eraseNames.globT σ).bind (fun g => (r.eval σ).bind fun _ => some g) =
      (U.globT σ).bind (fun g => (r.eval σ).bind fun _ => some g)
    rw [Upd.globT_eraseNames σ U]
  | _, .pop U _ => Upd.globT_eraseNames σ U
  | _, .drop U _ => Upd.globT_eraseNames σ U

theorem Upd.held_eraseNames {Γ : Ctx} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    ∀ {t : LTy} (i : Idx Δ t), U.eraseNames.held i = U.held i
  | _, .nil, _, _ => rfl
  | _, .snoc U e, _, i => by
    cases e with
    | «local» k r =>
      show Subst.set (Upd.held U.eraseNames) k r i = Subst.set (Upd.held U) k r i
      unfold Subst.set
      split
      · rfl
      · exact Upd.held_eraseNames U i
    | storage _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ =>
      exact Upd.held_eraseNames U i
  | _, .decl U _ _, _, i => by
    cases i with
    | here => rfl
    | there j => exact Upd.held_eraseNames U j
  | _, .pop U h, _, i => Upd.held_eraseNames U (i.ext h)
  | _, .drop U h, _, i => Upd.held_eraseNames U (i.wk h)

/-- **A binder's name is for printing**: a formula holds where it does with
its binders' names blanked. -/
theorem holds_eraseNames : {Γ : Ctx} → (σ : State C Γ) → (φ : Fml C Γ) →
    (holds σ φ.eraseNames ↔ holds σ φ)
  | _, _, .tt | _, _, .eq _ _ | _, _, .defined _ | _, _, .modal _ _ _ _ => Iff.rfl
  | _, σ, .not φ => not_congr (holds_eraseNames σ φ)
  | _, σ, .and φ ψ => and_congr (holds_eraseNames σ φ) (holds_eraseNames σ ψ)
  | _, σ, .imp φ ψ => imp_congr (holds_eraseNames σ φ) (holds_eraseNames σ ψ)
  | _, σ, .upd m U φ => by
    show U.eraseNames.afterT m σ (holds · φ.eraseNames) ↔ U.afterT m σ (holds · φ)
    unfold Upd.afterT Upd.Lands
    simp only [Upd.globT_eraseNames, Upd.held_eraseNames, holds_eraseNames, Upd.exh_eraseNames]
  | _, σ, .havoc φ => forall_congr' fun _ => forall_congr' fun _ => holds_eraseNames _ φ
  | _, σ, .all _ _ φ => forall_congr' fun _ => holds_eraseNames _ φ
  | _, σ, .bind _ _ _ φ => forall_congr' fun _ => holds_eraseNames _ φ
  | _, σ, .anon _ φ => forall_congr' fun _ => holds_eraseNames _ φ

/-- `φ ~~> L` past the program: `φ` leads to a line `B` that is the line
written `L` up to its binders' names (`Fml.eraseNames`).  The line written
is read where it stands (`dl![m]{ … }`), so it names `B` by its text, and
`Fml.LeadsK.valid` proves `φ` from `L`. -/
def Fml.LeadsK (φ L : Fml C []) : Prop :=
  ∃ B : Fml C [], Fml.Leads φ B ∧ B.eraseNames = L.eraseNames

/-- A `~~>` to a line that is the one written up to its binders' names. -/
theorem Fml.Leads.leadsK {φ B L : Fml C []} (h : Fml.Leads φ B)
    (he : B.eraseNames = L.eraseNames := by rfl) : Fml.LeadsK φ L :=
  ⟨B, h, he⟩

/-- A chain past the program, as `~~>` to the line written. -/
theorem Fml.Via.leadsK {φ L : Fml C []} {ws : List (Link C × Fml C [])}
    (v : Fml.Via φ ws) (he : (Fml.Via.last φ ws).eraseNames = L.eraseNames := by rfl) :
    Fml.LeadsK φ L :=
  v.leads.leadsK he

/-- **`~~>` past the program is a proof**: `φ` is valid where the line
written is. -/
theorem Fml.LeadsK.valid {φ L : Fml C []} (h : Fml.LeadsK φ L) (hL : Valid L) : Valid φ := by
  obtain ⟨B, hl, he⟩ := h
  refine hl.valid fun σ => (holds_eraseNames σ B).1 ?_
  rw [he]
  exact (holds_eraseNames σ L).2 (hL σ)

/-! `calc` chains `~>`, `~*>`, `~[r]~>` and the scoped merges; the result is
a derivation `~*>` where every link is a step, `~~>` otherwise. -/

/-- Two derivations, one after the other. -/
def Fml.Steps.trans : {φ ψ χ : Fml C Γ} → Fml.Steps φ ψ → Fml.Steps ψ χ → Fml.Steps φ χ
  | _, _, _, .refl _, d => d
  | _, _, _, .cons s c, d => .cons s (Fml.Steps.trans c d)

/-- One step as a derivation. -/
def Fml.Steps.single {φ ψ : Fml C Γ} (s : Fml.OneStep φ ψ) : Fml.Steps φ ψ := .cons s (.refl ψ)

/-- A named step as a derivation, its label dropped. -/
def Fml.StepBy.steps {r : StepRule C} {φ ψ : Fml C Γ} (h : Fml.StepBy r φ ψ) : Fml.Steps φ ψ :=
  .single h.oneStep

/-- The number of steps. -/
def Fml.Steps.length : {φ ψ : Fml C Γ} → Fml.Steps φ ψ → Nat
  | _, _, .refl _ => 0
  | _, _, .cons _ c => c.length + 1

instance : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) Fml.Steps Fml.Steps Fml.Steps := ⟨Fml.Steps.trans⟩
instance : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) Fml.OneStep Fml.Steps Fml.Steps := ⟨.cons⟩
instance : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) Fml.Steps Fml.OneStep Fml.Steps :=
  ⟨fun c s => c.trans (.single s)⟩
instance : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) Fml.OneStep Fml.OneStep Fml.Steps :=
  ⟨fun s t => .cons s (.single t)⟩
instance {r : StepRule C} : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) (Fml.StepBy r) Fml.Steps Fml.Steps :=
  ⟨fun h c => .cons h.oneStep c⟩
instance {r : StepRule C} : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) Fml.Steps (Fml.StepBy r) Fml.Steps :=
  ⟨fun c h => c.trans h.steps⟩
instance {r : StepRule C} : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) (Fml.StepBy r) Fml.OneStep Fml.Steps :=
  ⟨fun h s => .cons h.oneStep (.single s)⟩
instance {r : StepRule C} : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) Fml.OneStep (Fml.StepBy r) Fml.Steps :=
  ⟨fun s h => .cons s h.steps⟩
instance {r r' : StepRule C} :
    @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) (Fml.StepBy r) (Fml.StepBy r') Fml.Steps :=
  ⟨fun h h' => .cons h.oneStep h'.steps⟩

universe u v

/-- A relation between scoped lines whose evidence carries the second line's
truth back to the first: every arrow of a chain, and `~~>` itself. -/
class Fml.SoundRel (R : Fml C Γ → Fml C Γ → Sort u) : Prop where
  leads : ∀ {φ ψ : Fml C Γ}, R φ ψ → Fml.Leads φ ψ

instance : Fml.SoundRel (@Fml.OneStep C Γ) := ⟨Fml.OneStep.sound⟩
instance : Fml.SoundRel (@Fml.Steps C Γ) := ⟨Fml.Steps.sound⟩
instance {r : StepRule C} : Fml.SoundRel (@Fml.StepBy C Γ r) := ⟨Fml.StepBy.sound⟩
instance {k n : Nat} : Fml.SoundRel (@Fml.MergeBy C Γ k n) := ⟨fun h => Fml.mergeRun_leads k n _ h⟩
instance {n : String} {r : FmlRw C} : Fml.SoundRel (@Fml.RwBy C Γ n r) := ⟨fun h => r.sound h⟩
instance : Fml.SoundRel (@Fml.Leads C Γ) := ⟨id⟩

/-- A `calc` with a merge in it composes to `~~>`; one of steps alone still
composes to `~*>`, whose instances come first. -/
instance (priority := low) {R : Fml C Γ → Fml C Γ → Sort u} {S : Fml C Γ → Fml C Γ → Sort v}
    [Fml.SoundRel R] [Fml.SoundRel S] : @Trans (Fml C Γ) (Fml C Γ) (Fml C Γ) R S Fml.Leads :=
  ⟨fun a b => (Fml.SoundRel.leads a).comp (Fml.SoundRel.leads b)⟩

/-! ## The evidence is unique -/

/-- A rule is fixed by the statement it fires on: its premise by
`Rule.premise_unique`, its derivation by proof irrelevance. -/
theorem StepRule.eq_of_focus : {r r' : StepRule C} → r.focus = r'.focus → r = r'
  | .taclet k m s p d, .taclet k' m' s' p' d', h => by
    simp only [StepRule.focus, Focus.stmt.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, h⟩ := h
    obtain rfl := eq_of_heq h
    obtain rfl := d.premise_unique d'
    rfl
  | .emptyModality, .emptyModality, _ => rfl
  | .taclet .., .emptyModality, h | .emptyModality, .taclet .., h => Focus.noConfusion h

/-- A step fires one rule, and leaves one line. -/
theorem Fml.StepBy.unique {r r' : StepRule C} {χ : Fml C Γ} (h : Fml.StepBy r φ ψ)
    (h' : Fml.StepBy r' φ χ) : r = r' ∧ ψ = χ := by
  have := h.symm.trans h'
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact ⟨StepRule.eq_of_focus this.1, this.2⟩

/-- Two derivations of the same length between the same ends are one. -/
theorem Fml.Steps.eq_of_length : {φ ψ : Fml C Γ} → (c d : Fml.Steps φ ψ) → c.length = d.length → c = d
  | _, _, .refl _, .refl _, _ => rfl
  | _, _, .refl _, .cons _ _, h | _, _, .cons _ _, .refl _, h => by
    simp only [Fml.Steps.length] at h
    omega
  | _, _, .cons (ψ := ψ₁) s c, .cons (ψ := ψ₂) s' c', h => by
    obtain rfl : ψ₁ = ψ₂ := s.unique s'
    have : c.length = c'.length := by simp only [Fml.Steps.length] at h; omega
    rw [Fml.Steps.eq_of_length c c' this]

/-- Along a derivation a measure the step decreases does not go up. -/
theorem Fml.Steps.measure_le (μ : Fml C Γ → Nat)
    (hμ : ∀ {φ ψ : Fml C Γ}, Fml.OneStep φ ψ → μ ψ < μ φ) :
    {φ ψ : Fml C Γ} → Fml.Steps φ ψ → μ ψ ≤ μ φ
  | _, _, .refl _ => Nat.le_refl _
  | _, _, .cons s c => Nat.le_of_lt (Nat.lt_of_le_of_lt (c.measure_le μ hμ) (hμ s))

/-- A derivation between two formulas is unique, given a measure every step
decreases: it cannot come back to where it started. -/
theorem Fml.Steps.eq_of_measure (μ : Fml C Γ → Nat)
    (hμ : ∀ {φ ψ : Fml C Γ}, Fml.OneStep φ ψ → μ ψ < μ φ) :
    {φ ψ : Fml C Γ} → (c d : Fml.Steps φ ψ) → c = d
  | _, _, .refl _, .refl _ => rfl
  | _, _, .refl _, .cons s c | _, _, .cons s c, .refl _ =>
    absurd (hμ s) (Nat.not_lt.2 (c.measure_le μ hμ))
  | _, _, .cons (ψ := ψ₁) s c, .cons (ψ := ψ₂) s' c' => by
    obtain rfl : ψ₁ = ψ₂ := s.unique s'
    rw [Fml.Steps.eq_of_measure μ hμ c c']

/-- The strategy run `n` steps, as a derivation. -/
def Fml.Steps.ofSymex : (n : Nat) → (φ : Fml C Γ) → Fml.Steps φ (symex n φ)
  | 0, φ => .refl φ
  | n + 1, φ =>
    match hs : φ.step with
    | some ψ => (congrArg (Fml.Steps φ) (by simp only [symex, hs])).mpr (.cons hs (Fml.Steps.ofSymex n ψ))
    | none => (congrArg (Fml.Steps φ) (by simp only [symex, hs])).mpr (.refl φ)

end Sound

end Solidity
