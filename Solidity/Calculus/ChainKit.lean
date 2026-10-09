import Solidity.Calculus.NotationResolve
import Solidity.Calculus.Taclet
import Solidity.Calculus.HoldsErase
import Solidity.Calculus.Sound
import Solidity.Calculus.Merge
import Solidity.Calculus.RewriteScoped
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

theorem Fml.stepFocusR_modal {Γ₁ Γ₀ : Ctx} (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) : Fml.stepFocusR k (.modal m P κ φ) = Fml.modalFocus k m P κ φ := rfl

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

/-! ## A postcondition, erased

Past the program a chain goes on by `Calculus/ChainRewrites.lean`'s rewrites,
on the erasure of its line (`Fml.erase`): its postcondition `φ : Post C Γ`
is then `Update.lean`'s postcondition `φ.erase ns` (`Chains.lean`'s
`Post`), which names no fresh variable when the names `ns` of its context
do not (`Post.erase`). -/

section Erase

/-- Every variable of the list has an index at most `n`. -/
def IdxLe (n : Nat) (xs : List Var) : Prop := ∀ x ∈ xs, x.idx ≤ n

theorem IdxLe.mono {n n' : Nat} {xs : List Var} (h : IdxLe n xs) (hn : n ≤ n') : IdxLe n' xs :=
  fun x hx => Nat.le_trans (h x hx) hn

theorem IdxLe.append {n : Nat} {xs ys : List Var} (h : IdxLe n xs) (h' : IdxLe n ys) :
    IdxLe n (xs ++ ys) := fun x hx => by
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem IdxLe.cons {n : Nat} {x : Var} {xs : List Var} (hx : x.idx ≤ n) (h : IdxLe n xs) :
    IdxLe n (x :: xs) := fun y hy => by
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact h y hy

theorem IdxLe.maxIdx (xs : List Var) : IdxLe (Solidity.maxIdx xs) xs := fun _ hx => le_maxIdx hx

theorem IdxLe.maxIdx_le {n : Nat} {xs : List Var} (h : IdxLe n xs) : Solidity.maxIdx xs ≤ n := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact Nat.max_le.2 ⟨h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem Idx.name_idxLe {Γ : Ctx} {t : LTy} {n : Nat} {ns : List Var} (h : IdxLe n ns)
    (i : Idx Γ t) : (i.name ns).idx ≤ n := by
  unfold Idx.name
  rw [List.getD_eq_getElem?_getD]
  cases hg : ns[i.toNat]? with
  | none => exact Nat.zero_le _
  | some x => exact h x (List.mem_of_getElem? hg)

theorem Tm.erase_idxLe {Γ : Ctx} {n : Nat} {ns : List Var} (h : IdxLe n ns) :
    {s : Srt} → (t : Tm C Γ s) → IdxLe n (t.erase ns).vars
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i =>
    IdxLe.cons (Idx.name_idxLe h i) fun _ hx => nomatch hx
  | _, .netOf i a => IdxLe.cons (Idx.name_idxLe h i) (Tm.erase_idxLe h a)
  | _, .app0 _ => fun _ hx => nomatch hx
  | _, .app1 o ho a => by
    have ih := Tm.erase_idxLe h a
    show IdxLe n (Surface.Tm.app1 o (a.erase ns)).vars
    cases o <;> first
      | exact ih
      | cases ho
  | _, .app2 _ a b => IdxLe.append (Tm.erase_idxLe h a) (Tm.erase_idxLe h b)
  | _, .app3 _ a b c =>
    IdxLe.append (IdxLe.append (Tm.erase_idxLe h a) (Tm.erase_idxLe h b)) (Tm.erase_idxLe h c)

theorem Rhs.erase_idxLe {Γ : Ctx} {n : Nat} {ns : List Var} (h : IdxLe n ns) {x : Var}
    (hx : x.idx ≤ n) : {t : LTy} → (r : Rhs C Γ t) → IdxLe n (r.erase ns x).vars
  | _, .val t | _, .path t | _, .mref t | _, .store t => IdxLe.cons hx (Tm.erase_idxLe h t)
  | _, .unset | _, .saveNet | _, .saveNetMt => IdxLe.cons hx fun _ hx => nomatch hx

theorem UpdElem.erase_idxLe {Γ Δ : Ctx} {n : Nat} {ns ms : List Var} (h : IdxLe n ns)
    (hm : IdxLe n ms) : (e : UpdElem C Γ Δ) → IdxLe n (e.erase ns ms).vars
  | .local i r => Rhs.erase_idxLe h (Idx.name_idxLe hm i) r
  | .storage s => Tm.erase_idxLe h s
  | .memory m => Tm.erase_idxLe h m
  | .selfBalance _ a | .setBalance a => Tm.erase_idxLe h a
  | .net r _ a | .pay r a | .netMt r a => IdxLe.append (Tm.erase_idxLe h r) (Tm.erase_idxLe h a)

theorem Thin.names_subset : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (ns : List Var) →
    ∀ x ∈ h.names ns, x ∈ ns
  | _, _, .refl, _, _, hx => hx
  | _, _, .keep h, n :: ns, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Thin.names_subset h ns x hx)
  | _, _, .keep h, [], x, hx => Thin.names_subset h [] x hx
  | _, _, .drop h, ns, x, hx => List.mem_of_mem_tail (Thin.names_subset h ns.tail x hx)

theorem Upd.names_idxLe {Γ : Ctx} {ns : List Var} :
    {Δ : Ctx} → (U : Upd C Γ Δ) → IdxLe (max (Solidity.maxIdx ns) U.maxIdx) (U.names ns)
  | _, .nil => (IdxLe.maxIdx ns).mono (Nat.le_max_left _ _)
  | _, .snoc U _ => Upd.names_idxLe U
  | _, .decl U x _ => by
    show IdxLe (max (Solidity.maxIdx ns) (max U.maxIdx x.idx)) (x :: U.names ns)
    refine IdxLe.cons (by omega) ((Upd.names_idxLe U).mono (by omega))
  | _, .pop U _ => fun x hx => Upd.names_idxLe U x (List.mem_of_mem_drop hx)
  | _, .drop U h => fun x hx => Upd.names_idxLe U x (Thin.names_subset h _ x hx)

theorem _root_.Solidity.Surface.Upd.vars_append (U V : Surface.Upd C) :
    Surface.Upd.vars (U ++ V) = Surface.Upd.vars U ++ Surface.Upd.vars V := by
  induction U with
  | nil => rfl
  | cons e U ih => simp only [List.cons_append, Surface.Upd.vars, ih, List.append_assoc]

theorem Upd.erase_idxLe {Γ : Ctx} {ns : List Var} :
    {Δ : Ctx} → (U : Upd C Γ Δ) → IdxLe (max (Solidity.maxIdx ns) U.maxIdx) (Surface.Upd.vars (U.erase ns))
  | _, .nil => fun _ hx => nomatch hx
  | _, .snoc U e => by
    show IdxLe _ (Surface.Upd.vars (U.erase ns ++ [e.erase ns (U.names ns)]))
    rw [Surface.Upd.vars_append]
    exact IdxLe.append (Upd.erase_idxLe U)
      (IdxLe.append (UpdElem.erase_idxLe ((IdxLe.maxIdx ns).mono (Nat.le_max_left _ _))
        (Upd.names_idxLe U) e) fun _ hx => nomatch hx)
  | _, .decl U x r => by
    show IdxLe (max (Solidity.maxIdx ns) (max U.maxIdx x.idx)) (Surface.Upd.vars (U.erase ns ++ [r.erase ns x]))
    rw [Surface.Upd.vars_append]
    exact IdxLe.append ((Upd.erase_idxLe U).mono (by omega))
      (IdxLe.append (Rhs.erase_idxLe ((IdxLe.maxIdx ns).mono (by omega)) (by omega) r)
        fun _ hx => nomatch hx)
  | _, .pop U _ => Upd.erase_idxLe U
  | _, .drop U _ => Upd.erase_idxLe U

/-- The variables of a formula with no modality, erased: its context's names
and the names its binders give. -/
theorem Fml.erase_idxLe : {Γ : Ctx} → (φ : Fml C Γ) → φ.active = false → (ns : List Var) →
    IdxLe (max (Solidity.maxIdx ns) φ.maxIdx) (φ.erase ns).vars
  | _, .tt, _, _ => fun _ hx => nomatch hx
  | _, .eq a b, _, ns => IdxLe.append (Tm.erase_idxLe ((IdxLe.maxIdx ns).mono (Nat.le_max_left _ _)) a)
      (Tm.erase_idxLe ((IdxLe.maxIdx ns).mono (Nat.le_max_left _ _)) b)
  | _, .defined t, _, ns => Tm.erase_idxLe ((IdxLe.maxIdx ns).mono (Nat.le_max_left _ _)) t
  | _, .not φ, h, ns => Fml.erase_idxLe φ h ns
  | _, .and φ ψ, h, ns => by
    have h' := Bool.or_eq_false_iff.mp h
    show IdxLe (max _ (max φ.maxIdx ψ.maxIdx)) ((φ.erase ns).vars ++ (ψ.erase ns).vars)
    exact IdxLe.append ((Fml.erase_idxLe φ h'.1 ns).mono (by omega))
      ((Fml.erase_idxLe ψ h'.2 ns).mono (by omega))
  | _, .imp φ ψ, h, ns => by
    have h' := Bool.or_eq_false_iff.mp h
    show IdxLe (max _ (max φ.maxIdx ψ.maxIdx)) ((φ.erase ns).vars ++ (ψ.erase ns).vars)
    exact IdxLe.append ((Fml.erase_idxLe φ h'.1 ns).mono (by omega))
      ((Fml.erase_idxLe ψ h'.2 ns).mono (by omega))
  | _, .upd m U φ, h, ns => by
    show IdxLe (max (Solidity.maxIdx ns) (max U.maxIdx φ.maxIdx)) (Fml.erase ns (.upd m U φ)).vars
    have hφ : IdxLe (max (Solidity.maxIdx ns) (max U.maxIdx φ.maxIdx)) (φ.erase (U.names ns)).vars :=
      (Fml.erase_idxLe φ h (U.names ns)).mono
        (Nat.max_le.2 ⟨Nat.le_trans (Upd.names_idxLe U).maxIdx_le (by omega), by omega⟩)
    simp only [Fml.erase]
    split
    · exact hφ
    · exact IdxLe.append ((Upd.erase_idxLe U).mono (by omega)) hφ
  | _, .modal .., h, _ => nomatch h
  | _, .havoc φ, h, ns => Fml.erase_idxLe φ h ns
  | _, .all x p φ, h, ns => by
    show IdxLe (max _ (max x.idx φ.maxIdx)) (x :: (φ.erase (x :: ns)).vars)
    refine IdxLe.cons (by omega) ((Fml.erase_idxLe φ h (x :: ns)).mono ?_)
    show max (max x.idx (Solidity.maxIdx ns)) _ ≤ _
    omega
  | _, .bind _ x _ φ, h, ns => by
    show IdxLe (max _ (max x.idx φ.maxIdx)) (φ.erase (x :: ns)).vars
    refine (Fml.erase_idxLe φ h (x :: ns)).mono ?_
    show max (max x.idx (Solidity.maxIdx ns)) _ ≤ _
    omega
  | _, .anon xs φ, h, ns => by
    show IdxLe _ ((xs.map fun x => x.2.name ns) ++ (φ.erase ns).vars)
    refine IdxLe.append (fun y hy => ?_) (Fml.erase_idxLe φ h ns)
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
    exact Nat.le_trans (Idx.name_idxLe (IdxLe.maxIdx ns) x.2) (Nat.le_max_left _ _)

/-- `Update.lean`'s postcondition, the context's locals named by `ns`, which
name no fresh variable. -/
def Post.erase {Γ : Ctx} (φ : Post C Γ) (ns : List Var) (hns : Solidity.maxIdx ns = 0 := by decide) :
    NFml.Post C where
  fml := φ.fml.erase ns
  noFresh := Nat.le_zero.1 (Nat.le_trans (Fml.erase_idxLe φ.fml φ.inactive ns).maxIdx_le
    (by rw [hns, φ.noFresh]; exact Nat.le_refl _))

end Erase

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

/-- `Update.lean`'s formula with its outer quantifiers dropped: the
parameters a scoped line binds outermost (`∀ uint v;`, `Notation.lean`),
left free, as `dl!{ … }` reads them, so that the rewrites see the update. -/
def _root_.Solidity.NFml.dropAlls : Solidity.NFml C → Solidity.NFml C
  | .all _ _ φ => φ.dropAlls
  | φ => φ

/-- A formula is valid where it is with its outer quantifiers dropped. -/
theorem _root_.Solidity.NFml.holds_of_dropAlls : (φ : Solidity.NFml C) →
    (∀ τ, NFml.holds τ φ.dropAlls) → ∀ τ, NFml.holds τ φ
  | .all _ _ φ, h, _ => fun _ _ => Solidity.NFml.holds_of_dropAlls φ h _
  | .tt, h, τ | .eq .., h, τ | .defined _, h, τ | .not _, h, τ | .and .., h, τ | .imp .., h, τ
  | .upd .., h, τ | .havoc .., h, τ | .anon .., h, τ => h τ

/-- A chain that goes on past the program by `Calculus/ChainRewrites.lean`'s
rewrites: its scoped links, then, from the erasure `L` of its last scoped
line, its parameters left free (`Fml.dropAlls`), `Update.lean`'s
(`Solidity.NFml.Via`), the first a rewrite. -/
@[reducible] def Fml.ViaE (φ : Fml C []) (ws : List (Link C × Fml C [])) (L : Solidity.NFml C)
    (rs : List (NFml.Link C × Solidity.NFml C)) : Prop :=
  Fml.Via φ ws ∧ ((Fml.Via.last φ ws).erase []).dropAlls = L ∧ Solidity.NFml.Via L rs

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

/-- The fresh index from the formula's largest. -/
theorem Fml.fresh_eq {n : Nat} (h : φ.maxIdx = n) : φ.fresh = n + 1 := by
  unfold Fml.fresh
  rw [h]

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
      exact Modality.afterC_imp hψ fun τ a σ' e hx => Fml.stepFocusR_sound φ h₁ σ' (a σ' e hx)
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

/-- **A chain past the program** proves its first line from its last, given
that the last scoped line is valid where its erasure is (the bridge, for a
leaf with no modality the scoped closer's `Valid.of_erase`, W2 `symex`). -/
theorem Fml.ViaE.valid {φ : Fml C []} {ws : List (Link C × Fml C [])} {L : Solidity.NFml C}
    {rs : List (NFml.Link C × Solidity.NFml C)} (v : Fml.ViaE φ ws L rs)
    (bridge : (∀ τ, NFml.holds τ ((Fml.Via.last φ ws).erase [])) → Valid (Fml.Via.last φ ws))
    (h : ∀ τ, NFml.holds τ (Solidity.NFml.Via.last L rs)) : Valid φ :=
  v.1.valid (bridge (Solidity.NFml.holds_of_dropAlls _ (v.2.1 ▸ v.2.2.valid h)))

/-- **A chain past the program, closed**: the bridge of `Fml.ViaE.valid` is
`Proves.close` at the last scoped line, whose side conditions the kernel
decides (`Fml.closableB`: no modality left, updates of either modality; a
hidden binder's name avoids the empty context's). -/
theorem Fml.ViaE.valid_close {φ : Fml C []} {ws : List (Link C × Fml C [])} {L : Solidity.NFml C}
    {rs : List (NFml.Link C × Solidity.NFml C)} (v : Fml.ViaE φ ws L rs)
    (h : ∀ τ, NFml.holds τ (Solidity.NFml.Via.last L rs))
    (hc : (Fml.Via.last φ ws).closableB [] = true := by first | rfl | decide) : Valid φ :=
  v.valid (fun he => Proves.valid (R := .all) (Proves.close (Γ₀ := []) (H := .nil) [] rfl
    List.nodup_nil he hc fun _ _ h => nomatch h)) h

/-! ## Composing: `~~>`, segments, `calc`

`φ ~~> ψ` on scoped lines is `Fml.Leads` (wherever `ψ` holds, `φ` does):
what a chain composes to, and a segment's link to the next
(`(seg₁ ..).leads.via (seg₂ ..)`).  Past the program a chain's last line is
`Update.lean`'s, its erasure's: `Fml.LeadsE φ Z L` is `φ ~~> Z` for the last
scoped line `Z` and `L`'s rewrite chain from `Z`'s erasure, which `φ ~~> L`
elaborates to (`Calculus/Chains.lean`, `Z` the strategy's last line). -/

theorem Fml.Leads.self (φ : Fml C Γ) : Fml.Leads φ φ := fun _ h => h

/-- A chain goes on with a segment that starts where it ends. -/
theorem Fml.Leads.via {ψ : Fml C Γ} {ws : List (Link C × Fml C Γ)} (h : Fml.Leads φ ψ)
    (v : Fml.Via ψ ws) : Fml.Leads φ (Fml.Via.last ψ ws) :=
  h.comp v.leads

theorem Fml.Leads.valid {φ ψ : Fml C []} (h : Fml.Leads φ ψ) (hψ : Valid ψ) : Valid φ :=
  fun σ => h σ (hψ σ)

/-- `φ ~~> L` past the program: `φ` leads to the last scoped line `Z`, and
`Z`'s erasure, its parameters free, to `L` (`Update.lean`'s `~~>`). -/
def Fml.LeadsE (φ Z : Fml C []) (L : Solidity.NFml C) : Prop :=
  Fml.Leads φ Z ∧ Solidity.NFml.Leads ((Z.erase []).dropAlls) L

/-- A chain past the program, as `~~>`. -/
theorem Fml.ViaE.leads {φ : Fml C []} {ws : List (Link C × Fml C [])} {L : Solidity.NFml C}
    {rs : List (NFml.Link C × Solidity.NFml C)} (v : Fml.ViaE φ ws L rs) :
    Fml.LeadsE φ (Fml.Via.last φ ws) (Solidity.NFml.Via.last L rs) := by
  obtain ⟨h₁, rfl, h₃⟩ := v
  exact ⟨h₁.leads, Solidity.NFml.Via.leads h₃⟩

/-- A scoped segment, then one past the program. -/
theorem Fml.Leads.viaE {φ ψ : Fml C []} {ws : List (Link C × Fml C [])} {L : Solidity.NFml C}
    {rs : List (NFml.Link C × Solidity.NFml C)} (h : Fml.Leads φ ψ) (v : Fml.ViaE ψ ws L rs) :
    Fml.LeadsE φ (Fml.Via.last ψ ws) (Solidity.NFml.Via.last L rs) := by
  obtain ⟨h₁, rfl, h₃⟩ := v
  exact ⟨h.comp h₁.leads, Solidity.NFml.Via.leads h₃⟩

/-- Past the program, a segment of `Update.lean`'s rewrites. -/
theorem Fml.LeadsE.via {φ Z : Fml C []} {L : Solidity.NFml C}
    {rs : List (NFml.Link C × Solidity.NFml C)} (h : Fml.LeadsE φ Z L) (v : Solidity.NFml.Via L rs) :
    Fml.LeadsE φ Z (Solidity.NFml.Via.last L rs) :=
  ⟨h.1, Solidity.NFml.Leads.comp h.2 (Solidity.NFml.Via.leads v)⟩

/-- Past the program, a segment written from a line with no program left
(its erasure `L`, the line the chain so far ends at). -/
theorem Fml.LeadsE.viaE {φ Z B : Fml C []} {L : Solidity.NFml C}
    {rs : List (NFml.Link C × Solidity.NFml C)} (h : Fml.LeadsE φ Z L) (v : Fml.ViaE B [] L rs) :
    Fml.LeadsE φ Z (Solidity.NFml.Via.last L rs) :=
  h.via v.2.2

/-- **`~~>` past the program is a proof**, given the bridge at its last
scoped line (`Fml.ViaE.valid`'s). -/
theorem Fml.LeadsE.valid {φ Z : Fml C []} {L : Solidity.NFml C} (h : Fml.LeadsE φ Z L)
    (bridge : (∀ τ, NFml.holds τ (Z.erase [])) → Valid Z) (hL : ∀ τ, NFml.holds τ L) :
    Valid φ :=
  h.1.valid (bridge (Solidity.NFml.holds_of_dropAlls _ (fun τ => h.2 τ (hL τ))))

/-- `~~>` past the program, the bridge `Proves.close` at its last scoped line
(`Fml.ViaE.valid_close`'s). -/
theorem Fml.LeadsE.valid_close {φ Z : Fml C []} {L : Solidity.NFml C} (h : Fml.LeadsE φ Z L)
    (hL : ∀ τ, NFml.holds τ L) (hc : Z.closableB [] = true := by first | rfl | decide) :
    Valid φ :=
  h.valid (fun he => Proves.valid (R := .all) (Proves.close (Γ₀ := []) (H := .nil) [] rfl
    List.nodup_nil he hc fun _ _ h => nomatch h)) hL

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
