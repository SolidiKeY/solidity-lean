import Solidity.Calculus.MemSwap

/-!
# Value binders moved out past fresh arrays (M7, plan step 6)

The fresh arrays' cut (`Calculus/MemSwap.lean`) reads each read of a fresh
array at the binder, so an index must be bound before its array.  A leaf
`∀ fresh s. len(s) > 0 → ∀ i. i < len(s) → s[i] == 0` binds `i` after
`s`; read as `∀ i. ∀ fresh s. len(s) > 0 → i < len(s) → s[i] == 0` it does
not.  The two read alike at every state: a universal binder moves out of an
implication's consequent whose antecedent does not mention it, out of a
conjunct, and past a fresh object's binder, whose objects do not depend on
the value (`Fml.hoist`, `Fml.hoist_holds`).  So does every other pair of
universal binders, at either polarity: these are equivalences, not
polarity-sensitive steps.

The binders trade places by a renaming of the locals (`Ren`, `Tm.ren`,
`Fml.ren?`), read in the state whose locals are pulled back along it
(`State.pull`, `Tm.eval_ren`, `Tm.denote_ren`, `Fml.holds_ren`).
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Renamings -/

/-- **A renaming of locals**: each of `Γ`'s to one of `Δ`'s, at its type. -/
structure Ren (Γ Δ : Ctx) where
  f : {t : LTy} → Idx Γ t → Idx Δ t

/-- Under one more binder. -/
def Ren.lift {Γ Δ : Ctx} (r : Ren Γ Δ) (u : LTy) : Ren (u :: Γ) (u :: Δ) where
  f := fun {_} i => match i with
    | .here => .here
    | .there j => .there (r.f j)

/-- Past the innermost local. -/
def Ren.tail {Γ Δ : Ctx} {u : LTy} (r : Ren (u :: Γ) Δ) : Ren Γ Δ := ⟨fun j => r.f (.there j)⟩

/-- Every local, one binder further out. -/
def Ren.up {Γ : Ctx} (u : LTy) : Ren Γ (u :: Γ) := ⟨fun j => .there j⟩

/-- The identity. -/
def Ren.id (Γ : Ctx) : Ren Γ Γ := ⟨fun j => j⟩

/-- The two innermost locals swapped. -/
def Ren.swap (a b : LTy) (Γ : Ctx) : Ren (a :: b :: Γ) (b :: a :: Γ) where
  f := fun {_} i => match i with
    | .here => .there .here
    | .there .here => .here
    | .there (.there j) => .there (.there j)

/-- The locals pulled back along a renaming. -/
def TEnv.pull {H : HTy} : {Γ Δ : Ctx} → Ren Γ Δ → TEnv C H Δ → TEnv C H Γ
  | [], _, _, _ => ()
  | _ :: _, _, r, e => (TEnv.get (r.f .here) e, TEnv.pull r.tail e)

theorem TEnv.get_pull {H : HTy} : {Γ Δ : Ctx} → (r : Ren Γ Δ) → (e : TEnv C H Δ) → {t : LTy} →
    (i : Idx Γ t) → TEnv.get i (TEnv.pull r e) = TEnv.get (r.f i) e
  | _ :: _, _, _, _, _, .here => rfl
  | _ :: _, _, r, e, _, .there i => TEnv.get_pull r.tail e i

theorem TEnv.pull_there {H : HTy} {u : LTy} : {Γ Δ : Ctx} → (r : Ren Γ Δ) → (v : u.TDenote C H) →
    (e : TEnv C H Δ) → TEnv.pull (Δ := u :: Δ) ⟨fun j => .there (r.f j)⟩ (v, e) = TEnv.pull r e
  | [], _, _, _, _ => rfl
  | _ :: _, _, r, v, e => by
    show (TEnv.get (r.f .here) e, TEnv.pull (Δ := u :: _) ⟨fun j => .there (r.tail.f j)⟩ (v, e)) = _
    rw [TEnv.pull_there r.tail v e]
    rfl

theorem TEnv.pull_id {H : HTy} : {Γ : Ctx} → (e : TEnv C H Γ) → TEnv.pull (Ren.id Γ) e = e
  | [], () => rfl
  | _ :: _, (x, e) => by
    show (x, TEnv.pull (Δ := _ :: _) ⟨fun j => .there ((Ren.id _).f j)⟩ (x, e)) = _
    rw [TEnv.pull_there (Ren.id _) x e, TEnv.pull_id e]

theorem TEnv.pull_wk {H H' : HTy} (ext : H <+: H') : {Γ Δ : Ctx} → (r : Ren Γ Δ) → (e : TEnv C H Δ) →
    TEnv.pull r (TEnv.wk ext Δ e) = TEnv.wk ext Γ (TEnv.pull r e)
  | [], _, _, _ => rfl
  | _ :: _, _, r, e => by
    show (TEnv.get (r.f .here) (TEnv.wk ext _ e), TEnv.pull r.tail (TEnv.wk ext _ e)) = _
    rw [TEnv.get_wk, TEnv.pull_wk ext r.tail e]
    rfl

/-- **A state read along a renaming**: its locals pulled back. -/
def _root_.Solidity.State.pull {Γ Δ : Ctx} (r : Ren Γ Δ) (σ : State C Δ) : State C Γ := σ.withEnv (TEnv.pull r σ.env)

/-! ## Terms -/

/-- **A term, its locals renamed.** -/
def _root_.Solidity.Tm.ren {Γ Δ : Ctx} (r : Ren Γ Δ) : {s : Srt} → Tm C Γ s → Tm C Δ s
  | _, .pvV i => .pvV (r.f i)
  | _, .pvP i => .pvP (r.f i)
  | _, .pvS i => .pvS (r.f i)
  | _, .pvI i => .pvI (r.f i)
  | _, .netOf i a => .netOf (r.f i) (a.ren r)
  | _, .app0 o => .app0 o
  | _, .app1 o a => .app1 o (a.ren r)
  | _, .app2 o a b => .app2 o (a.ren r) (b.ren r)
  | _, .app3 o a b c => .app3 o (a.ren r) (b.ren r) (c.ren r)
  | _, .pvZ i => .pvZ (r.f i)

theorem _root_.Solidity.Tm.eval_ren {Γ Δ : Ctx} (r : Ren Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.ren r).eval σ = t.eval (σ.pull r)
  | _, .pvV i => by
    show some (TEnv.get (r.f i) σ.env) = some (TEnv.get i (TEnv.pull r σ.env))
    rw [TEnv.get_pull]
  | _, .pvP i => by
    show TEnv.get (r.f i) σ.env = TEnv.get i (TEnv.pull r σ.env)
    rw [TEnv.get_pull]
  | _, .pvS i => by
    show some (TEnv.get (r.f i) σ.env) = some (TEnv.get i (TEnv.pull r σ.env))
    rw [TEnv.get_pull]
  | _, .pvI i => by
    show (TEnv.get (r.f i) σ.env).map (·.id) = (TEnv.get i (TEnv.pull r σ.env)).map (·.id)
    rw [TEnv.get_pull]
  | _, .netOf i a => by
    show ((a.ren r).eval σ).bind _ = (a.eval (σ.pull r)).bind (Tm.netOfT (TEnv.get i (TEnv.pull r σ.env)))
    rw [Tm.eval_ren r σ a, TEnv.get_pull]
  | _, .app0 o => rfl
  | _, .app1 o a => by
    show o.eval σ.glob ((a.ren r).eval σ) = o.eval σ.glob (a.eval (σ.pull r))
    rw [Tm.eval_ren r σ a]
  | _, .app2 o a b => by
    show o.eval σ.glob ((a.ren r).eval σ) ((b.ren r).eval σ) =
      o.eval σ.glob (a.eval (σ.pull r)) (b.eval (σ.pull r))
    rw [Tm.eval_ren r σ a, Tm.eval_ren r σ b]
  | _, .app3 o a b c => by
    show o.eval σ.glob ((a.ren r).eval σ) ((b.ren r).eval σ) ((c.ren r).eval σ) =
      o.eval σ.glob (a.eval (σ.pull r)) (b.eval (σ.pull r)) (c.eval (σ.pull r))
    rw [Tm.eval_ren r σ a, Tm.eval_ren r σ b, Tm.eval_ren r σ c]
  | _, .pvZ i => by
    show some (TEnv.get (r.f i) σ.env) = some (TEnv.get i (TEnv.pull r σ.env))
    rw [TEnv.get_pull]

theorem _root_.Solidity.Tm.denote_ren {Γ Δ : Ctx} (r : Ren Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.ren r).denote σ = t.denote (σ.pull r)
  | _, .pvV i => by
    show some (TEnv.get (r.f i) σ.env) = some (TEnv.get i (TEnv.pull r σ.env))
    rw [TEnv.get_pull]
  | _, .pvP i => by
    show Tm.denote σ (.pvP (r.f i)) = Tm.denote (σ.pull r) (.pvP i)
    simp only [Tm.denote, State.pull, State.withEnv, TEnv.get_pull]
    split <;> rfl
  | _, .pvS i => by
    show Tm.denote σ (.pvS (r.f i)) = Tm.denote (σ.pull r) (.pvS i)
    simp only [Tm.denote, State.pull, State.withEnv, TEnv.get_pull]
  | _, .pvI _ => rfl
  | _, .netOf i a => by
    show ((a.ren r).denote σ).map _ = (a.denote (σ.pull r)).map _
    rw [Tm.denote_ren r σ a]
    simp only [State.pull, State.withEnv, TEnv.get_pull]
  | _, .app0 o => rfl
  | _, .app1 o a => by
    show o.denote σ.glob ((a.ren r).denote σ) = o.denote σ.glob (a.denote (σ.pull r))
    rw [Tm.denote_ren r σ a]
  | _, .app2 o a b => by
    show o.denote σ.glob ((a.ren r).eval σ) ((b.ren r).eval σ) ((a.ren r).denote σ) ((b.ren r).denote σ) =
      o.denote σ.glob (a.eval (σ.pull r)) (b.eval (σ.pull r)) (a.denote (σ.pull r))
        (b.denote (σ.pull r))
    rw [Tm.denote_ren r σ a, Tm.denote_ren r σ b, Tm.eval_ren r σ a, Tm.eval_ren r σ b]
  | _, .app3 o a b c => by
    show o.denote ((a.ren r).denote σ) ((b.ren r).denote σ) ((c.ren r).denote σ) =
      o.denote (a.denote (σ.pull r)) (b.denote (σ.pull r)) (c.denote (σ.pull r))
    rw [Tm.denote_ren r σ a, Tm.denote_ren r σ b, Tm.denote_ren r σ c]
  | _, .pvZ i => by
    show some (TEnv.get (r.f i) σ.env) = some (TEnv.get i (TEnv.pull r σ.env))
    rw [TEnv.get_pull]

/-! ## Formulas -/

/-- **A formula of the fresh arrays' fragment, its locals renamed**
(`none` outside it). -/
def _root_.Solidity.Fml.ren? : {Γ Δ : Ctx} → Ren Γ Δ → Fml C Γ → Option (Fml C Δ)
  | _, _, _, .tt => some .tt
  | _, _, r, .eq a b => some (.eq (a.ren r) (b.ren r))
  | _, _, r, .not φ => (Fml.ren? r φ).map .not
  | _, _, r, .and φ ψ => (Fml.ren? r φ).bind fun φ' => (Fml.ren? r ψ).map fun ψ' => .and φ' ψ'
  | _, _, r, .imp φ ψ => (Fml.ren? r φ).bind fun φ' => (Fml.ren? r ψ).map fun ψ' => .imp φ' ψ'
  | _, _, r, .all x p φ => (Fml.ren? (r.lift _) φ).map (.all x p)
  | _, _, r, .allocAll x R φ => (Fml.ren? (r.lift _) φ).map (.allocAll x R)
  | _, _, _, _ => none

theorem _root_.Solidity.State.pull_push {Γ Δ : Ctx} (r : Ren Γ Δ) (σ : State C Δ) {u : LTy} (v : u.TDenote C σ.H) :
    (σ.push v).pull (r.lift u) = (σ.pull r).push (t := u) v := by
  show State.withEnv (Δ := u :: Γ) (σ.push v) (v, TEnv.pull (Δ := u :: Δ) ⟨fun j => .there (r.f j)⟩ (v, σ.env)) = _
  rw [TEnv.pull_there r v σ.env]
  rfl

theorem _root_.Solidity.State.pull_allocPush {Γ Δ : Ctx} (r : Ren Γ Δ) (σ : State C Δ) {R : RefTy} (o : MObj σ.H R) :
    (σ.allocPush o).pull (r.lift (.mem R)) = (σ.pull r).allocPush o := by
  show State.withEnv (Δ := .mem R :: Γ) (σ.allocPush o) (some (σ.alloc o).2,
    TEnv.pull (Δ := .mem R :: Δ) ⟨fun j => .there (r.f j)⟩
      (some (σ.alloc o).2, TEnv.wk (List.prefix_append σ.H [R]) Δ σ.env)) = _
  rw [TEnv.pull_there r, TEnv.pull_wk]
  rfl

/-- **A renamed formula holds where the formula does in the pulled-back
state.** -/
theorem _root_.Solidity.Fml.holds_ren {Γ : Ctx} (φ : Fml C Γ) : {Δ : Ctx} → (r : Ren Γ Δ) → {ψ : Fml C Δ} →
    φ.ren? r = some ψ → ∀ σ : State C Δ, holds σ ψ ↔ holds (σ.pull r) φ := by
  induction φ with
  | tt => intro _ _ _ e _; cases e; exact Iff.rfl
  | eq a b =>
    intro _ r _ e σ
    cases e
    show (a.ren r).denote σ = (b.ren r).denote σ ↔ a.denote (σ.pull r) = b.denote (σ.pull r)
    rw [Tm.denote_ren, Tm.denote_ren]
  | not φ ih =>
    intro _ r _ e σ
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih r hφ σ)
  | and φ ψ ihφ ihψ =>
    intro _ r _ e σ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ r hφ σ) (ihψ r hψ σ)
  | imp φ ψ ihφ ihψ =>
    intro _ r _ e σ
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ r hφ σ) (ihψ r hψ σ)
  | all x p φ ih =>
    intro _ r _ e σ
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    show (∀ v : p.Denote, holds (σ.push (t := .val p) v) φ') ↔
      ∀ v : p.Denote, holds ((σ.pull r).push (t := .val p) v) φ
    exact forall_congr' fun v => (ih (r.lift _) hφ _).trans (by rw [State.pull_push])
  | allocAll x R φ ih =>
    intro _ r _ e σ
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    show (∀ o : MObj σ.H R, holds (σ.allocPush o) φ') ↔ ∀ o : MObj σ.H R, holds ((σ.pull r).allocPush o) φ
    exact forall_congr' fun o => (ih (r.lift _) hφ _).trans (by rw [State.pull_allocPush])
  | wellFormed | upd | modal | havoc | bind | anon | grow =>
    intro _ _ _ e; cases e

/-! ## Binders moved out -/

/-- `A → ∀ y. B` as `∀ y. A → B`, as long as the consequent starts with a
binder and the antecedent renames. -/
def _root_.Solidity.Fml.hoistImp : Nat → {Γ : Ctx} → Fml C Γ → Fml C Γ → Fml C Γ
  | n + 1, _, A, .all y p B =>
    match A.ren? (Ren.up (.val p)) with
    | some A' => .all y p (Fml.hoistImp n A' B)
    | none => .imp A (.all y p B)
  | _, _, A, B => .imp A B

/-- `A ∧ ∀ y. B` as `∀ y. A ∧ B`. -/
def _root_.Solidity.Fml.hoistAndR : Nat → {Γ : Ctx} → Fml C Γ → Fml C Γ → Fml C Γ
  | n + 1, _, A, .all y p B =>
    match A.ren? (Ren.up (.val p)) with
    | some A' => .all y p (Fml.hoistAndR n A' B)
    | none => .and A (.all y p B)
  | _, _, A, B => .and A B

/-- `(∀ y. A) ∧ B` as `∀ y. A ∧ B`, then `A ∧ ∀ y. B`. -/
def _root_.Solidity.Fml.hoistAnd : Nat → {Γ : Ctx} → Fml C Γ → Fml C Γ → Fml C Γ
  | n + 1, _, .all y p A, B =>
    match B.ren? (Ren.up (.val p)) with
    | some B' => .all y p (Fml.hoistAnd n A B')
    | none => Fml.hoistAndR n (.all y p A) B
  | n, _, A, B => Fml.hoistAndR n A B

/-- `∀ fresh x. ∀ y. B` as `∀ y. ∀ fresh x. B`. -/
def _root_.Solidity.Fml.hoistAlloc : Nat → {Γ : Ctx} → Var → (R : RefTy) → Fml C (.mem R :: Γ) → Fml C Γ
  | n + 1, _, x, R, .all y p B =>
    match B.ren? (Ren.swap (.val p) (.mem R) _) with
    | some B' => .all y p (Fml.hoistAlloc n x R B')
    | none => .allocAll x R (.all y p B)
  | _, _, x, R, B => .allocAll x R B

/-- **Universal value binders moved out** of consequents, conjuncts and
fresh objects' binders, bottom up. -/
def _root_.Solidity.Fml.hoist : Nat → {Γ : Ctx} → Fml C Γ → Fml C Γ
  | n + 1, _, .not φ => .not (Fml.hoist n φ)
  | n + 1, _, .and φ ψ => Fml.hoistAnd n (Fml.hoist n φ) (Fml.hoist n ψ)
  | n + 1, _, .imp φ ψ => Fml.hoistImp n (Fml.hoist n φ) (Fml.hoist n ψ)
  | n + 1, _, .all x p φ => .all x p (Fml.hoist n φ)
  | n + 1, _, .allocAll x R φ => Fml.hoistAlloc n x R (Fml.hoist n φ)
  | _, _, φ => φ

theorem _root_.Solidity.State.pull_up_push {Γ : Ctx} (σ : State C Γ) {u : LTy} (v : u.TDenote C σ.H) :
    (σ.push v).pull (Ren.up u) = σ := by
  show State.withEnv _ (TEnv.pull (Δ := u :: Γ) ⟨fun j => .there ((Ren.id Γ).f j)⟩ (v, σ.env)) = σ
  rw [TEnv.pull_there (Ren.id Γ) v σ.env, TEnv.pull_id]
  rfl

theorem _root_.Solidity.Fml.hoistImp_holds : (n : Nat) → {Γ : Ctx} → (A B : Fml C Γ) → (σ : State C Γ) →
    (holds σ (Fml.hoistImp n A B) ↔ holds σ (.imp A B))
  | n + 1, Γ, A, .all y p B, σ => by
    unfold Fml.hoistImp
    split
    · rename_i A' hA
      show (∀ v : p.Denote, holds (σ.push (t := .val p) v) (Fml.hoistImp n A' B)) ↔
        (holds σ A → ∀ v : p.Denote, holds (σ.push (t := .val p) v) B)
      have hA' : ∀ v : p.Denote, holds (σ.push (t := .val p) v) A' ↔ holds σ A := fun v => by
        rw [Fml.holds_ren A _ hA, State.pull_up_push]
      constructor
      · intro h ha v
        exact ((Fml.hoistImp_holds n A' B _).1 (h v)) ((hA' v).2 ha)
      · intro h v
        exact (Fml.hoistImp_holds n A' B _).2 fun ha => h ((hA' v).1 ha) v
    · exact Iff.rfl
  | 0, _, _, _, _ => Iff.rfl
  | _ + 1, _, _, .tt, _ | _ + 1, _, _, .eq .., _ | _ + 1, _, _, .wellFormed _, _
  | _ + 1, _, _, .not _, _ | _ + 1, _, _, .and .., _ | _ + 1, _, _, .imp .., _
  | _ + 1, _, _, .upd .., _ | _ + 1, _, _, .modal .., _ | _ + 1, _, _, .havoc _, _
  | _ + 1, _, _, .bind .., _ | _ + 1, _, _, .anon .., _ | _ + 1, _, _, .allocAll .., _
  | _ + 1, _, _, .grow _, _ => Iff.rfl

theorem _root_.Solidity.Fml.hoistAndR_holds : (n : Nat) → {Γ : Ctx} → (A B : Fml C Γ) → (σ : State C Γ) →
    (holds σ (Fml.hoistAndR n A B) ↔ holds σ (.and A B))
  | n + 1, Γ, A, .all y p B, σ => by
    unfold Fml.hoistAndR
    split
    · rename_i A' hA
      show (∀ v : p.Denote, holds (σ.push (t := .val p) v) (Fml.hoistAndR n A' B)) ↔
        (holds σ A ∧ ∀ v : p.Denote, holds (σ.push (t := .val p) v) B)
      have hA' : ∀ v : p.Denote, holds (σ.push (t := .val p) v) A' ↔ holds σ A := fun v => by
        rw [Fml.holds_ren A _ hA, State.pull_up_push]
      constructor
      · intro h
        refine ⟨?_, fun v => ((Fml.hoistAndR_holds n A' B _).1 (h v)).2⟩
        exact (hA' (PrimTy.dflt p)).1 ((Fml.hoistAndR_holds n A' B _).1 (h _)).1
      · intro h v
        exact (Fml.hoistAndR_holds n A' B _).2 ⟨(hA' v).2 h.1, h.2 v⟩
    · exact Iff.rfl
  | 0, _, _, _, _ => Iff.rfl
  | _ + 1, _, _, .tt, _ | _ + 1, _, _, .eq .., _ | _ + 1, _, _, .wellFormed _, _
  | _ + 1, _, _, .not _, _ | _ + 1, _, _, .and .., _ | _ + 1, _, _, .imp .., _
  | _ + 1, _, _, .upd .., _ | _ + 1, _, _, .modal .., _ | _ + 1, _, _, .havoc _, _
  | _ + 1, _, _, .bind .., _ | _ + 1, _, _, .anon .., _ | _ + 1, _, _, .allocAll .., _
  | _ + 1, _, _, .grow _, _ => Iff.rfl

theorem _root_.Solidity.Fml.hoistAnd_holds : (n : Nat) → {Γ : Ctx} → (A B : Fml C Γ) → (σ : State C Γ) →
    (holds σ (Fml.hoistAnd n A B) ↔ holds σ (.and A B))
  | n + 1, Γ, .all y p A, B, σ => by
    unfold Fml.hoistAnd
    split
    · rename_i B' hB
      show (∀ v : p.Denote, holds (σ.push (t := .val p) v) (Fml.hoistAnd n A B')) ↔
        ((∀ v : p.Denote, holds (σ.push (t := .val p) v) A) ∧ holds σ B)
      have hB' : ∀ v : p.Denote, holds (σ.push (t := .val p) v) B' ↔ holds σ B := fun v => by
        rw [Fml.holds_ren B _ hB, State.pull_up_push]
      constructor
      · intro h
        refine ⟨fun v => ((Fml.hoistAnd_holds n A B' _).1 (h v)).1, ?_⟩
        exact (hB' (PrimTy.dflt p)).1 ((Fml.hoistAnd_holds n A B' _).1 (h _)).2
      · intro h v
        exact (Fml.hoistAnd_holds n A B' _).2 ⟨h.1 v, (hB' v).2 h.2⟩
    · exact Fml.hoistAndR_holds n _ B σ
  | 0, _, A, B, σ => Fml.hoistAndR_holds 0 A B σ
  | n + 1, _, .tt, B, σ | n + 1, _, .eq .., B, σ | n + 1, _, .wellFormed _, B, σ
  | n + 1, _, .not _, B, σ | n + 1, _, .and .., B, σ | n + 1, _, .imp .., B, σ
  | n + 1, _, .upd .., B, σ | n + 1, _, .modal .., B, σ | n + 1, _, .havoc _, B, σ
  | n + 1, _, .bind .., B, σ | n + 1, _, .anon .., B, σ | n + 1, _, .allocAll .., B, σ
  | n + 1, _, .grow _, B, σ => Fml.hoistAndR_holds (n + 1) _ B σ

theorem _root_.Solidity.State.pull_swap {Γ : Ctx} (σ : State C Γ) {p : PrimTy} {R : RefTy} (v : p.Denote)
    (o : MObj σ.H R) :
    ((σ.push (t := .val p) v).allocPush o).pull (Ren.swap (.val p) (.mem R) Γ) =
      (σ.allocPush o).push (t := .val p) v := by
  have h : TEnv.pull (Δ := .mem R :: .val p :: Γ)
      ⟨fun j => .there (.there ((Ren.id Γ).f j))⟩
      (some (σ.alloc o).2, (v, TEnv.wk (List.prefix_append σ.H [R]) Γ σ.env)) =
      TEnv.wk (List.prefix_append σ.H [R]) Γ σ.env := by
    exact (TEnv.pull_there (H := (σ.alloc o).1.H) (Δ := .val p :: Γ)
      ⟨fun j => .there ((Ren.id Γ).f j)⟩ _ _).trans
      ((TEnv.pull_there (Ren.id Γ) _ _).trans (TEnv.pull_id _))
  show State.withEnv (Δ := .val p :: .mem R :: Γ) ((σ.push (t := .val p) v).allocPush o) (v, (some (σ.alloc o).2, TEnv.pull (Δ := .mem R :: .val p :: Γ)
      ⟨fun j => .there (.there ((Ren.id Γ).f j))⟩
      (some (σ.alloc o).2, (v, TEnv.wk (List.prefix_append σ.H [R]) Γ σ.env)))) = _
  rw [h]
  rfl

theorem _root_.Solidity.Fml.hoistAlloc_holds : (n : Nat) → {Γ : Ctx} → (x : Var) → (R : RefTy) →
    (B : Fml C (.mem R :: Γ)) → (σ : State C Γ) →
    (holds σ (Fml.hoistAlloc n x R B) ↔ holds σ (.allocAll x R B))
  | n + 1, Γ, x, R, .all y p B, σ => by
    unfold Fml.hoistAlloc
    split
    · rename_i B' hB
      show (∀ v : p.Denote, holds (σ.push (t := .val p) v) (Fml.hoistAlloc n x R B')) ↔
        ∀ o : MObj σ.H R, ∀ v : p.Denote, holds ((σ.allocPush o).push (t := .val p) v) B
      have key : ∀ v : p.Denote, holds (σ.push (t := .val p) v) (Fml.hoistAlloc n x R B') ↔
          ∀ o : MObj σ.H R, holds ((σ.allocPush o).push (t := .val p) v) B := fun v => by
        rw [Fml.hoistAlloc_holds n x R B' _]
        show (∀ o : MObj σ.H R, holds ((σ.push (t := .val p) v).allocPush o) B') ↔ _
        exact forall_congr' fun o => by rw [Fml.holds_ren B _ hB, State.pull_swap]
      constructor
      · intro h o v
        exact (key v).1 (h v) o
      · intro h v
        exact (key v).2 fun o => h o v
    · exact Iff.rfl
  | 0, _, _, _, _, _ => Iff.rfl
  | _ + 1, _, _, _, .tt, _ | _ + 1, _, _, _, .eq .., _ | _ + 1, _, _, _, .wellFormed _, _
  | _ + 1, _, _, _, .not _, _ | _ + 1, _, _, _, .and .., _ | _ + 1, _, _, _, .imp .., _
  | _ + 1, _, _, _, .upd .., _ | _ + 1, _, _, _, .modal .., _ | _ + 1, _, _, _, .havoc _, _
  | _ + 1, _, _, _, .bind .., _ | _ + 1, _, _, _, .anon .., _ | _ + 1, _, _, _, .allocAll .., _
  | _ + 1, _, _, _, .grow _, _ => Iff.rfl

/-- **Moving binders out is exact at every state.** -/
theorem _root_.Solidity.Fml.hoist_holds : (n : Nat) → {Γ : Ctx} → (φ : Fml C Γ) → (σ : State C Γ) →
    (holds σ (Fml.hoist n φ) ↔ holds σ φ)
  | 0, _, _, _ => Iff.rfl
  | n + 1, _, φ, σ => by
    cases φ with
    | not φ => exact not_congr (Fml.hoist_holds n φ σ)
    | and φ ψ =>
      exact (Fml.hoistAnd_holds n _ _ σ).trans (and_congr (Fml.hoist_holds n φ σ) (Fml.hoist_holds n ψ σ))
    | imp φ ψ =>
      exact (Fml.hoistImp_holds n _ _ σ).trans (imp_congr (Fml.hoist_holds n φ σ) (Fml.hoist_holds n ψ σ))
    | all x p φ => exact forall_congr' fun v => Fml.hoist_holds n φ _
    | allocAll x R φ =>
      exact (Fml.hoistAlloc_holds n x R _ σ).trans (forall_congr' fun o => Fml.hoist_holds n φ _)
    | _ => exact Iff.rfl

end Solidity.Decide
