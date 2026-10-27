import Solidity.Calculus.LexVariant
import Solidity.Calculus.LowerRun
import Solidity.Semantics.LexMetrics

/-!
# Agreement of typed lexicographic snapshots

Every captured component must be defined. The comparison formula only reads
locals produced by successful snapshots; its total Theory interpretation
therefore cannot hide a reverting expression. Ordinary diamonds still accept
exhaustion; these lemmas alone do not construct a strict SourceCertificate.
-/
namespace Solidity.LoopLex

variable {C : Contract} {Γ Δ : Ctx}

def UIntTuple : Nat → Type
  | 0 => Unit
  | n + 1 => PrimTy.uint.Denote × UIntTuple n

def UIntTuple.toNat : {n : Nat} → UIntTuple n → LoopMetrics.NatTuple n
  | 0, _ => ()
  | _ + 1, xs => (xs.1.1.toNat, toNat xs.2)

def extendEnv {H : HTy} : {n : Nat} → UIntTuple n → TEnv C H Γ → TEnv C H (SavedCtx n Γ)
  | 0, _, ρ => ρ
  | _ + 1, xs, ρ => (xs.1, extendEnv xs.2 ρ)

def saveState (σ : State C Γ) {n : Nat} (xs : UIntTuple n) : State C (SavedCtx n Γ) :=
  { σ with env := extendEnv xs σ.env }

theorem saveState_cons (σ : State C Γ) {n : Nat} (x : PrimTy.uint.Denote) (xs : UIntTuple n) :
    saveState σ (n := n + 1) (x, xs) = (saveState σ xs).push (t := .val .uint) x := rfl

theorem drop_extendEnv {H : HTy} {n : Nat} (xs : UIntTuple n) (ρ : TEnv C H Γ) :
    TEnv.drop (savedExt Γ n) (extendEnv xs ρ) = ρ := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih xs.2

theorem saveState_drop (σ : State C Γ) {n : Nat} (xs : UIntTuple n) :
    (saveState σ xs).drop (savedExt Γ n) = σ := by
  cases σ
  simp only [saveState, State.drop, drop_extendEnv]

def readMetrics (σ : State C Γ) : {n : Nat} → LoopMetrics C Γ n → Option (UIntTuple n)
  | 0, .nil => some ()
  | _ + 1, .cons head tail => do
      let x ← head.lower.eval σ
      let xs ← readMetrics σ tail
      pure (x, xs)

private theorem lower_eval_iff (σ : State C Γ) (v : Val C Γ .uint)
    (x : PrimTy.uint.Denote) : v.lower.eval σ = some x ↔ v.evalT σ = .ok x := by
  have hagrees := Val.lower_evalT σ v
  constructor
  · intro h
    cases hv : v.evalT σ with
    | ok y =>
      rw [hv] at hagrees
      change v.lower.eval σ = some y at hagrees
      rw [h] at hagrees
      cases Option.some.inj hagrees
      rfl
    | error e =>
      have he := Val.evalT_revertOnly σ v e hv
      subst e
      rw [hv] at hagrees
      change v.lower.eval σ = none at hagrees
      rw [h] at hagrees
      cases hagrees
  · intro h
    rw [h] at hagrees
    exact hagrees

/-- Successful capture defines every source metric, at the original scope. -/
theorem eval_of_readMetrics (σ : State C Γ) {n : Nat} (metrics : LoopMetrics C Γ n)
    (xs : UIntTuple n) (h : readMetrics σ metrics = some xs) :
    LoopMetrics.eval σ metrics = .ok xs.toNat := by
  induction metrics with
  | nil => cases xs; rfl
  | cons head tail ih =>
    cases hx : head.lower.eval σ with
    | none => simp only [readMetrics, hx, bind, Option.bind, reduceCtorEq] at h
    | some x =>
      cases ht : readMetrics σ tail with
      | none => simp only [readMetrics, hx, ht, bind, Option.bind, reduceCtorEq] at h
      | some rest =>
        simp only [readMetrics, hx, ht, bind, Option.bind, pure, Pure.pure, Option.some.injEq] at h
        cases h
        have hv := (lower_eval_iff σ head x).1 hx
        have htail := ih rest ht
        change (head.evalT σ >>= fun v => LoopMetrics.eval σ tail >>= fun vs =>
          pure (v.1.toNat, vs)) = _
        rw [hv, htail]
        rfl

theorem readMetrics_of_eval (σ : State C Γ) {n : Nat} (metrics : LoopMetrics C Γ n)
    {values : LoopMetrics.NatTuple n} (h : LoopMetrics.eval σ metrics = .ok values) :
    ∃ xs, readMetrics σ metrics = some xs ∧ xs.toNat = values := by
  induction metrics with
  | nil => cases values; exact ⟨(), rfl, rfl⟩
  | cons head tail ih =>
    change (head.evalT σ >>= fun v => LoopMetrics.eval σ tail >>= fun vs =>
      pure (v.1.toNat, vs)) = .ok values at h
    cases hx : head.evalT σ with
    | error e => rw [hx] at h; cases h
    | ok x =>
      cases ht : LoopMetrics.eval σ tail with
      | error e => rw [hx, ht] at h; cases h
      | ok rest =>
        obtain ⟨xs, hxs, heq⟩ := ih ht
        have hv := (lower_eval_iff σ head x).2 hx
        refine ⟨(x, xs), ?_, ?_⟩
        · change (head.lower.eval σ).bind (fun v => (readMetrics σ tail).bind
            fun vs => some (v, vs)) = _
          rw [hv, hxs]
          rfl
        · rw [hx, ht] at h
          cases h
          exact congrArg (Prod.mk x.1.toNat) heq

theorem snapshot_globT (σ : State C Γ) (k : Nat) {n : Nat} (metrics : LoopMetrics C Γ n) :
    (snapshot k metrics).globT σ = (readMetrics σ metrics).map (fun _ => σ.globG) := by
  induction metrics generalizing k with
  | nil => rfl
  | cons head tail ih =>
    change ((snapshot (k + 1) tail).globT σ).bind
      (fun g => (head.lower.eval σ).bind fun _ => some g) = _
    rw [ih]
    change ((readMetrics σ tail).map (fun _ => σ.globG)).bind
      (fun g => (head.lower.eval σ).bind fun _ => some g) =
      ((head.lower.eval σ).bind fun x => (readMetrics σ tail).bind
        fun xs => some (x, xs)).map (fun _ => σ.globG)
    cases head.lower.eval σ <;> cases readMetrics σ tail <;> rfl

/-- Any successful snapshot globally preserves the input and defines all
source components. No component may be skipped after an early decrease. -/
theorem snapshot_defined (σ : State C Γ) (k : Nat) {n : Nat} (metrics : LoopMetrics C Γ n)
    {g : GlobT C σ.H} (h : (snapshot k metrics).globT σ = some g) :
    g = σ.globG ∧ ∃ xs, readMetrics σ metrics = some xs ∧
      LoopMetrics.eval σ metrics = .ok xs.toNat := by
  rw [snapshot_globT] at h
  cases hx : readMetrics σ metrics with
  | none => rw [hx] at h; cases h
  | some xs =>
    rw [hx] at h
    exact ⟨(Option.some.inj h).symm, xs, rfl, eval_of_readMetrics σ metrics xs hx⟩

theorem snapshot_globT_iff_eval (σ : State C Γ) (k : Nat) {n : Nat}
    (metrics : LoopMetrics C Γ n) :
    (snapshot k metrics).globT σ = some σ.globG ↔
      ∃ values, LoopMetrics.eval σ metrics = .ok values := by
  constructor
  · intro h
    obtain ⟨_, xs, _, heval⟩ := snapshot_defined σ k metrics h
    exact ⟨xs.toNat, heval⟩
  · rintro ⟨values, h⟩
    obtain ⟨xs, hx, _⟩ := readMetrics_of_eval σ metrics h
    rw [snapshot_globT, hx]
    rfl

theorem snapshot_fails_of_undefined (σ : State C Γ) (k : Nat) {n : Nat}
    (metrics : LoopMetrics C Γ n) {e : THalt}
    (h : LoopMetrics.eval σ metrics = .error e) : (snapshot k metrics).globT σ = none := by
  cases hg : (snapshot k metrics).globT σ with
  | none => rfl
  | some g =>
    obtain ⟨_, xs, _, heval⟩ := snapshot_defined σ k metrics hg
    rw [h] at heval
    cases heval

theorem metrics_eval_wk (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {n : Nat} (metrics : LoopMetrics C Γ n) :
    LoopMetrics.eval (σ.lift h d) (metrics.wk h) = LoopMetrics.eval σ metrics := by
  induction metrics with
  | nil => rfl
  | cons head tail ih =>
    simp only [LoopMetrics.wk, LoopMetrics.eval, Val.evalT_wk, ih]

theorem snapshot_pushFree (k : Nat) {n : Nat} (metrics : LoopMetrics C Γ n) :
    (snapshot k metrics).pushFree = true := by
  induction metrics generalizing k with
  | nil => rfl
  | cons head tail ih =>
    simp only [snapshot, Upd.pushFree, Rhs.pushFree, ih, Val.lower_pushFree, Bool.and_self]

theorem snapshot_exh (σ : State C Γ) (k : Nat) {n : Nat} (metrics : LoopMetrics C Γ n) :
    (snapshot k metrics).exh σ = false :=
  Upd.exh_of_pushFree (snapshot_pushFree k metrics)

theorem snapshot_lands (σ : State C Γ) (k : Nat) {n : Nat} (metrics : LoopMetrics C Γ n)
    (xs : UIntTuple n) (h : readMetrics σ metrics = some xs) :
    (snapshot k metrics).Lands σ σ.globG (saveState σ xs) := by
  induction metrics generalizing k with
  | nil => cases xs; exact Upd.lands_nil σ
  | cons head tail ih =>
    cases hx : head.lower.eval σ with
    | none => simp only [readMetrics, hx, bind, Option.bind, reduceCtorEq] at h
    | some x =>
      cases ht : readMetrics σ tail with
      | none => simp only [readMetrics, hx, ht, bind, Option.bind, reduceCtorEq] at h
      | some rest =>
        simp only [readMetrics, hx, ht, bind, Option.bind, pure, Pure.pure, Option.some.injEq] at h
        cases h
        exact Upd.lands_decl (ih (k + 1) rest ht) _ hx

/-- Every successful landing is the canonical saved state. -/
theorem snapshot_lands_eq (σ : State C Γ) (k : Nat) {n : Nat}
    (metrics : LoopMetrics C Γ n) {g : GlobT C σ.H} {τ : State C (SavedCtx n Γ)}
    (h : (snapshot k metrics).Lands σ g τ) :
    ∃ xs, readMetrics σ metrics = some xs ∧ τ = saveState σ xs := by
  obtain ⟨_, xs, hx, _⟩ := snapshot_defined σ k metrics h.1
  exact ⟨xs, hx, h.eq (snapshot_lands σ k metrics xs hx)⟩

def Refs.read (ρ : TEnv C H Γ) : {n : Nat} → Refs Γ n → UIntTuple n
  | 0, .nil => ()
  | _ + 1, .cons head tail => (TEnv.get head ρ, tail.read ρ)

theorem Refs.read_wk (h : Thin Γ Δ) (ρ : TEnv C H Γ) (d : TEnv C H Δ)
    {n : Nat} (refs : Refs Γ n) :
    (refs.wk h).read (TEnv.put h ρ d) = refs.read ρ := by
  induction refs with
  | nil => rfl
  | cons head tail ih => simp only [Refs.wk, Refs.read, TEnv.get_put, ih]

theorem freshRefs_read {n : Nat} (xs : UIntTuple n) (ρ : TEnv C H Γ) :
    (freshRefs Γ n).read (extendEnv xs ρ) = xs := by
  induction n with
  | zero => cases xs; rfl
  | succ n ih =>
    change (xs.1, ((freshRefs Γ n).wk (.drop .refl)).read
      (C := C) (H := H) (Γ := .val .uint :: SavedCtx n Γ) (xs.1, extendEnv xs.2 ρ)) = xs
    have h := Refs.read_wk (.drop (t := .val .uint) .refl)
      (extendEnv xs.2 ρ) (xs.1, extendEnv xs.2 ρ) (freshRefs Γ n)
    change ((freshRefs Γ n).wk (.drop .refl)).read
      (C := C) (H := H) (Γ := .val .uint :: SavedCtx n Γ) (xs.1, extendEnv xs.2 ρ) = _ at h
    rw [h, ih xs.2]
    cases xs; rfl

theorem put_extendEnv {n : Nat} (xs : UIntTuple n) (ρ : TEnv C H Γ) :
    TEnv.put (.ofExt (savedExt Γ n)) ρ (extendEnv xs ρ) = extendEnv xs ρ := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (Prod.mk xs.1) (ih xs.2)

theorem saveState_eq_lift (σ : State C Γ) {n : Nat} (xs : UIntTuple n) :
    σ.lift (.ofExt (savedExt Γ n)) (extendEnv xs σ.env) = saveState σ xs := by
  unfold State.lift State.withEnv saveState
  rw [put_extendEnv]

/-- Ghost snapshots do not change how the original scoped metrics evaluate. -/
theorem metrics_eval_saved (σ : State C Γ) {n m : Nat} (metrics : LoopMetrics C Γ n)
    (xs : UIntTuple m) :
    LoopMetrics.eval (saveState σ xs) (metrics.wk (.ofExt (savedExt Γ m))) =
      LoopMetrics.eval σ metrics := by
  rw [← saveState_eq_lift]
  exact metrics_eval_wk _ σ _ metrics

theorem Refs.read_saved (refs : Refs Γ n) {m : Nat} (xs : UIntTuple m)
    (ρ : TEnv C H Γ) :
    (refs.wk (.ofExt (savedExt Γ m))).read (extendEnv xs ρ) = refs.read ρ := by
  have h := refs.read_wk (.ofExt (savedExt Γ m)) ρ (extendEnv xs ρ)
  rw [put_extendEnv] at h
  exact h

private theorem uint_toNat_lt (x y : PrimTy.uint.Denote) :
    x.1 < y.1 ↔ x.1.toNat < y.1.toNat := by
  have hx := PrimTy.uint_nonneg x
  have hy := PrimTy.uint_nonneg y
  omega

private theorem uint_toNat_eq (x y : PrimTy.uint.Denote) :
    x = y ↔ x.1.toNat = y.1.toNat := by
  constructor
  · intro h; rw [h]
  · intro h
    apply Subtype.ext
    have hx := PrimTy.uint_nonneg x
    have hy := PrimTy.uint_nonneg y
    omega

/-- The generated formula is exactly the well-founded natural tuple order. -/
theorem lexFml_holds (σ : State C Γ) {n : Nat} (a b : Refs Γ n) :
    holds σ (lexFml a b) ↔
      LoopMetrics.NatTuple.Lt (a.read σ.env).toNat (b.read σ.env).toNat := by
  induction a with
  | nil => cases b; simp only [lexFml, holds, LoopMetrics.NatTuple.Lt, not_true_eq_false]
  | cons x xs ih =>
    cases b with
    | cons y ys =>
      have hlt :
          (Tm.app2 (C := C) (.binop .lt rfl) (.pvV x) (.pvV y)).eval σ =
            some (decide ((TEnv.get x σ.env).1 < (TEnv.get y σ.env).1)) := rfl
      have heq := holds_eq_of_eval (C := C) (σ := σ)
        (a := Tm.pvV x) (b := Tm.pvV y) rfl rfl
      change (¬ (¬ holds σ (.eq (.app2 (.binop .lt rfl) (.pvV x) (.pvV y))
          (.app0 (.lit true))) ∧ ¬ (holds σ (.eq (.pvV x) (.pvV y)) ∧
            holds σ (lexFml xs ys)))) ↔ _
      rw [holds_eq_of_eval hlt (show (Tm.app0 (C := C) (.lit (p := .bool) true)).eval σ = some true from rfl),
        heq, ih ys]
      have hd : (decide ((TEnv.get x σ.env).1 < (TEnv.get y σ.env).1) = true) ↔
          (TEnv.get x σ.env).1 < (TEnv.get y σ.env).1 := decide_eq_true_iff
      rw [hd]
      simp only [Refs.read, UIntTuple.toNat, LoopMetrics.NatTuple.Lt,
        Prod.lex_def, uint_toNat_lt, uint_toNat_eq, Classical.not_and_iff_not_or_not,
        Classical.not_not, not_or, Nat.lt_eq]

theorem lexFml_holds_wk (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {n : Nat} (a b : Refs Γ n) :
    holds (σ.lift h d) (lexFml (a.wk h) (b.wk h)) ↔ holds σ (lexFml a b) := by
  rw [lexFml_holds, lexFml_holds]
  change LoopMetrics.NatTuple.Lt ((a.wk h).read (TEnv.put h σ.env d)).toNat
    ((b.wk h).read (TEnv.put h σ.env d)).toNat ↔ _
  rw [Refs.read_wk, Refs.read_wk]

theorem snapshotsDecrease_holds (σ : State C Γ) {n : Nat} (before after : UIntTuple n) :
    holds (saveState (saveState σ before) after) (snapshotsDecrease n) ↔
      LoopMetrics.NatTuple.Lt after.toNat before.toNat := by
  rw [snapshotsDecrease, lexFml_holds]
  change LoopMetrics.NatTuple.Lt
    ((freshRefs (SavedCtx n Γ) n).read (extendEnv after (extendEnv before σ.env))).toNat
    (((freshRefs Γ n).wk (.ofExt (savedExt (SavedCtx n Γ) n))).read
      (extendEnv after (extendEnv before σ.env))).toNat ↔ _
  rw [freshRefs_read, Refs.read_saved, freshRefs_read]

/-- info: 'Solidity.LoopLex.snapshot_lands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms snapshot_lands
/-- info: 'Solidity.LoopLex.snapshot_globT_iff_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms snapshot_globT_iff_eval
/-- info: 'Solidity.LoopLex.lexFml_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lexFml_holds
/-- info: 'Solidity.LoopLex.metrics_eval_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms metrics_eval_saved

end Solidity.LoopLex
