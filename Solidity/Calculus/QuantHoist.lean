import Solidity.Calculus.QuantArithmetic

/-!
# Storage reads hoisted out of quantifiers (M7, step 4)

A quantifier past the prefix whose body reads storage at no variable it
binds (`∃ y. balances[k] == y + y`) is Presburger once the read is named:
`quantReduction?` compiles its subformulas read-free.  `LFml.hoistOut`
replaces each such read inside a quantifier (outside binders, a read of
a total path whose atoms the quantifiers inside do not bind) by a fresh
atom `r`, and the body becomes `⋀ (read == r) → body'`, the definitions
outside every binder, where the flattener reads them (`hoistPrep`).

The step is exact in the reading the reduction needs (`Prep`): the
prepared body valid makes the body valid (the fresh atoms set to the
reads' values, `HDef.fill`), and where it fails, the body fails at the
same state (its definitions hold there, so each atom is its read).

A `Prep` is what every such stage gives `quantReduction?`: the
prepared body is decided in the body's place, and a refuting state of
the prepared body yields one of the body, at the same atoms.  Array
property instantiation (`Calculus/ArrayProperty.lean`) is the other.
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Preparations -/

/-- **A body decided through another**: valid where the other is, refuted
(at a state of its own, the atoms kept) where the other is. -/
structure Prep (B : LFml C) where
  body : LFml C
  sound : (∀ (g : State C []) (ν : AEnv), body.holds g ν) → ∀ (g : State C []) (ν : AEnv), B.holds g ν
  refute : (g : State C []) → (ν : AEnv) → ¬ body.holds g ν → {g' : State C [] // ¬ B.holds g' ν}

/-- **A preparation is exact**: the prepared body is valid exactly where
the body is. -/
theorem Prep.valid_iff {B : LFml C} (P : Prep B) : P.body.Valid ↔ B.Valid :=
  ⟨P.sound, fun hv g ν => Classical.byContradiction fun hn => (P.refute g ν hn).2 (hv _ ν)⟩

/-- The body itself. -/
def Prep.id (B : LFml C) : Prep B := ⟨B, fun h => h, fun g _ h => ⟨g, h⟩⟩

/-- One preparation after another. -/
def Prep.trans {B : LFml C} (P : Prep B) (Q : Prep P.body) : Prep B :=
  ⟨Q.body, fun h => P.sound (Q.sound h), fun g ν h => P.refute (Q.refute g ν h).1 ν (Q.refute g ν h).2⟩

/-! ## Total reads -/

/-- A term that returns wherever its atoms do: atoms, literals, roots,
fields, unchecked keys, and the words read there. -/
def LTm.totalB : {s : Srt} → LTm C s → Bool
  | _, .var _ => true
  | _, .app0 o =>
    match o with
    | .lit _ | .root .. => true
    | _ => false
  | _, .app1 o q =>
    match o with
    | .field _ => q.totalB
    | _ => false
  | _, .index _ q i => q.totalB && i.totalB
  | _, .obsW q => q.totalB
  | _, _ => false

theorem LTm.totalB_eval (g : State C []) (ν : AEnv) {s : Srt} (t : LTm C s) (h : t.totalB = true) :
    (t.eval g ν).isSome = true := by
  induction t with
  | var _ => rfl
  | app0 o => cases o <;> first | rfl | simp only [LTm.totalB, Bool.false_eq_true] at h
  | app1 o q ih =>
    cases o with
    | field hf =>
      have := ih h
      rw [LTm.eval_app1, Close.Op1.eval_field]
      cases hq : q.eval g ν with
      | none => rw [hq] at this; cases this
      | some _ => rfl
    | _ => simp only [LTm.totalB, Bool.false_eq_true] at h
  | index it q i ihq ihi =>
    simp only [LTm.totalB, Bool.and_eq_true] at h
    have h1 := ihq h.1
    have h2 := ihi h.2
    rw [LTm.eval_index]
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => rw [hq] at h1; cases h1
    | some _ =>
      cases hi : (i.eval g ν : Option _) with
      | none => rw [hi] at h2; cases h2
      | some _ => rfl
  | obsW q ih =>
    have h1 := ih h
    rw [LTm.eval_obsW]
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => rw [hq] at h1; cases h1
    | some _ => rfl
  | _ => simp only [LTm.totalB, Bool.false_eq_true] at h

/-! ## Hoisted reads -/

/-- A hoisted read: the read `t`, named by the atom at `m`. -/
structure HDef (C : Contract) where
  p : PrimTy
  t : LTm C (.val p)
  m : Nat

/-- The atom holds the read's value. -/
def HDef.Good (g : State C []) (ν : AEnv) (e : HDef C) : Prop :=
  (e.t.eval g ν : Option e.p.Denote) = some (ν.get e.p e.m)

/-- `t == r`. -/
def HDef.fml (e : HDef C) : LFml C := .eq e.t (.var e.m)

theorem HDef.holds_fml (g : State C []) (ν : AEnv) (e : HDef C) : e.fml.holds g ν ↔ e.Good g ν := by
  rw [HDef.fml, LFml.holds_eq_iff, HDef.Good, LTm.eval_var]
  exact ⟨fun ⟨_, h1, h2⟩ => h1.trans h2.symm, fun h => ⟨_, h, rfl⟩⟩

/-- **A term, its reads at no variable of `bs` hoisted**: each such read
of a total path becomes the atom at the next position from `n`. -/
def LTm.hoist (bs : List Parameter) : {s : Srt} → LTm C s → Nat → LTm C s × List (HDef C)
  | _, .obsW (p := p) q, n =>
    if q.totalB && q.parameters.all (· ∉ bs) then (.var n, [⟨p, .obsW q, n⟩])
    else (.obsW (q.hoist bs n).1, (q.hoist bs n).2)
  | _, .app1 o a, n => (.app1 o (a.hoist bs n).1, (a.hoist bs n).2)
  | _, .obsL a, n => (.obsL (a.hoist bs n).1, (a.hoist bs n).2)
  | _, .obsH a, n => (.obsH (a.hoist bs n).1, (a.hoist bs n).2)
  | _, .app2 o a b, n =>
    (.app2 o (a.hoist bs n).1 (b.hoist bs (n + (a.hoist bs n).2.length)).1,
      (a.hoist bs n).2 ++ (b.hoist bs (n + (a.hoist bs n).2.length)).2)
  | _, .index it a b, n =>
    (.index it (a.hoist bs n).1 (b.hoist bs (n + (a.hoist bs n).2.length)).1,
      (a.hoist bs n).2 ++ (b.hoist bs (n + (a.hoist bs n).2.length)).2)
  | _, .seq a b, n =>
    (.seq (a.hoist bs n).1 (b.hoist bs (n + (a.hoist bs n).2.length)).1,
      (a.hoist bs n).2 ++ (b.hoist bs (n + (a.hoist bs n).2.length)).2)
  | _, .orElse a b, n =>
    (.orElse (a.hoist bs n).1 (b.hoist bs (n + (a.hoist bs n).2.length)).1,
      (a.hoist bs n).2 ++ (b.hoist bs (n + (a.hoist bs n).2.length)).2)
  | _, .app3 o a b c, n =>
    (.app3 o (a.hoist bs n).1 (b.hoist bs (n + (a.hoist bs n).2.length)).1
        (c.hoist bs (n + (a.hoist bs n).2.length + (b.hoist bs (n + (a.hoist bs n).2.length)).2.length)).1,
      (a.hoist bs n).2 ++ (b.hoist bs (n + (a.hoist bs n).2.length)).2 ++
        (c.hoist bs (n + (a.hoist bs n).2.length + (b.hoist bs (n + (a.hoist bs n).2.length)).2.length)).2)
  | _, .kite a b t e, n =>
    let A := a.hoist bs n
    let B := b.hoist bs (n + A.2.length)
    let T := t.hoist bs (n + A.2.length + B.2.length)
    let E := e.hoist bs (n + A.2.length + B.2.length + T.2.length)
    (.kite A.1 B.1 T.1 E.1, A.2 ++ B.2 ++ T.2 ++ E.2)
  | _, t, _ => (t, [])

/-- What the hoisting of a term keeps: its atoms are `n`, `n + 1`, …, its
reads total, at no variable of `bs`, below the term's atoms; where each
atom holds its read, the term reads as before. -/
structure HoistSpec (bs : List Parameter) (n bound : Nat) {s : Srt} (t : LTm C s)
    (r : LTm C s × List (HDef C)) : Prop where
  keys : r.2.map (·.m) = List.range' n r.2.length
  total : ∀ e ∈ r.2, e.t.totalB = true
  free : ∀ e ∈ r.2, ∀ q ∈ e.t.parameters, q ∉ bs
  below : ∀ e ∈ r.2, e.t.atomBound ≤ bound
  eval : ∀ (g : State C []) (ν : AEnv), (∀ e ∈ r.2, e.Good g ν) → r.1.eval g ν = t.eval g ν

theorem HoistSpec.nil {bs : List Parameter} {n bound : Nat} {s : Srt} (t : LTm C s) :
    HoistSpec bs n bound t (t, []) :=
  ⟨rfl, (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), fun _ _ _ => rfl⟩

theorem range'_append_len (n a b : Nat) : List.range' n a ++ List.range' (n + a) b = List.range' n (a + b) := by
  rw [List.range'_append_1]

/-- Two specs side by side. -/
theorem HoistSpec.keys_append {n : Nat} (l₁ l₂ : List (HDef C))
    (h₁ : l₁.map (·.m) = List.range' n l₁.length) (h₂ : l₂.map (·.m) = List.range' (n + l₁.length) l₂.length) :
    (l₁ ++ l₂).map (·.m) = List.range' n (l₁ ++ l₂).length := by
  rw [List.map_append, h₁, h₂, List.length_append, List.range'_append_1]

theorem forall_mem_append {α : Type} {P : α → Prop} {l₁ l₂ : List α} :
    (∀ e ∈ l₁ ++ l₂, P e) ↔ (∀ e ∈ l₁, P e) ∧ (∀ e ∈ l₂, P e) :=
  ⟨fun h => ⟨fun e he => h e (List.mem_append_left _ he), fun e he => h e (List.mem_append_right _ he)⟩,
    fun h e he => (List.mem_append.1 he).elim (h.1 e) (h.2 e)⟩

theorem LTm.hoist_spec (bs : List Parameter) : ∀ {s : Srt} (t : LTm C s) (n : Nat) {bound : Nat},
    t.atomBound ≤ bound → HoistSpec bs n bound t (t.hoist bs n)
  | _, .obsW (p := p) q, n, bound, hb => by
    unfold LTm.hoist
    split
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · intro e he; rw [List.mem_singleton.1 he]; exact hc.1
      · intro e he; rw [List.mem_singleton.1 he]; exact hc.2
      · intro e he; rw [List.mem_singleton.1 he]; exact hb
      · intro g ν h
        exact (h _ List.mem_cons_self).symm
    · have A := LTm.hoist_spec bs q n (bound := bound) hb
      exact ⟨A.keys, A.total, A.free, A.below, fun g ν h => by
        rw [LTm.eval_obsW, LTm.eval_obsW, A.eval g ν h]⟩
  | _, .app1 o a, n, bound, hb => by
    have A := LTm.hoist_spec bs a n (bound := bound) hb
    exact ⟨A.keys, A.total, A.free, A.below, fun g ν h => by
      show (LTm.app1 o _).eval g ν = _
      rw [LTm.eval_app1, LTm.eval_app1, A.eval g ν h]⟩
  | _, .obsL a, n, bound, hb => by
    have A := LTm.hoist_spec bs a n (bound := bound) hb
    exact ⟨A.keys, A.total, A.free, A.below, fun g ν h => by
      show (LTm.obsL _).eval g ν = _
      rw [LTm.eval_obsL, LTm.eval_obsL, A.eval g ν h]⟩
  | _, .obsH a, n, bound, hb => by
    have A := LTm.hoist_spec bs a n (bound := bound) hb
    exact ⟨A.keys, A.total, A.free, A.below, fun g ν h => by
      show (LTm.obsH _).eval g ν = _
      rw [LTm.eval_obsH, LTm.eval_obsH, A.eval g ν h]⟩
  | _, .app2 o a b, n, bound, hb => by
    simp only [LTm.atomBound] at hb
    have A := LTm.hoist_spec bs a n (bound := bound) (by omega)
    have B := LTm.hoist_spec bs b (n + (a.hoist bs n).2.length) (bound := bound) (by omega)
    refine ⟨HoistSpec.keys_append _ _ A.keys B.keys, forall_mem_append.2 ⟨A.total, B.total⟩,
      forall_mem_append.2 ⟨A.free, B.free⟩, forall_mem_append.2 ⟨A.below, B.below⟩, fun g ν h => ?_⟩
    have h' := forall_mem_append.1 h
    show (LTm.app2 o _ _).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2, A.eval g ν h'.1, B.eval g ν h'.2]
  | _, .index it a b, n, bound, hb => by
    simp only [LTm.atomBound] at hb
    have A := LTm.hoist_spec bs a n (bound := bound) (by omega)
    have B := LTm.hoist_spec bs b (n + (a.hoist bs n).2.length) (bound := bound) (by omega)
    refine ⟨HoistSpec.keys_append _ _ A.keys B.keys, forall_mem_append.2 ⟨A.total, B.total⟩,
      forall_mem_append.2 ⟨A.free, B.free⟩, forall_mem_append.2 ⟨A.below, B.below⟩, fun g ν h => ?_⟩
    have h' := forall_mem_append.1 h
    show (LTm.index it _ _).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, A.eval g ν h'.1, B.eval g ν h'.2]
  | _, .seq a b, n, bound, hb => by
    simp only [LTm.atomBound] at hb
    have A := LTm.hoist_spec bs a n (bound := bound) (by omega)
    have B := LTm.hoist_spec bs b (n + (a.hoist bs n).2.length) (bound := bound) (by omega)
    refine ⟨HoistSpec.keys_append _ _ A.keys B.keys, forall_mem_append.2 ⟨A.total, B.total⟩,
      forall_mem_append.2 ⟨A.free, B.free⟩, forall_mem_append.2 ⟨A.below, B.below⟩, fun g ν h => ?_⟩
    have h' := forall_mem_append.1 h
    show (LTm.seq _ _).eval g ν = _
    rw [LTm.eval_seq, LTm.eval_seq, A.eval g ν h'.1, B.eval g ν h'.2]
  | _, .orElse a b, n, bound, hb => by
    simp only [LTm.atomBound] at hb
    have A := LTm.hoist_spec bs a n (bound := bound) (by omega)
    have B := LTm.hoist_spec bs b (n + (a.hoist bs n).2.length) (bound := bound) (by omega)
    refine ⟨HoistSpec.keys_append _ _ A.keys B.keys, forall_mem_append.2 ⟨A.total, B.total⟩,
      forall_mem_append.2 ⟨A.free, B.free⟩, forall_mem_append.2 ⟨A.below, B.below⟩, fun g ν h => ?_⟩
    have h' := forall_mem_append.1 h
    show (LTm.orElse _ _).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, A.eval g ν h'.1, B.eval g ν h'.2]
  | _, .app3 o a b c, n, bound, hb => by
    simp only [LTm.atomBound] at hb
    have A := LTm.hoist_spec bs a n (bound := bound) (by omega)
    have B := LTm.hoist_spec bs b (n + (a.hoist bs n).2.length) (bound := bound) (by omega)
    have D := LTm.hoist_spec bs c (n + (a.hoist bs n).2.length + (b.hoist bs (n + (a.hoist bs n).2.length)).2.length)
      (bound := bound) (by omega)
    refine ⟨HoistSpec.keys_append _ _ (HoistSpec.keys_append _ _ A.keys B.keys)
        (by rw [List.length_append, ← Nat.add_assoc]; exact D.keys),
      forall_mem_append.2 ⟨forall_mem_append.2 ⟨A.total, B.total⟩, D.total⟩,
      forall_mem_append.2 ⟨forall_mem_append.2 ⟨A.free, B.free⟩, D.free⟩,
      forall_mem_append.2 ⟨forall_mem_append.2 ⟨A.below, B.below⟩, D.below⟩, fun g ν h => ?_⟩
    have h' := forall_mem_append.1 h
    have h'' := forall_mem_append.1 h'.1
    show (LTm.app3 o _ _ _).eval g ν = _
    rw [LTm.eval_app3, LTm.eval_app3, A.eval g ν h''.1, B.eval g ν h''.2, D.eval g ν h'.2]
  | _, .kite a b t e, n, bound, hb => by
    simp only [LTm.atomBound] at hb
    have A := LTm.hoist_spec bs a n (bound := bound) (by omega)
    have B := LTm.hoist_spec bs b (n + (a.hoist bs n).2.length) (bound := bound) (by omega)
    have T := LTm.hoist_spec bs t (n + (a.hoist bs n).2.length + (b.hoist bs (n + (a.hoist bs n).2.length)).2.length)
      (bound := bound) (by omega)
    have E := LTm.hoist_spec bs e (n + (a.hoist bs n).2.length + (b.hoist bs (n + (a.hoist bs n).2.length)).2.length +
      (t.hoist bs (n + (a.hoist bs n).2.length + (b.hoist bs (n + (a.hoist bs n).2.length)).2.length)).2.length)
      (bound := bound) (by omega)
    refine ⟨HoistSpec.keys_append _ _ (HoistSpec.keys_append _ _ (HoistSpec.keys_append _ _ A.keys B.keys)
          (by rw [List.length_append, ← Nat.add_assoc]; exact T.keys))
        (by simp only [List.length_append, ← Nat.add_assoc]; exact E.keys),
      forall_mem_append.2 ⟨forall_mem_append.2 ⟨forall_mem_append.2 ⟨A.total, B.total⟩, T.total⟩, E.total⟩,
      forall_mem_append.2 ⟨forall_mem_append.2 ⟨forall_mem_append.2 ⟨A.free, B.free⟩, T.free⟩, E.free⟩,
      forall_mem_append.2 ⟨forall_mem_append.2 ⟨forall_mem_append.2 ⟨A.below, B.below⟩, T.below⟩, E.below⟩,
      fun g ν h => ?_⟩
    have h1 := forall_mem_append.1 h
    have h2 := forall_mem_append.1 h1.1
    have h3 := forall_mem_append.1 h2.1
    show (LTm.kite _ _ _ _).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, A.eval g ν h3.1, B.eval g ν h3.2, T.eval g ν h2.2, E.eval g ν h1.2]
  | _, .var _, _, _, _ | _, .app0 _, _, _, _ | _, .err, _, _, _ => HoistSpec.nil _

/-! ## Formulas -/

/-- Inside a quantifier: the reads of each equation at no variable bound
on the way (`bs`) hoisted. -/
def LFml.hoistIn (bs : List Parameter) : LFml C → Nat → LFml C × List (HDef C)
  | .tt, _ => (.tt, [])
  | .eq a b, n => (.eq (a.hoist bs n).1 (b.hoist bs (n + (a.hoist bs n).2.length)).1,
      (a.hoist bs n).2 ++ (b.hoist bs (n + (a.hoist bs n).2.length)).2)
  | .not φ, n => ((φ.hoistIn bs n).1.not, (φ.hoistIn bs n).2)
  | .and φ ψ, n => (.and (φ.hoistIn bs n).1 (ψ.hoistIn bs (n + (φ.hoistIn bs n).2.length)).1,
      (φ.hoistIn bs n).2 ++ (ψ.hoistIn bs (n + (φ.hoistIn bs n).2.length)).2)
  | .imp φ ψ, n => (.imp (φ.hoistIn bs n).1 (ψ.hoistIn bs (n + (φ.hoistIn bs n).2.length)).1,
      (φ.hoistIn bs n).2 ++ (ψ.hoistIn bs (n + (φ.hoistIn bs n).2.length)).2)
  | .all k p φ, n => (.all k p (φ.hoistIn (⟨p, k⟩ :: bs) n).1, (φ.hoistIn (⟨p, k⟩ :: bs) n).2)

/-- **The body's quantifiers, their reads hoisted**; nothing outside a
quantifier changes. -/
def LFml.hoistOut : LFml C → Nat → LFml C × List (HDef C)
  | .all k p φ, n => (.all k p (φ.hoistIn [⟨p, k⟩] n).1, (φ.hoistIn [⟨p, k⟩] n).2)
  | .not φ, n => ((φ.hoistOut n).1.not, (φ.hoistOut n).2)
  | .and φ ψ, n => (.and (φ.hoistOut n).1 (ψ.hoistOut (n + (φ.hoistOut n).2.length)).1,
      (φ.hoistOut n).2 ++ (ψ.hoistOut (n + (φ.hoistOut n).2.length)).2)
  | .imp φ ψ, n => (.imp (φ.hoistOut n).1 (ψ.hoistOut (n + (φ.hoistOut n).2.length)).1,
      (φ.hoistOut n).2 ++ (ψ.hoistOut (n + (φ.hoistOut n).2.length)).2)
  | φ, _ => (φ, [])

/-- What the hoisting of a formula keeps; its atoms past `n` are fresh. -/
structure HoistF (n bound : Nat) (φ : LFml C) (r : LFml C × List (HDef C)) : Prop where
  keys : r.2.map (·.m) = List.range' n r.2.length
  total : ∀ e ∈ r.2, e.t.totalB = true
  below : ∀ e ∈ r.2, e.t.atomBound ≤ bound
  holds : ∀ (g : State C []) (ν : AEnv), (∀ e ∈ r.2, e.Good g ν) → (r.1.holds g ν ↔ φ.holds g ν)

/-- An atom past every binder keeps its read under the binder. -/
theorem HDef.good_set {g : State C []} {ν : AEnv} {e : HDef C} (h : e.Good g ν) (p : PrimTy) (k : Nat)
    (v : p.Denote) (hq : (⟨p, k⟩ : Parameter) ∉ e.t.parameters) (hk : k < e.m) : e.Good g (ν.set p k v) := by
  unfold HDef.Good at h ⊢
  rw [AEnv.get_set_ne ν p e.p v (Nat.ne_of_gt hk), ← h]
  exact e.t.eval_agree_parameters g fun q hq' =>
    Parameter.read_set_ne q ⟨p, k⟩ (fun he => hq (he ▸ hq')) ν v

theorem LFml.hoistIn_spec : ∀ (bs : List Parameter) (φ : LFml C) (n : Nat) {bound : Nat},
    φ.atomBound ≤ bound → bound ≤ n →
      HoistF n bound φ (φ.hoistIn bs n) ∧ ∀ e ∈ (φ.hoistIn bs n).2, ∀ q ∈ e.t.parameters, q ∉ bs
  | _, .tt, _, _, _, _ => ⟨⟨rfl, (fun _ h => nomatch h), (fun _ h => nomatch h), fun _ _ _ => Iff.rfl⟩,
      (fun _ h => nomatch h)⟩
  | bs, .eq a b, n, bound, hb, hn => by
    simp only [LFml.atomBound] at hb
    have A := LTm.hoist_spec bs a n (bound := bound) (by omega)
    have B := LTm.hoist_spec bs b (n + (a.hoist bs n).2.length) (bound := bound) (by omega)
    refine ⟨⟨HoistSpec.keys_append _ _ A.keys B.keys, forall_mem_append.2 ⟨A.total, B.total⟩,
      forall_mem_append.2 ⟨A.below, B.below⟩, fun g ν h => ?_⟩, forall_mem_append.2 ⟨A.free, B.free⟩⟩
    have h' := forall_mem_append.1 h
    show (LFml.eq _ _).holds g ν ↔ _
    simp only [LFml.holds, A.eval g ν h'.1, B.eval g ν h'.2]
  | bs, .not φ, n, bound, hb, hn => by
    obtain ⟨A, hA⟩ := LFml.hoistIn_spec bs φ n (bound := bound) hb hn
    exact ⟨⟨A.keys, A.total, A.below, fun g ν h => not_congr (A.holds g ν h)⟩, hA⟩
  | bs, .and φ ψ, n, bound, hb, hn | bs, .imp φ ψ, n, bound, hb, hn => by
    simp only [LFml.atomBound] at hb
    obtain ⟨A, hA⟩ := LFml.hoistIn_spec bs φ n (bound := bound) (by omega) hn
    obtain ⟨B, hB⟩ := LFml.hoistIn_spec bs ψ (n + (φ.hoistIn bs n).2.length) (bound := bound) (by omega)
      (by omega)
    refine ⟨⟨HoistSpec.keys_append _ _ A.keys B.keys, forall_mem_append.2 ⟨A.total, B.total⟩,
      forall_mem_append.2 ⟨A.below, B.below⟩, fun g ν h => ?_⟩, forall_mem_append.2 ⟨hA, hB⟩⟩
    have h' := forall_mem_append.1 h
    first
      | exact and_congr (A.holds g ν h'.1) (B.holds g ν h'.2)
      | exact imp_congr (A.holds g ν h'.1) (B.holds g ν h'.2)
  | bs, .all k p φ, n, bound, hb, hn => by
    simp only [LFml.atomBound] at hb
    obtain ⟨A, hA⟩ := LFml.hoistIn_spec (⟨p, k⟩ :: bs) φ n (bound := bound) (by omega) hn
    have hkb : k < bound := by omega
    refine ⟨⟨A.keys, A.total, A.below, fun g ν h => forall_congr' fun v => A.holds g _ fun e he =>
      HDef.good_set (h e he) p k v (fun hq => hA e he _ hq List.mem_cons_self) ?_⟩,
      fun e he q hq hmem => hA e he q hq (List.mem_cons_of_mem _ hmem)⟩
    have hm : e.m ∈ (φ.hoistIn (⟨p, k⟩ :: bs) n).2.map (·.m) := List.mem_map.2 ⟨e, he, rfl⟩
    rw [A.keys, List.mem_range'_1] at hm
    omega

theorem LFml.hoistOut_spec : ∀ (φ : LFml C) (n : Nat) {bound : Nat},
    φ.atomBound ≤ bound → bound ≤ n → HoistF n bound φ (φ.hoistOut n)
  | .all k p φ, n, _, hb, hn => (LFml.hoistIn_spec [] (.all k p φ) n hb hn).1
  | .not φ, n, bound, hb, hn => by
    have A := LFml.hoistOut_spec φ n (bound := bound) hb hn
    exact ⟨A.keys, A.total, A.below, fun g ν h => not_congr (A.holds g ν h)⟩
  | .and φ ψ, n, bound, hb, hn | .imp φ ψ, n, bound, hb, hn => by
    simp only [LFml.atomBound] at hb
    have A := LFml.hoistOut_spec φ n (bound := bound) (by omega) hn
    have B := LFml.hoistOut_spec ψ (n + (φ.hoistOut n).2.length) (bound := bound) (by omega) (by omega)
    refine ⟨HoistSpec.keys_append _ _ A.keys B.keys, forall_mem_append.2 ⟨A.total, B.total⟩,
      forall_mem_append.2 ⟨A.below, B.below⟩, fun g ν h => ?_⟩
    have h' := forall_mem_append.1 h
    first
      | exact and_congr (A.holds g ν h'.1) (B.holds g ν h'.2)
      | exact imp_congr (A.holds g ν h'.1) (B.holds g ν h'.2)
  | .tt, _, _, _, _ | .eq _ _, _, _, _, _ =>
    ⟨rfl, (fun _ h => nomatch h), (fun _ h => nomatch h), fun _ _ _ => Iff.rfl⟩

/-! ## The atoms set to the reads -/

/-- Each atom set to its read's value in `ν`. -/
noncomputable def HDef.fill (g : State C []) (ν : AEnv) : List (HDef C) → AEnv → AEnv
  | [], μ => μ
  | e :: es, μ => HDef.fill g ν es (μ.set e.p e.m ((e.t.eval g ν).getD (PrimTy.dflt e.p)))

theorem HDef.fill_get_ne (g : State C []) (ν : AEnv) (p : PrimTy) (j : Nat) :
    ∀ (es : List (HDef C)) (μ : AEnv), j ∉ es.map (·.m) → (HDef.fill g ν es μ).get p j = μ.get p j
  | [], _, _ => rfl
  | e :: es, μ, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [HDef.fill, HDef.fill_get_ne g ν p j es _ h.2, AEnv.get_set_ne μ e.p p _ h.1]

theorem HDef.fill_get (g : State C []) (ν : AEnv) :
    ∀ (es : List (HDef C)) (μ : AEnv), (es.map (·.m)).Nodup → ∀ e ∈ es,
      (HDef.fill g ν es μ).get e.p e.m = (e.t.eval g ν).getD (PrimTy.dflt e.p)
  | [], _, _, _, h => nomatch h
  | e' :: es, μ, hn, e, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [HDef.fill]
    rcases List.mem_cons.1 he with rfl | he
    · rw [HDef.fill_get_ne g ν _ _ es _ hn.1, AEnv.get_set_self]
    · exact HDef.fill_get g ν es _ hn.2 e he

theorem HDef.fill_below (g : State C []) (ν : AEnv) (n : Nat) :
    ∀ (es : List (HDef C)) (μ : AEnv), (∀ e ∈ es, n ≤ e.m) → μ.AgreesBelow n (HDef.fill g ν es μ)
  | [], _, _ => fun _ _ _ => rfl
  | e :: es, μ, h => fun p k hk => by
    rw [HDef.fill, HDef.fill_get_ne g ν p k es _ (fun hm => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 hm
      have := h e' (List.mem_cons_of_mem _ he'); omega)]
    exact (AEnv.get_set_ne μ e.p p _ (by have := h e List.mem_cons_self; omega)).symm

/-- **Reads hoisted out of the body's quantifiers**, their definitions in
front (`HDef.fml`); the body itself where nothing is hoisted. -/
def hoistPrep (B : LFml C) : Prep B :=
  if (B.hoistOut B.atomBound).2.isEmpty then Prep.id B
  else
    { body := .imp (LFml.conj ((B.hoistOut B.atomBound).2.map HDef.fml)) (B.hoistOut B.atomBound).1
      sound := fun hv g ν => by
        have H := LFml.hoistOut_spec B B.atomBound (Nat.le_refl _) (Nat.le_refl _)
        have hge : ∀ e ∈ (B.hoistOut B.atomBound).2, B.atomBound ≤ e.m := fun e he => by
          have hm : e.m ∈ (B.hoistOut B.atomBound).2.map (·.m) := List.mem_map.2 ⟨e, he, rfl⟩
          rw [H.keys, List.mem_range'_1] at hm
          exact hm.1
        have hnd : ((B.hoistOut B.atomBound).2.map (·.m)).Nodup := by rw [H.keys]; exact List.nodup_range'
        let μ := HDef.fill g ν (B.hoistOut B.atomBound).2 ν
        have hagree : ν.AgreesBelow B.atomBound μ := HDef.fill_below g ν _ _ ν hge
        have hgood : ∀ e ∈ (B.hoistOut B.atomBound).2, e.Good g μ := by
          intro e he
          unfold HDef.Good
          rw [HDef.fill_get g ν _ ν hnd e he, ← e.t.eval_agree_below g (hagree.mono (H.below e he))]
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (LTm.totalB_eval g ν e.t (H.total e he))
          rw [hv, Option.getD_some]
        have hc : (LFml.conj ((B.hoistOut B.atomBound).2.map HDef.fml)).holds g μ := by
          rw [LFml.holds_conj]
          intro d hd
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
          exact (HDef.holds_fml g μ e).2 (hgood e he)
        exact (LFml.holds_agree_below g B hagree).2 ((H.holds g μ hgood).1 (hv g μ hc))
      refute := fun g ν hn => ⟨g, fun hB => hn fun hc => by
        have H := LFml.hoistOut_spec B B.atomBound (Nat.le_refl _) (Nat.le_refl _)
        have hgood : ∀ e ∈ (B.hoistOut B.atomBound).2, e.Good g ν := by
          rw [LFml.holds_conj] at hc
          exact fun e he => (HDef.holds_fml g ν e).1 (hc _ (List.mem_map.2 ⟨e, he, rfl⟩))
        exact (H.holds g ν hgood).2 hB⟩ }

/-- **Hoisting is exact.** -/
theorem hoistPrep_valid_iff (B : LFml C) : (hoistPrep B).body.Valid ↔ B.Valid := (hoistPrep B).valid_iff

/-- info: 'Solidity.Decide.hoistPrep_valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hoistPrep_valid_iff

end Solidity.Decide
