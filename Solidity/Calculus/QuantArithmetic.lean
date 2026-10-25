import Solidity.Calculus.Prenex
import Solidity.Calculus.PresburgerDecision

/-!
# Quantified leaves compiled to quantified linear arithmetic (M7, step 4)

A quantifier of a leaf whose body reads nothing in storage (a Presburger
quantifier over value locals) is compiled to `QFml` (`Calculus/
PresburgerDecision.lean`): each equation by the shared checked compiler
(`StorageEncoding.ofFormula?`), its parameters placed at the positions
`pos` gives them, a binder at its variable's position under the variable's
range.  The compiled formula holds exactly where the leaf does, at every
assignment that represents the valuation at those positions (`QArith`).

The equation is read-free (`readFreeFormula?`), so it holds alike in every
storage.  Any storage scalar its compiled form still names (the compiler's
static reads; none is expected under that check, but the proof does not
rely on it) gets a position of its own, any value in range.

Positions are named, not de Bruijn: `.all k p φ` binds the variable at
`pos ⟨p, k⟩`, shadowing it as `AEnv.set` does.
-/

namespace Solidity.Decide

open Linear ScalarCode ReadRealization

variable {C : Contract}

/-! ## Free parameters -/

/-- The parameters a formula reads outside its own binders. -/
def LFml.freeParams : LFml C → List Parameter
  | .tt => []
  | .eq a b => a.parameters ++ b.parameters
  | .not φ => φ.freeParams
  | .and φ ψ | .imp φ ψ => φ.freeParams ++ ψ.freeParams
  | .all k p φ => φ.freeParams.filter (· ≠ ⟨p, k⟩)

/-- **A formula reads only its free parameters.** -/
theorem LFml.holds_agree_free (g : State C []) :
    ∀ (φ : LFml C) {ν μ : AEnv}, Parameters.Agree φ.freeParams ν μ → (φ.holds g ν ↔ φ.holds g μ)
  | .tt, _, _, _ => Iff.rfl
  | .eq a b, ν, μ, h => LFml.holds_agree g (.eq a b) h
  | .not φ, _, _, h => not_congr (LFml.holds_agree_free g φ h)
  | .and φ ψ, _, _, h => and_congr (LFml.holds_agree_free g φ h.left) (LFml.holds_agree_free g ψ h.right)
  | .imp φ ψ, _, _, h => imp_congr (LFml.holds_agree_free g φ h.left) (LFml.holds_agree_free g ψ h.right)
  | .all k p φ, ν, μ, h => forall_congr' fun v => LFml.holds_agree_free g φ fun q hq => by
      by_cases he : q = ⟨p, k⟩
      · subst he
        exact (Parameter.read_set ⟨p, k⟩ ν v).trans (Parameter.read_set ⟨p, k⟩ μ v).symm
      · exact (Parameter.read_set_ne q ⟨p, k⟩ he ν v).trans ((h q (List.mem_filter.2 ⟨hq,
          by simp only [ne_eq, he, not_false_eq_true, decide_true]⟩)).trans
          (Parameter.read_set_ne q ⟨p, k⟩ he μ v).symm)

theorem LFml.freeParams_sub : ∀ (φ : LFml C), ∀ q ∈ φ.freeParams, q ∈ φ.parameters
  | .tt, _, h => h
  | .eq _ _, _, h => h
  | .not φ, q, h => LFml.freeParams_sub φ q h
  | .and φ ψ, q, h | .imp φ ψ, q, h => by
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append_left _ (LFml.freeParams_sub φ q h)
    · exact List.mem_append_right _ (LFml.freeParams_sub ψ q h)
  | .all _ _ φ, q, h => LFml.freeParams_sub φ q (List.mem_filter.1 h).1

/-! ## Representation of a valuation -/

/-- The code of a parameter's value. -/
def Parameter.code (q : Parameter) (ν : AEnv) : Nat := (encode q.prim (q.read ν)).val

/-- `x` holds the codes of `ν`'s parameters `qs` at their positions. -/
def Rep (pos : Parameter → Nat) (qs : List Parameter) (ν : AEnv) (x : Nat → Nat) : Prop :=
  ∀ q ∈ qs, x (pos q) = q.code ν

/-- **What a compiled quantified formula is**: it holds where the leaf
does, at every assignment holding the codes of the leaf's free parameters
at their positions and, at each position of `refs`, any value in range.
The positions `refs` lie in `[start, next)`. -/
structure QArith (φ : LFml C) (pos : Parameter → Nat) (start : Nat) where
  formula : QFml
  refs : List (Nat × PrimTy)
  next : Nat
  start_le : start ≤ next
  refs_mem : ∀ r ∈ refs, start ≤ r.1 ∧ r.1 < next
  correct : ∀ (g : State C []) (ν : AEnv) (x : Nat → Nat), Rep pos φ.freeParams ν x →
    (∀ r ∈ refs, x r.1 < bound r.2) → (formula.holds x ↔ φ.holds g ν)

/-! ## Equations -/

theorem Parameters.index_lt_of_mem {q : Parameter} {ps : List Parameter} (h : q ∈ ps) :
    Parameters.index q ps < ps.length := by
  induction ps with
  | nil => cases h
  | cons x ps ih =>
    unfold Parameters.index
    by_cases he : q = x
    · simp only [he, if_true, List.length_cons]; omega
    · simp only [he, if_false, List.length_cons]
      have := ih ((List.mem_cons.mp h).resolve_left he)
      omega

theorem Parameters.getElem_index {q : Parameter} : ∀ {ps : List Parameter} (h : q ∈ ps),
    ps[Parameters.index q ps]'(Parameters.index_lt_of_mem h) = q
  | [], h => nomatch h
  | x :: ps, h => by
    by_cases he : q = x
    · subst he; simp only [Parameters.index, if_true, List.getElem_cons_zero]
    · have := Parameters.getElem_index ((List.mem_cons.mp h).resolve_left he)
      simp only [Parameters.index, he, if_false, List.getElem_cons_succ]
      exact this

/-- The map of an equation's variables: its parameters at their
positions, then its storage scalars from `start` on. -/
def leafMap (pos : Parameter → Nat) (ps : List Parameter) (n start : Nat) : List Nat :=
  ps.map pos ++ (List.range n).map (start + ·)

theorem leafMap_param (pos : Parameter → Nat) (ps : List Parameter) (n start : Nat) {q : Parameter}
    (h : q ∈ ps) : (leafMap pos ps n start).getD (Parameters.index q ps) 0 = pos q := by
  have hl := Parameters.index_lt_of_mem h
  rw [leafMap, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa only [List.length_map] using hl),
    List.getElem?_map, List.getElem?_eq_getElem hl, Parameters.getElem_index h]
  rfl

theorem leafMap_lt (pos : Parameter → Nat) (ps : List Parameter) (n start : Nat) {k : Nat}
    (h : k < ps.length) : (leafMap pos ps n start).getD k 0 = pos ps[k] := by
  rw [leafMap, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa only [List.length_map] using h),
    List.getElem?_map, List.getElem?_eq_getElem h]
  rfl

theorem leafMap_ref (pos : Parameter → Nat) (ps : List Parameter) (n start : Nat) {u : Nat}
    (h : u < n) : (leafMap pos ps n start).getD (ps.length + u) 0 = start + u := by
  rw [leafMap, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [List.length_map]; omega),
    List.length_map, Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range h]
  rfl

theorem types_length (ps : List Parameter) (rs : List (Ref C)) :
    (Inputs.types [] ps rs).length = ps.length + rs.length := by
  simp only [Inputs.types, Parameters.types, Layout.types, List.length_append, List.length_map]

theorem types_getElem?_param (ps : List Parameter) (rs : List (Ref C)) {k : Nat} (h : k < ps.length) :
    (Inputs.types [] ps rs)[k]? = some ps[k].prim := by
  simp only [Inputs.types, Parameters.types]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using h), List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

theorem types_getElem?_ref (ps : List Parameter) (rs : List (Ref C)) {u : Nat} (h : u < rs.length) :
    (Inputs.types [] ps rs)[ps.length + u]? = some ((Layout.types rs).getD u .bool) := by
  simp only [Inputs.types, Parameters.types, Layout.types]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega), List.length_map,
    Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem h]
  rfl

/-- The storage scalars of an equation, at their positions from `start`. -/
def leafRefs (rs : List (Ref C)) (start : Nat) : List (Nat × PrimTy) :=
  (List.range rs.length).map fun u => (start + u, (Layout.types rs).getD u .bool)

/-- **A compiled equation means the equation**: its parameters read at
their positions, its storage scalars at any value in range. -/
theorem eqn_correct (pos : Parameter → Nat) (start : Nat) {p : PrimTy} (a b : LTm C (.val p))
    (ps : List Parameter) (hps : ∀ q ∈ (LFml.eq a b).parameters, q ∈ ps)
    (hsub : ∀ q ∈ ps, q ∈ (LFml.eq a b).parameters) (hpn : ps.Nodup)
    (enc : StorageEncoding (ps := ps) (es := []) (LFml.eq a b)) (rf : ReadFreeFormula (LFml.eq a b))
    (rs : List (Ref C)) (hr : rs.Nodup) (hc : ∀ q ∈ enc.refs, q ∈ rs)
    (hw : (enc.lower rs).width ≤ ps.length + rs.length)
    (g : State C []) (ν : AEnv) (x : Nat → Nat) (hrep : Rep pos (LFml.eq a b).freeParams ν x)
    (hrefs : ∀ r ∈ leafRefs rs start, x r.1 < bound r.2) :
    (QFml.atom (enc.lower rs) (leafMap pos ps rs.length start)).holds x ↔ (LFml.eq a b).holds g ν := by
  let T := Inputs.types [] ps rs
  let y : Nat → Nat := fun t => x ((leafMap pos ps rs.length start).getD t 0)
  have hy : ∀ q ∈ ps, y (Parameters.index q ps) = q.code ν := by
    intro q hq
    show x _ = _
    rw [leafMap_param pos ps rs.length start hq]
    exact hrep q (hsub q hq)
  have hdom : (domain T).holds y := by
    apply (domainFrom_iff T 0 y).2
    intro k p hk
    rw [Nat.zero_add]
    by_cases hkp : k < ps.length
    · rw [types_getElem?_param ps rs hkp, Option.some.injEq] at hk
      subst hk
      show x _ < _
      rw [leafMap_lt pos ps rs.length start hkp, hrep ps[k] (hsub _ (List.getElem_mem hkp))]
      exact (encode _ _).isLt
    · have hlt : k < ps.length + rs.length := by
        rw [← types_length ps rs]; exact (List.getElem?_eq_some_iff.1 hk).1
      obtain ⟨u, rfl⟩ : ∃ u, k = ps.length + u := ⟨k - ps.length, by omega⟩
      have hu : u < rs.length := by omega
      rw [types_getElem?_ref ps rs hu, Option.some.injEq] at hk
      subst hk
      show x _ < _
      rw [leafMap_ref pos ps rs.length start hu]
      exact hrefs _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩)
  let vs := Values.decode T y hdom
  have hcodes : ∀ k < ps.length + rs.length, vs.codes k = y k := fun k hk =>
    Values.codes_decode T y hdom k (by rw [types_length]; exact hk)
  let st := (Parameters.realize ps rs vs).1
  let ν' := (Parameters.realize ps rs vs).2
  have hobs : Inputs.observe [] ps rs { g with storage := st } ν' = vs :=
    Parameters.observe_realize ps rs hpn hr vs
  have hE := enc.correct rs hc { g with storage := st } ν'
  rw [hobs] at hE
  have hA : (enc.lower rs).holds vs.codes ↔ (enc.lower rs).holds y :=
    AFml.holds_agree _ _ _ fun i hi => hcodes i (Nat.lt_of_lt_of_le hi hw)
  have hagree : Parameters.Agree (LFml.eq a b).parameters ν' ν := by
    intro q hq
    have hq' := hps q hq
    have h1 : (Parameters.observe ps rs st ν').codes (Parameters.index q ps) = q.code ν' :=
      Parameters.codes_parameter ps q rs st ν' hq'
    have h2 : (Parameters.observe ps rs st ν').codes (Parameters.index q ps) = q.code ν := by
      have : Parameters.observe ps rs st ν' = vs := hobs
      rw [this, hcodes _ (by have := Parameters.index_lt_of_mem hq'; omega), hy q hq']
    exact (encode_val_eq_iff q.prim _ _).1 (h1.symm.trans h2)
  show (enc.lower rs).holds y ↔ _
  rw [← hA, hE, LFml.holds_agree _ (.eq a b) hagree]
  exact rf.holds_storage g ν st

namespace QArith

variable {pos : Parameter → Nat}

theorem leafRefs_mem (rs : List (Ref C)) (start : Nat) :
    ∀ r ∈ leafRefs rs start, start ≤ r.1 ∧ r.1 < start + rs.length := by
  intro r hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hr
  have := List.mem_range.1 hu
  exact ⟨Nat.le_add_right _ _, by simp only; omega⟩

/-- An equation, by the shared checked compiler, its storage scalars from
`start` on. -/
def eqn? (pos : Parameter → Nat) (start : Nat) {p : PrimTy} (a b : LTm C (.val p)) :
    Option (QArith (.eq a b) pos start) := do
  let ps := uniq (LFml.eq a b).parameters
  let enc ← StorageEncoding.ofFormula? (ps := ps) (es := []) (LFml.eq a b)
  let rf ← readFreeFormula? (LFml.eq a b)
  let rs := Layout.unique enc.refs
  if hr : rs.Nodup then
    if hc : ∀ q ∈ enc.refs, q ∈ rs then
      if hw : (enc.lower rs).width ≤ ps.length + rs.length then
        return ⟨.atom (enc.lower rs) (leafMap pos ps rs.length start), leafRefs rs start,
          start + rs.length, Nat.le_add_right _ _, leafRefs_mem rs start,
          fun g ν x hrep hrefs => eqn_correct pos start a b ps
            (fun q hq => (mem_uniq q _).2 hq) (fun q hq => (mem_uniq q _).1 hq)
            (nodup_uniq _) enc rf rs hr hc hw g ν x hrep hrefs⟩
      else none
    else none
  else none

/-- `true`. -/
def tt (pos : Parameter → Nat) (start : Nat) : QArith (LFml.tt (C := C)) pos start where
  formula := .atom .tt []
  refs := []
  next := start
  start_le := Nat.le_refl _
  refs_mem := fun _ h => nomatch h
  correct := fun _ _ _ _ _ => iff_of_true trivial trivial

/-- `¬φ`. -/
def not {φ : LFml C} {start : Nat} (A : QArith φ pos start) : QArith (.not φ) pos start :=
  ⟨.not A.formula, A.refs, A.next, A.start_le, A.refs_mem,
    fun g ν x hr hrefs => not_congr (A.correct g ν x hr hrefs)⟩

theorem refs_append {φ ψ : LFml C} {start : Nat} (A : QArith φ pos start) (B : QArith ψ pos A.next) :
    ∀ r ∈ A.refs ++ B.refs, start ≤ r.1 ∧ r.1 < B.next := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact ⟨(A.refs_mem r hr).1, Nat.lt_of_lt_of_le (A.refs_mem r hr).2 B.start_le⟩
  · exact ⟨Nat.le_trans A.start_le (B.refs_mem r hr).1, (B.refs_mem r hr).2⟩

/-- `φ ∧ ψ`. -/
def and {φ ψ : LFml C} {start : Nat} (A : QArith φ pos start) (B : QArith ψ pos A.next) :
    QArith (.and φ ψ) pos start :=
  ⟨.and A.formula B.formula, A.refs ++ B.refs, B.next, Nat.le_trans A.start_le B.start_le,
    refs_append A B, fun g ν x hr hrefs =>
      and_congr (A.correct g ν x (fun q hq => hr q (List.mem_append_left _ hq))
          (fun r h => hrefs r (List.mem_append_left _ h)))
        (B.correct g ν x (fun q hq => hr q (List.mem_append_right _ hq))
          (fun r h => hrefs r (List.mem_append_right _ h)))⟩

/-- `φ → ψ`. -/
def imp {φ ψ : LFml C} {start : Nat} (A : QArith φ pos start) (B : QArith ψ pos A.next) :
    QArith (.imp φ ψ) pos start :=
  ⟨.imp A.formula B.formula, A.refs ++ B.refs, B.next, Nat.le_trans A.start_le B.start_le,
    refs_append A B, fun g ν x hr hrefs => by
      rw [QFml.holds_imp]
      exact imp_congr (A.correct g ν x (fun q hq => hr q (List.mem_append_left _ hq))
          (fun r h => hrefs r (List.mem_append_left _ h)))
        (B.correct g ν x (fun q hq => hr q (List.mem_append_right _ hq))
          (fun r h => hrefs r (List.mem_append_right _ h)))⟩

/-- `∀ k : p. φ`: every code in range at the variable's position. -/
def all (P : List Parameter) (hinj : ∀ q ∈ P, ∀ q' ∈ P, pos q = pos q' → q = q')
    (k : Nat) (p : PrimTy) {φ : LFml C} {start : Nat} (hq : (⟨p, k⟩ : Parameter) ∈ P)
    (hfree : ∀ q ∈ φ.freeParams, q ∈ P) (hpos : ∀ q, pos q < start) (A : QArith φ pos start) :
    QArith (.all k p φ) pos start where
  formula := QFml.all (pos ⟨p, k⟩) (QFml.imp (.atom (range p 0) [pos ⟨p, k⟩]) A.formula)
  refs := A.refs
  next := A.next
  start_le := A.start_le
  refs_mem := A.refs_mem
  correct := by
    intro g ν x hrep hrefs
    rw [QFml.holds_all]
    have key : ∀ v : p.Denote, A.formula.holds (updAt x (pos ⟨p, k⟩) (encode p v).val) ↔
        φ.holds g (ν.set p k v) := by
      intro v
      apply A.correct
      · intro q hq'
        simp only [updAt]
        split
        · next he =>
          have : q = ⟨p, k⟩ := hinj q (hfree q hq') _ hq he
          subst this
          exact (congrArg (fun w => (encode p w).val) (Parameter.read_set ⟨p, k⟩ ν v)).symm
        · next he =>
          have hne : q ≠ ⟨p, k⟩ := fun e => he (e ▸ rfl)
          rw [hrep q (List.mem_filter.2 ⟨hq', by simp only [ne_eq, hne, not_false_eq_true, decide_true]⟩)]
          exact (congrArg (fun w => (encode q.prim w).val) (Parameter.read_set_ne q ⟨p, k⟩ hne ν v)).symm
      · intro r hr
        have hge := (A.refs_mem r hr).1
        have hlt := hpos ⟨p, k⟩
        simp only [updAt]
        rw [if_neg (by omega)]
        exact hrefs r hr
    constructor
    · intro h v
      have := h (encode p v).val
      rw [QFml.holds_imp] at this
      exact (key v).1 (this ((range_holds_iff p 0 _).2 (by simp only [List.getD_cons_zero, updAt, if_true]; exact (encode p v).isLt)))
    · intro h n
      rw [QFml.holds_imp]
      intro hn
      have hn' : n < bound p := by
        have := (range_holds_iff p 0 _).1 hn
        simpa only [List.getD_cons_zero, updAt, if_true] using this
      have he : (encode p (decode p ⟨n, hn'⟩)).val = n := congrArg Fin.val (encode_decode p _)
      have := (key (decode p ⟨n, hn'⟩)).2 (h _)
      rwa [he] at this

/-- **Compile a leaf** whose quantifiers' variables are among `P`, at
positions `pos` distinct on `P` and below `start`. -/
def compile (pos : Parameter → Nat) (P : List Parameter)
    (hinj : ∀ q ∈ P, ∀ q' ∈ P, pos q = pos q' → q = q') :
    (φ : LFml C) → (start : Nat) → (∀ q, pos q < start) → Option (QArith φ pos start)
  | .tt, start, _ => some (tt pos start)
  | .eq a b, start, _ => eqn? pos start a b
  | .not φ, start, h => (compile pos P hinj φ start h).map QArith.not
  | .and φ ψ, start, h => do
    let A ← compile pos P hinj φ start h
    let B ← compile pos P hinj ψ A.next (fun q => Nat.lt_of_lt_of_le (h q) A.start_le)
    return A.and B
  | .imp φ ψ, start, h => do
    let A ← compile pos P hinj φ start h
    let B ← compile pos P hinj ψ A.next (fun q => Nat.lt_of_lt_of_le (h q) A.start_le)
    return A.imp B
  | .all k p φ, start, h =>
    if hq : (⟨p, k⟩ : Parameter) ∈ P ∧ ∀ q ∈ φ.freeParams, q ∈ P then
      (compile pos P hinj φ start h).map (QArith.all P hinj k p hq.1 hq.2 h)
    else none

end QArith

/-! ## Quantified subformulas abstracted -/

/-- The Boolean atom at `k` is `true`. -/
def LFml.boolAtom (k : Nat) : LFml C := .eq (LTm.var (p := .bool) k) (LTm.lit (p := .bool) true)

theorem LFml.holds_boolAtom (g : State C []) (ν : AEnv) (k : Nat) :
    (LFml.boolAtom (C := C) k).holds g ν ↔ ν.get .bool k = true := Iff.rfl

/-- **Each quantified subformula outside binders replaced** by a fresh
Boolean atom, numbered from `n`: the formula, and the replaced
subformulas at their atoms. -/
def LFml.abstractQ : LFml C → Nat → LFml C × List (Nat × LFml C)
  | .all k p φ, n => (boolAtom n, [(n, .all k p φ)])
  | .not φ, n => ((φ.abstractQ n).1.not, (φ.abstractQ n).2)
  | .and φ ψ, n =>
    (.and (φ.abstractQ n).1 (ψ.abstractQ (n + (φ.abstractQ n).2.length)).1,
      (φ.abstractQ n).2 ++ (ψ.abstractQ (n + (φ.abstractQ n).2.length)).2)
  | .imp φ ψ, n =>
    (.imp (φ.abstractQ n).1 (ψ.abstractQ (n + (φ.abstractQ n).2.length)).1,
      (φ.abstractQ n).2 ++ (ψ.abstractQ (n + (φ.abstractQ n).2.length)).2)
  | .tt, _ => (.tt, [])
  | .eq a b, _ => (.eq a b, [])

/-- **Abstraction is exact** where each atom holds its subformula's truth. -/
theorem LFml.abstractQ_holds (g : State C []) (ν : AEnv) : ∀ (φ : LFml C) (n : Nat),
    (∀ e ∈ (φ.abstractQ n).2, (ν.get .bool e.1 = true ↔ e.2.holds g ν)) →
    ((φ.abstractQ n).1.holds g ν ↔ φ.holds g ν)
  | .all k p φ, n, h => h _ List.mem_cons_self
  | .not φ, n, h => not_congr (LFml.abstractQ_holds g ν φ n h)
  | .and φ ψ, n, h => and_congr (LFml.abstractQ_holds g ν φ n fun e he => h e (List.mem_append_left _ he))
      (LFml.abstractQ_holds g ν ψ _ fun e he => h e (List.mem_append_right _ he))
  | .imp φ ψ, n, h => imp_congr (LFml.abstractQ_holds g ν φ n fun e he => h e (List.mem_append_left _ he))
      (LFml.abstractQ_holds g ν ψ _ fun e he => h e (List.mem_append_right _ he))
  | .tt, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl

/-- The atoms are `n`, `n + 1`, …, in order. -/
theorem LFml.abstractQ_keys : ∀ (φ : LFml C) (n : Nat),
    (φ.abstractQ n).2.map Prod.fst = List.range' n (φ.abstractQ n).2.length
  | .all k p φ, n => rfl
  | .not φ, n => LFml.abstractQ_keys φ n
  | .and φ ψ, n | .imp φ ψ, n => by
    simp only [LFml.abstractQ, List.map_append, LFml.abstractQ_keys φ n,
      LFml.abstractQ_keys ψ (n + (φ.abstractQ n).2.length), List.length_append, List.range'_append_1]
  | .tt, _ => rfl
  | .eq _ _, _ => rfl

/-- The replaced subformulas read only parameters of the formula. -/
theorem LFml.abstractQ_params : ∀ (φ : LFml C) (n : Nat), ∀ e ∈ (φ.abstractQ n).2,
    ∀ q ∈ e.2.parameters, q ∈ φ.parameters
  | .all k p φ, n, e, he, q, hq => by
    rw [List.mem_singleton.1 he] at hq; exact hq
  | .not φ, n, e, he, q, hq => LFml.abstractQ_params φ n e he q hq
  | .and φ ψ, n, e, he, q, hq | .imp φ ψ, n, e, he, q, hq => by
    rcases List.mem_append.1 he with he | he
    · exact List.mem_append_left _ (LFml.abstractQ_params φ n e he q hq)
    · exact List.mem_append_right _ (LFml.abstractQ_params ψ _ e he q hq)
  | .tt, _, _, he, _, _ | .eq _ _, _, _, he, _, _ => nomatch he

/-- Every atom is read by the abstracted formula. -/
theorem LFml.abstractQ_bound : ∀ (φ : LFml C) (n : Nat), ∀ e ∈ (φ.abstractQ n).2,
    e.1 < (φ.abstractQ n).1.atomBound
  | .all k p φ, n, e, he => by
    rw [List.mem_singleton.1 he]
    show n < max (n + 1) 0
    omega
  | .not φ, n, e, he => LFml.abstractQ_bound φ n e he
  | .and φ ψ, n, e, he | .imp φ ψ, n, e, he => by
    rcases List.mem_append.1 he with he | he
    · exact Nat.lt_of_lt_of_le (LFml.abstractQ_bound φ n e he) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (LFml.abstractQ_bound ψ _ e he) (Nat.le_max_right _ _)
  | .tt, _, _, he | .eq _ _, _, _, he => nomatch he

/-- The binders of a formula. -/
def LFml.binders : LFml C → List Parameter
  | .all k p φ => ⟨p, k⟩ :: φ.binders
  | .not φ => φ.binders
  | .and φ ψ | .imp φ ψ => φ.binders ++ ψ.binders
  | .tt | .eq _ _ => []

theorem LTm.index_lt_atomBound : ∀ {s : Srt} (t : LTm C s), ∀ q ∈ t.parameters, q.index < t.atomBound := by
  intro s t
  induction t with
  | var k => intro q hq; rw [List.mem_singleton.1 hq]; exact Nat.lt_succ_self k
  | app0 | err => intro q hq; cases hq
  | app1 _ a ih | obsW a ih | obsL a ih | obsH a ih => exact ih
  | app2 _ a b iha ihb | index _ a b iha ihb | seq a b iha ihb | orElse a b iha ihb =>
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact Nat.lt_of_lt_of_le (iha q hq) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ihb q hq) (Nat.le_max_right _ _)
  | app3 _ a b c iha ihb ihc =>
    intro q hq
    simp only [LTm.parameters, List.mem_append] at hq
    simp only [LTm.atomBound]
    rcases hq with (hq | hq) | hq
    · have := iha q hq; omega
    · have := ihb q hq; omega
    · have := ihc q hq; omega
  | kite a b t e iha ihb iht ihe =>
    intro q hq
    simp only [LTm.parameters, List.mem_append] at hq
    simp only [LTm.atomBound]
    rcases hq with ((hq | hq) | hq) | hq
    · have := iha q hq; omega
    · have := ihb q hq; omega
    · have := iht q hq; omega
    · have := ihe q hq; omega

theorem LFml.index_lt_atomBound : ∀ (φ : LFml C), ∀ q ∈ φ.parameters, q.index < φ.atomBound
  | .tt, _, h => nomatch h
  | .eq a b, q, h => by
    rcases List.mem_append.1 h with h | h
    · exact Nat.lt_of_lt_of_le (LTm.index_lt_atomBound a q h) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (LTm.index_lt_atomBound b q h) (Nat.le_max_right _ _)
  | .not φ, q, h => LFml.index_lt_atomBound φ q h
  | .and φ ψ, q, h | .imp φ ψ, q, h => by
    rcases List.mem_append.1 h with h | h
    · exact Nat.lt_of_lt_of_le (LFml.index_lt_atomBound φ q h) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (LFml.index_lt_atomBound ψ q h) (Nat.le_max_right _ _)
  | .all k p φ, q, h => Nat.lt_of_lt_of_le (LFml.index_lt_atomBound φ q h) (Nat.le_max_right _ _)

end Solidity.Decide
