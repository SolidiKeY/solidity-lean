import Solidity.Calculus.QuantArithmetic
import Solidity.Calculus.DependentReduction

/-!
# Leaves with Presburger quantifiers, decided (M7, step 4)

`dependentReduction?` refuses a leaf whose body, past its universal prefix,
still has a quantifier: one in an antecedent (an `∃` of the leaf), under a
negation, or alternating with another.  `quantReduction?` takes such a
leaf when every remaining quantifier reads nothing in storage, a
Presburger quantifier over value locals:

1. the front of `dependentReduction?` (normalization, read elimination,
   folding, `LFml.prenex`, the universal prefix), the lift of the body's
   conditionals;
2. each quantified subformula `Qⱼ` outside binders replaced by a fresh
   Boolean atom `bⱼ` (`LFml.abstractQ`); the rest is the quantifier-free
   leaf `dependentReduction?` decides, flattened and compiled as there
   (`FlattenedArithmetic`);
3. each `Qⱼ` compiled to `QFml` (`QArith.compile`), at the positions of
   the main layout, with positions of their own for its other variables;
4. one quantified sentence: the domain, `bⱼ ↔ Qⱼ` for every `j`, then the
   main arithmetic; decided by `QFml.decide_iff` (`QFml.verify`).

Both answers are exact (`QuantReduction.verify`): validity of the sentence
is validity of the leaf (`bⱼ` set to `Qⱼ`'s truth), and a false
assignment gives a starting state that refutes the leaf (the flattening's
countermodel, `bⱼ` agreeing with `Qⱼ` there since `Qⱼ` reads no storage).
-/

namespace Solidity.Decide

open Linear ScalarCode ReadRealization

variable {C : Contract}

/-! ## Parameters set together -/

/-- `ν` with every parameter of `qs` set by `f`. -/
def Parameters.setAll (qs : List Parameter) (f : (q : Parameter) → q.Value) (ν : AEnv) : AEnv :=
  qs.foldr (fun q μ => q.set μ (f q)) ν

theorem Parameters.read_setAll (f : (q : Parameter) → q.Value) (ν : AEnv) (q : Parameter) :
    ∀ qs : List Parameter, q.read (Parameters.setAll qs f ν) = if q ∈ qs then f q else q.read ν
  | [] => by simp only [Parameters.setAll, List.foldr_nil, List.not_mem_nil, ↓reduceIte]
  | q' :: qs => by
    have ih := Parameters.read_setAll f ν q qs
    simp only [Parameters.setAll, List.foldr_cons] at ih ⊢
    by_cases he : q = q'
    · subst he; simp only [Parameter.read_set, List.mem_cons_self, ↓reduceIte]
    · rw [Parameter.read_set_ne q q' he, ih]
      simp only [List.mem_cons, he, false_or]

theorem Inputs.observe_set_param (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (ν : AEnv) (q : Parameter) (v : q.Value) (h : q ∉ ps) :
    Inputs.observe es ps rs g (q.set ν v) = Inputs.observe es ps rs g ν := by
  induction es with
  | nil => exact Parameters.observe_set_ne ps rs g.storage ν q v h
  | cons e es ih => exact congrArg (Prod.mk (g.envVal e)) ih

theorem Inputs.observe_setAll (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (ν : AEnv) (f : (q : Parameter) → q.Value) :
    ∀ qs : List Parameter, (∀ q ∈ qs, q ∉ ps) →
      Inputs.observe es ps rs g (Parameters.setAll qs f ν) = Inputs.observe es ps rs g ν
  | [], _ => rfl
  | q :: qs, h => by
    show Inputs.observe es ps rs g (q.set (Parameters.setAll qs f ν) (f q)) = _
    rw [Inputs.observe_set_param es ps rs g _ q _ (h q List.mem_cons_self),
      Inputs.observe_setAll es ps rs g ν f qs fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

theorem Inputs.types_length' (ps : List Parameter) (rs : List (Ref C)) :
    ∀ es : List EnvKey, (Inputs.types es ps rs).length = es.length + (ps.length + rs.length)
  | [] => by
    simp only [Inputs.types, Parameters.types, Layout.types, List.length_append, List.length_map,
      List.length_nil, Nat.zero_add]
  | _ :: es => by
    simp only [Inputs.types, List.length_cons, Inputs.types_length' ps rs es]
    omega

theorem Inputs.codes_param (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (ν : AEnv) (q : Parameter) (h : q ∈ ps) :
    (Inputs.observe es ps rs g ν).codes (es.length + Parameters.index q ps) = q.code ν := by
  rw [Inputs.codes_tail]
  exact Parameters.codes_parameter ps q rs g.storage ν h

theorem Parameters.index_inj {q q' : Parameter} {ps : List Parameter} (hq : q ∈ ps) (hq' : q' ∈ ps)
    (h : Parameters.index q ps = Parameters.index q' ps) : q = q' := by
  have e1 := Parameters.getElem_index hq
  have e2 := Parameters.getElem_index hq'
  simp only [h] at e1
  exact e1.symm.trans e2

/-! ## Positions -/

/-- The variables of the quantified sentence: the main layout's `W`
inputs (environment, parameters `ps`, storage), then the `extras`. -/
structure QLayout where
  es : List EnvKey
  ps : List Parameter
  W : Nat
  extras : List Parameter

namespace QLayout

/-- A parameter's position. -/
def pos (L : QLayout) (q : Parameter) : Nat :=
  if q ∈ L.ps then L.es.length + Parameters.index q L.ps
  else if q ∈ L.extras then L.W + Parameters.index q L.extras else 0

/-- Every parameter with a position. -/
def P (L : QLayout) : List Parameter := L.ps ++ L.extras

/-- The first position past the parameters'. -/
def top (L : QLayout) : Nat := L.W + L.extras.length + 1

theorem pos_lt (L : QLayout) (hW : L.es.length + L.ps.length ≤ L.W) (q : Parameter) : L.pos q < L.top := by
  unfold pos top
  by_cases h1 : q ∈ L.ps
  · have := Parameters.index_lt_of_mem h1
    simp only [h1, ↓reduceIte]; omega
  · by_cases h2 : q ∈ L.extras
    · have := Parameters.index_lt_of_mem h2
      simp only [h1, h2, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; omega

theorem pos_inj (L : QLayout) (hW : L.es.length + L.ps.length ≤ L.W) (hd : ∀ q ∈ L.extras, q ∉ L.ps) :
    ∀ q ∈ L.P, ∀ q' ∈ L.P, L.pos q = L.pos q' → q = q' := by
  intro q hq q' hq' h
  unfold pos at h
  by_cases h1 : q ∈ L.ps <;> by_cases h2 : q' ∈ L.ps
  · simp only [h1, h2, ↓reduceIte, Nat.add_left_cancel_iff] at h
    exact Parameters.index_inj h1 h2 h
  · have he2 : q' ∈ L.extras := (List.mem_append.1 hq').resolve_left h2
    simp only [h1, h2, he2, ↓reduceIte] at h
    have := Parameters.index_lt_of_mem h1; omega
  · have he1 : q ∈ L.extras := (List.mem_append.1 hq).resolve_left h1
    simp only [h1, h2, he1, ↓reduceIte] at h
    have := Parameters.index_lt_of_mem h2; omega
  · have he1 : q ∈ L.extras := (List.mem_append.1 hq).resolve_left h1
    have he2 : q' ∈ L.extras := (List.mem_append.1 hq').resolve_left h2
    simp only [h1, h2, he1, he2, ↓reduceIte, Nat.add_left_cancel_iff] at h
    exact Parameters.index_inj he1 he2 h

end QLayout

/-! ## The definitions `bⱼ ↔ Qⱼ` -/

/-- `x i = 1`. -/
def QFml.isOne (i : Nat) : QFml := .atom (.eq [1] 1) [i]

theorem QFml.holds_isOne (i : Nat) (x : Nat → Nat) : (QFml.isOne i).holds x ↔ x i = 1 := by
  simp only [QFml.isOne, QFml.holds, AFml.holds, Lin.eval, List.getD_cons_zero, Int.one_mul, Int.add_zero]
  omega

/-- `φ ↔ ψ`. -/
def QFml.iff (s t : QFml) : QFml := .and (.imp s t) (.imp t s)

theorem QFml.holds_iff (s t : QFml) (x : Nat → Nat) : (QFml.iff s t).holds x ↔ (s.holds x ↔ t.holds x) := by
  simp only [QFml.iff, QFml.holds, QFml.holds_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **The compiled definitions** of the abstracted atoms. -/
structure QDefs (es : List (Nat × LFml C)) (pos : Parameter → Nat) (start : Nat) where
  formula : QFml
  refs : List (Nat × PrimTy)
  next : Nat
  start_le : start ≤ next
  refs_mem : ∀ r ∈ refs, start ≤ r.1 ∧ r.1 < next
  correct : ∀ (g : State C []) (ν : AEnv) (x : Nat → Nat), (∀ e ∈ es, Rep pos e.2.freeParams ν x) →
    (∀ r ∈ refs, x r.1 < bound r.2) →
    (formula.holds x ↔ ∀ e ∈ es, (x (pos ⟨.bool, e.1⟩) = 1 ↔ e.2.holds g ν))

namespace QDefs

/-- Compile every definition. -/
def compile (pos : Parameter → Nat) (P : List Parameter)
    (hinj : ∀ q ∈ P, ∀ q' ∈ P, pos q = pos q' → q = q') :
    (es : List (Nat × LFml C)) → (start : Nat) → (∀ q, pos q < start) → Option (QDefs es pos start)
  | [], start, _ => some
      { formula := .atom .tt []
        refs := []
        next := start
        start_le := Nat.le_refl _
        refs_mem := fun _ h => nomatch h
        correct := fun _ _ _ _ _ => iff_of_true trivial fun _ h => nomatch h }
  | e :: es, start, h => do
    let A ← QArith.compile pos P hinj e.2 start h
    let D ← compile pos P hinj es A.next (fun q => Nat.lt_of_lt_of_le (h q) A.start_le)
    return ⟨.and (QFml.iff (QFml.isOne (pos ⟨.bool, e.1⟩)) A.formula) D.formula, A.refs ++ D.refs, D.next,
      Nat.le_trans A.start_le D.start_le,
      fun r hr => by
        rcases List.mem_append.1 hr with hr | hr
        · exact ⟨(A.refs_mem r hr).1, Nat.lt_of_lt_of_le (A.refs_mem r hr).2 D.start_le⟩
        · exact ⟨Nat.le_trans A.start_le (D.refs_mem r hr).1, (D.refs_mem r hr).2⟩,
      fun g ν x hrep hrefs => by
        rw [QFml.holds, QFml.holds_iff, QFml.holds_isOne,
          A.correct g ν x (hrep e List.mem_cons_self) (fun r hr => hrefs r (List.mem_append_left _ hr)),
          D.correct g ν x (fun e' he' => hrep e' (List.mem_cons_of_mem _ he'))
            (fun r hr => hrefs r (List.mem_append_right _ hr))]
        simp only [List.mem_cons, forall_eq_or_imp]⟩

end QDefs

/-! ## The reduction -/

/-- The lifted body, its quantified subformulas abstracted. -/
def abstracted (B : LFml C) : LFml C × List (Nat × LFml C) :=
  (B.liftCond condLiftFuel).abstractQ (B.liftCond condLiftFuel).atomBound

/-- The parameters the abstracted subformulas name. -/
def quantParams (Qs : List (Nat × LFml C)) : List Parameter :=
  Qs.flatMap fun e => ⟨.bool, e.1⟩ :: (e.2.parameters ++ e.2.binders)

/-- The parameters the abstracted subformulas read free, and their atoms. -/
def freeQ (Qs : List (Nat × LFml C)) : List Parameter :=
  Qs.flatMap fun e => ⟨.bool, e.1⟩ :: e.2.freeParams

theorem freeQ_sub (Qs : List (Nat × LFml C)) : ∀ q ∈ freeQ Qs, q ∈ quantParams Qs := by
  intro q hq
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.1 hq
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  rcases List.mem_cons.1 hq with rfl | hq
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (LFml.freeParams_sub e.2 q hq))

/-- The sentence's variables, from the main layout. -/
def layoutOf {L : LFml C} (M : FlattenedArithmetic L) (Qs : List (Nat × LFml C)) : QLayout where
  es := M.encoding.environment
  ps := M.encoding.parameters
  W := (Inputs.types M.encoding.environment M.encoding.parameters M.encoding.refs).length
  extras := (uniq (quantParams Qs)).filter (· ∉ M.encoding.parameters)

theorem layoutOf_W {L : LFml C} (M : FlattenedArithmetic L) (Qs : List (Nat × LFml C)) :
    (layoutOf M Qs).es.length + (layoutOf M Qs).ps.length ≤ (layoutOf M Qs).W := by
  simp only [layoutOf, Inputs.types_length']
  omega

theorem layoutOf_extras {L : LFml C} (M : FlattenedArithmetic L) (Qs : List (Nat × LFml C)) :
    ∀ q ∈ (layoutOf M Qs).extras, q ∉ (layoutOf M Qs).ps := by
  intro q hq
  simpa only [layoutOf, decide_eq_true_eq] using (List.mem_filter.1 hq).2

theorem layoutOf_P {L : LFml C} (M : FlattenedArithmetic L) (Qs : List (Nat × LFml C)) :
    ∀ q ∈ quantParams Qs, q ∈ (layoutOf M Qs).P := by
  intro q hq
  by_cases h : q ∈ M.encoding.parameters
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_filter.2 ⟨(mem_uniq q _).2 hq,
      by simp only [h, not_false_eq_true, decide_true]⟩)

/-- Conjunction of a list. -/
def QFml.conj : List QFml → QFml
  | [] => .atom .tt []
  | s :: ss => .and s (QFml.conj ss)

theorem QFml.holds_conj (x : Nat → Nat) : ∀ ss : List QFml, (QFml.conj ss).holds x ↔ ∀ s ∈ ss, s.holds x
  | [] => iff_of_true trivial fun _ h => nomatch h
  | s :: ss => by
    simp only [QFml.conj, QFml.holds, QFml.holds_conj x ss, List.mem_cons, forall_eq_or_imp]

/-- `x i < bound p`. -/
def QFml.inRange (i : Nat) (p : PrimTy) : QFml := .atom (range p 0) [i]

theorem QFml.holds_inRange (i : Nat) (p : PrimTy) (x : Nat → Nat) :
    (QFml.inRange i p).holds x ↔ x i < bound p :=
  range_holds_iff p 0 _

theorem QFml.holds_atom_range (F : AFml) (W : Nat) (hw : F.width ≤ W) (x : Nat → Nat) :
    (QFml.atom F (List.range W)).holds x ↔ F.holds x := by
  apply AFml.holds_agree
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_range (Nat.lt_of_lt_of_le hi hw)]
  rfl

/-- **A leaf whose remaining quantifiers are Presburger quantifiers**,
reduced to one quantified linear sentence. -/
structure QuantReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  sentence : UniversalPrefix source.leaf.elim.condSimp.prenex
  covered : ∀ q ∈ sentence.body.freeParams, q ∈ sentence.parameters
  main : FlattenedArithmetic (abstracted sentence.body).1
  defs : QDefs (abstracted sentence.body).2 (layoutOf main (abstracted sentence.body).2).pos
    (layoutOf main (abstracted sentence.body).2).top

namespace QuantReduction

variable {φ : Fml C []} (r : QuantReduction φ)

/-- The main layout and the abstracted subformulas. -/
abbrev L : QLayout := layoutOf r.main (abstracted r.sentence.body).2
abbrev Qs : List (Nat × LFml C) := (abstracted r.sentence.body).2
abbrev A : TypedFormula (Inputs.types r.main.encoding.environment r.main.encoding.parameters
    r.main.encoding.refs) := r.main.encoding.arithmetic

/-- The domain of every variable. -/
def domainF : QFml :=
  .and (.atom (domain (Inputs.types r.main.encoding.environment r.main.encoding.parameters
      r.main.encoding.refs)) (List.range r.L.W))
    (.and (QFml.conj ((r.L.extras.filter (· ∈ freeQ r.Qs)).map fun q => QFml.inRange (r.L.pos q) q.prim))
      (QFml.conj (r.defs.refs.map fun e => QFml.inRange e.1 e.2)))

/-- **The sentence**: the domain and the definitions imply the main
arithmetic. -/
def sentenceF : QFml := QFml.imp r.domainF (QFml.imp r.defs.formula (.atom r.A.formula (List.range r.L.W)))

theorem holds_atom_domain (T : List PrimTy) (x : Nat → Nat) :
    (QFml.atom (domain T) (List.range T.length)).holds x ↔ (domain T).holds x := by
  show (domain T).holds _ ↔ _
  rw [domain, domainFrom_iff, domainFrom_iff]
  refine forall_congr' fun k => forall_congr' fun p => imp_congr_right fun hk => ?_
  have hk' : k < T.length := (List.getElem?_eq_some_iff.1 hk).1
  rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_range hk']
  rfl

theorem bound_pos (p : PrimTy) : 0 < ScalarCode.bound p := by
  cases p <;> simp only [ScalarCode.bound] <;> omega

theorem code_bool (ν : AEnv) (k : Nat) :
    (Parameter.code ⟨.bool, k⟩ ν = 1) ↔ ν.get .bool k = true := by
  simp only [Parameter.code, Parameter.read, encode]
  have : ∀ b : Bool, ((if b = true then 1 else 0) = 1 ↔ b = true) := by decide
  exact this _

/-- The keys of the abstraction are at least its start, and distinct. -/
theorem keys_spec (B : LFml C) (n : Nat) :
    (∀ e ∈ (B.abstractQ n).2, n ≤ e.1) ∧ ((B.abstractQ n).2.map Prod.fst).Nodup := by
  have h := LFml.abstractQ_keys B n
  refine ⟨fun e he => ?_, ?_⟩
  · have : e.1 ∈ (B.abstractQ n).2.map Prod.fst := List.mem_map.2 ⟨e, he, rfl⟩
    rw [h, List.mem_range'_1] at this
    exact this.1
  · rw [h]; exact List.nodup_range'

theorem nodup_map_inj {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | c :: l, hn, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · exact ha'.trans hb'.symm
    · subst ha'; exact (hn.1 (by rw [he]; exact List.mem_map.2 ⟨b, hb', rfl⟩)).elim
    · subst hb'; exact (hn.1 (by rw [← he]; exact List.mem_map.2 ⟨a, ha', rfl⟩)).elim
    · exact nodup_map_inj hn.2 ha' hb' he

/-- `x`'s values at positions: the main layout's codes below `W`, the
extras' codes past it. -/
def assignmentOf (L : QLayout) (main : Nat → Nat) (ν : AEnv) : Nat → Nat := fun i =>
  if i < L.W then main i
  else match L.extras[i - L.W]? with
    | some q => q.code ν
    | none => 0

theorem assignmentOf_rep (L : QLayout) (hW : L.es.length + L.ps.length ≤ L.W)
    (main : Nat → Nat) (ν : AEnv)
    (hmain : ∀ q ∈ L.ps, main (L.es.length + Parameters.index q L.ps) = q.code ν) :
    ∀ q ∈ L.P, assignmentOf L main ν (L.pos q) = q.code ν := by
  intro q hq
  by_cases h1 : q ∈ L.ps
  · have := Parameters.index_lt_of_mem h1
    simp only [assignmentOf, QLayout.pos, h1, ↓reduceIte, show L.es.length + Parameters.index q L.ps < L.W by omega]
    exact hmain q h1
  · have h2 : q ∈ L.extras := (List.mem_append.1 hq).resolve_left h1
    have hl := Parameters.index_lt_of_mem h2
    simp only [assignmentOf, QLayout.pos, h1, h2, ↓reduceIte, show ¬ L.W + Parameters.index q L.extras < L.W by omega,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hl, Parameters.getElem_index h2]

theorem assignmentOf_top (L : QLayout) (main : Nat → Nat) (ν : AEnv) (i : Nat) (h : L.top ≤ i) :
    assignmentOf L main ν i = 0 := by
  simp only [QLayout.top] at h
  simp only [assignmentOf, show ¬ i < L.W by omega, ↓reduceIte,
    List.getElem?_eq_none (show L.extras.length ≤ i - L.W by omega)]

/-- **A valid sentence makes the body valid.** -/
theorem body_of_sentence (h : r.sentenceF.Valid) (g : State C []) (ν' : AEnv) :
    r.sentence.body.holds g ν' := by
  let L0 := r.sentence.body.liftCond condLiftFuel
  let n := L0.atomBound
  have hQs : r.Qs = (L0.abstractQ n).2 := rfl
  obtain ⟨hkge, hknd⟩ := keys_spec L0 n
  let ν1 : AEnv := { ν' with b := fun j =>
    if n ≤ j then (@decide (∃ e ∈ r.Qs, e.1 = j ∧ e.2.holds g ν') (Classical.propDecidable _)) else ν'.b j }
  have hagree1 : ∀ q : Parameter, q.index < n → q.read ν1 = q.read ν' := by
    intro q hq
    obtain ⟨p, k⟩ := q
    cases p <;> simp only [Parameter.read, AEnv.get, ν1] <;> simp only at hq <;>
      simp only [show ¬ n ≤ k by omega, ↓reduceIte]
  have hQparams : ∀ e ∈ r.Qs, ∀ q ∈ e.2.parameters, q.index < n := fun e he q hq =>
    LFml.index_lt_atomBound L0 q (LFml.abstractQ_params L0 n e he q hq)
  have hQ1 : ∀ e ∈ r.Qs, (e.2.holds g ν1 ↔ e.2.holds g ν') := fun e he =>
    LFml.holds_agree g e.2 fun q hq => hagree1 q (hQparams e he q hq)
  have hkey : ∀ e ∈ r.Qs, (ν1.get .bool e.1 = true ↔ e.2.holds g ν') := by
    intro e he
    have hv : ν1.get .bool e.1 =
        (@decide (∃ e' ∈ r.Qs, e'.1 = e.1 ∧ e'.2.holds g ν') (Classical.propDecidable _)) := by
      simp only [ν1, AEnv.get, if_pos (hkge e he)]
    rw [hv, @decide_eq_true_eq _ (Classical.propDecidable _)]
    constructor
    · rintro ⟨e', he', hk, hh⟩
      have : e' = e := nodup_map_inj hknd he' he hk
      exact this ▸ hh
    · exact fun hh => ⟨e, he, rfl, hh⟩
  have hL0 : L0.holds g ν1 ↔ r.sentence.body.holds g ν' :=
    (LFml.holds_agree g L0 fun q hq => hagree1 q (LFml.index_lt_atomBound L0 q hq)).trans
      (LFml.liftCond_holds g _ _ ν')
  have hhat : (abstracted r.sentence.body).1.holds g ν1 ↔ L0.holds g ν1 :=
    LFml.abstractQ_holds g ν1 L0 n fun e he => (hkey e he).trans (hQ1 e he).symm
  let fl := r.main.flattening
  let ν2 := fl.layout.fill g ν1
  have hfill : fl.flat.formula.holds g ν2 ↔ (abstracted r.sentence.body).1.holds g ν1 := fl.fill_iff g ν1
  have hcons : (ReadOccurrence.constraints fl.flat.reads).holds g ν2 :=
    (fl.layout.constraints_iff g ν2).2 (fl.layout.entries_consistent g ν2 (fl.layout.fill_interpreted g ν1))
  have hagree2 : ν1.AgreesBelow (abstracted r.sentence.body).1.atomBound ν2 := fl.layout.fill_agrees g ν1
  have hQ2 : ∀ e ∈ r.Qs, (e.2.holds g ν2 ↔ e.2.holds g ν1) := fun e he =>
    LFml.holds_agree g e.2 fun q hq => (hagree2 q.prim q.index (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (hQparams e he q hq) (hkge e he))
      (Nat.le_of_lt (LFml.abstractQ_bound L0 n e he)))).symm
  have hkey2 : ∀ e ∈ r.Qs, ν2.get .bool e.1 = ν1.get .bool e.1 := fun e he =>
    (hagree2 .bool e.1 (LFml.abstractQ_bound L0 n e he)).symm
  let obs := Inputs.observe r.main.encoding.environment r.main.encoding.parameters r.main.encoding.refs g ν2
  let x := assignmentOf r.L obs.codes ν2
  have hW := layoutOf_W r.main r.Qs
  have hrep : ∀ q ∈ r.L.P, x (r.L.pos q) = q.code ν2 :=
    assignmentOf_rep r.L hW obs.codes ν2 fun q hq => Inputs.codes_param _ _ _ g ν2 q hq
  have hlow : ∀ i < r.L.W, x i = obs.codes i := fun i hi => by simp only [x, assignmentOf, hi, ↓reduceIte]
  have hx0 : ∀ i, r.L.top ≤ i → x i = 0 := fun i hi => assignmentOf_top _ _ _ _ hi
  have hs := h x
  simp only [sentenceF, QFml.holds_imp] at hs
  have hdom : r.domainF.holds x := by
    refine ⟨?_, ?_, ?_⟩
    · show (QFml.atom _ (List.range (Inputs.types _ _ _).length)).holds x
      rw [holds_atom_domain]
      have := domain_codes obs
      rw [domain, domainFrom_iff] at this ⊢
      intro k p hk
      have hk' : k < r.L.W := (List.getElem?_eq_some_iff.1 hk).1
      have h' := this k p hk
      simp only [Nat.zero_add] at h' ⊢
      rw [hlow k hk']
      exact h'
    · rw [QFml.holds_conj]
      intro s hs'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hs'
      rw [QFml.holds_inRange, hrep q (List.mem_append_right _ (List.mem_filter.1 hq).1)]
      exact (encode _ _).isLt
    · rw [QFml.holds_conj]
      intro s hs'
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs'
      rw [QFml.holds_inRange, hx0 _ (r.defs.refs_mem e he).1]
      exact bound_pos _
  have hrepQ : ∀ e ∈ r.Qs, Rep r.L.pos e.2.freeParams ν2 x := fun e he q hq =>
    hrep q (layoutOf_P r.main r.Qs q (List.mem_flatMap.2 ⟨e, he, List.mem_cons_of_mem _
      (List.mem_append_left _ (LFml.freeParams_sub e.2 q hq))⟩))
  have hrefs : ∀ e ∈ r.defs.refs, x e.1 < bound e.2 := fun e he => by
    rw [hx0 _ (r.defs.refs_mem e he).1]; exact bound_pos _
  have hdefs : r.defs.formula.holds x := by
    rw [r.defs.correct g ν2 x hrepQ hrefs]
    intro e he
    rw [hrep _ (layoutOf_P r.main r.Qs _ (List.mem_flatMap.2 ⟨e, he, List.mem_cons_self⟩)), code_bool,
      hkey2 e he, hkey e he, hQ2 e he, hQ1 e he]
  have hA := hs hdom hdefs
  rw [QFml.holds_atom_range r.A.formula r.L.W r.A.width] at hA
  have hA' : r.A.holds obs := (AFml.holds_agree _ _ _ fun i hi =>
    hlow i (Nat.lt_of_lt_of_le hi r.A.width)).1 hA
  have hflat := (r.main.encoding.correct g ν2).1 hA' hcons
  exact hL0.1 (hhat.1 (hfill.1 hflat))

/-- **A valid sentence makes the leaf valid.** -/
theorem valid_of_sentence (h : r.sentenceF.Valid) : Fml.Valid φ := fun g =>
  (r.normalization.correct g).mp ((r.source.elim_holds_iff g).mp ((LFml.condSimp_holds g _ _).mp
    ((LFml.prenex_holds g _ _).mp (r.sentence.close g AEnv.dflt (r.body_of_sentence h g)))))

/-- The value of an extra parameter, read from `x`. -/
def extraValue (L : QLayout) (x : Nat → Nat) (q : Parameter) : q.Value :=
  (decode? q.prim (x (L.pos q))).getD (PrimTy.dflt q.prim)

/-- **A false assignment gives a refuting state**: the main layout's
values realized, the extras read from the assignment, the flattening's
countermodel; its definitions make each atom agree with its subformula. -/
def countermodelOf (x : Nat → Nat) (hx : ¬ r.sentenceF.holds x) : {σ : State C [] // ¬ holds σ φ} := by
  have hx' : r.domainF.holds x ∧ r.defs.formula.holds x ∧
      ¬ (QFml.atom r.A.formula (List.range r.L.W)).holds x := by
    simp only [sentenceF, QFml.holds_imp] at hx
    exact Classical.byContradiction fun h => hx fun h1 h2 =>
      Classical.byContradiction fun h3 => h ⟨h1, h2, h3⟩
  have hdomM : (domain (Inputs.types r.main.encoding.environment r.main.encoding.parameters
      r.main.encoding.refs)).holds x := (holds_atom_domain _ x).1 hx'.1.1
  let vs := Values.decode _ x hdomM
  let gM := (Inputs.realize r.main.encoding.environment r.main.encoding.parameters r.main.encoding.refs vs).1
  let νM := (Inputs.realize r.main.encoding.environment r.main.encoding.parameters r.main.encoding.refs vs).2
  let ν := Parameters.setAll r.L.extras (extraValue r.L x) νM
  have hobs : Inputs.observe r.main.encoding.environment r.main.encoding.parameters r.main.encoding.refs
      gM ν = vs :=
    (Inputs.observe_setAll _ _ _ gM νM _ r.L.extras (layoutOf_extras r.main r.Qs)).trans
      (Inputs.observe_realize _ _ _ r.main.encoding.distinctEnvironment r.main.encoding.distinctParameters
        r.main.encoding.distinctRefs vs)
  have hcodes : ∀ i < r.L.W, vs.codes i = x i := fun i hi => Values.codes_decode _ x hdomM i hi
  have hnA : ¬ r.A.holds vs := fun h => hx'.2.2 ((QFml.holds_atom_range r.A.formula r.L.W r.A.width x).2
    ((AFml.holds_agree _ _ _ fun i hi => hcodes i (Nat.lt_of_lt_of_le hi r.A.width)).1 h))
  have hflat : ¬ r.main.flattening.formula.holds gM ν := fun h =>
    hnA (hobs ▸ (r.main.encoding.correct gM ν).2 h)
  have hc : (ReadOccurrence.constraints r.main.flattening.flat.reads).holds gM ν :=
    Classical.byContradiction fun h => hflat fun hh => (h hh).elim
  have hf : ¬ r.main.flattening.flat.formula.holds gM ν := fun h => hflat fun _ => h
  let st := r.main.flattening.countermodel gM ν ((r.main.flattening.layout.constraints_iff gM ν).1 hc) hf
  refine ⟨st.1, fun hφ => ?_⟩
  have hW : r.L.es.length + r.L.ps.length ≤ r.L.W := layoutOf_W r.main r.Qs
  have hrep : ∀ q ∈ freeQ r.Qs, x (r.L.pos q) = q.code ν := by
    intro q hqf
    have hq := layoutOf_P r.main r.Qs q (freeQ_sub r.Qs q hqf)
    by_cases h1 : q ∈ r.L.ps
    · have hl := Parameters.index_lt_of_mem h1
      have hp : r.L.pos q = r.L.es.length + Parameters.index q r.L.ps := by
        simp only [QLayout.pos, h1, ↓reduceIte]
      rw [hp, ← hcodes _ (by omega)]
      have := Inputs.codes_param r.main.encoding.environment r.main.encoding.parameters
        r.main.encoding.refs gM ν q h1
      rw [hobs] at this
      exact this
    · have h2 : q ∈ r.L.extras := (List.mem_append.1 hq).resolve_left h1
      have hin : x (r.L.pos q) < ScalarCode.bound q.prim := by
        have := (QFml.holds_conj x _).1 hx'.1.2.1 _ (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨h2,
          by simp only [hqf, decide_true]⟩, rfl⟩)
        exact (QFml.holds_inRange _ _ x).1 this
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((decode?_isSome q.prim _).2 hin)
      have hread : q.read ν = v := by
        rw [Parameters.read_setAll, if_pos h2]
        simp only [extraValue, hv, Option.getD_some]
      simp only [Parameter.code, hread]
      exact (encode_of_decode? _ _ v hv).symm
  have hrefs : ∀ e ∈ r.defs.refs, x e.1 < ScalarCode.bound e.2 := fun e he =>
    (QFml.holds_inRange _ _ x).1 ((QFml.holds_conj x _).1 hx'.1.2.2 _ (List.mem_map.2 ⟨e, he, rfl⟩))
  have hrepQ : ∀ e ∈ r.Qs, Rep r.L.pos e.2.freeParams ν x := fun e he q hq =>
    hrep q (List.mem_flatMap.2 ⟨e, he, List.mem_cons_of_mem _ hq⟩)
  have hdefs := (r.defs.correct st.1 ν x hrepQ hrefs).1 hx'.2.1
  have hkey : ∀ e ∈ r.Qs, (ν.get .bool e.1 = true ↔ e.2.holds st.1 ν) := fun e he => by
    rw [← code_bool, ← hrep _ (List.mem_flatMap.2 ⟨e, he, List.mem_cons_self⟩)]
    exact hdefs e he
  let L0 := r.sentence.body.liftCond condLiftFuel
  have hL0 : ¬ L0.holds st.1 ν := fun h =>
    st.2 ((LFml.abstractQ_holds st.1 ν L0 L0.atomBound hkey).2 h)
  have hB : ¬ r.sentence.body.holds st.1 ν := fun h => hL0 ((LFml.liftCond_holds st.1 _ _ ν).2 h)
  have hinst := r.sentence.instantiate st.1 AEnv.dflt ν ((LFml.prenex_holds _ _ _).mpr
    ((LFml.condSimp_holds _ _ _).mpr ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr hφ))))
  refine hB ((LFml.holds_agree_free st.1 _ fun q hq => ?_).1 hinst)
  rw [Parameters.read_assign, if_pos (r.covered q hq)]

/-- **Proof or refutation**, from one traversal of the sentence's
automaton. -/
def verify : Sum (PLift (Fml.Valid φ)) {σ : State C [] // ¬ holds σ φ} :=
  match r.sentenceF.verify with
  | .inl h => .inl ⟨r.valid_of_sentence h.down⟩
  | .inr cm => .inr (r.countermodelOf cm.1 cm.2)

end QuantReduction

/-- **The reduction of a leaf with Presburger quantifiers.** -/
def quantReduction? (φ : Fml C []) : Option (QuantReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  let sentence ← UniversalPrefix.ofFormula? 1024 r.leaf.elim.condSimp.prenex
  if hc : ∀ q ∈ sentence.body.freeParams, q ∈ sentence.parameters then
    if (sentence.body.liftCondB condLiftFuel liftBudget).isNone then none
    else
      let M ← flattenedArithmetic? 2048 (abstracted sentence.body).1
      let L := layoutOf M (abstracted sentence.body).2
      let D ← QDefs.compile L.pos L.P (L.pos_inj (layoutOf_W M _) (layoutOf_extras M _))
        (abstracted sentence.body).2 L.top (L.pos_lt (layoutOf_W M _))
      return ⟨d, r, sentence, hc, M, D⟩
  else none

end Solidity.Decide
