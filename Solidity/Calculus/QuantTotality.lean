import Solidity.Calculus.QuantReduction
import Solidity.Calculus.AutoComplete

/-!
# The quantified reduction never refuses its fragment (M7, step 4)

`Fml.quantCovered` is the fragment `quantReduction?` is proved total on:
the eliminated leaf (`leafOf?`) has a universal prefix binding its free
parameters; its lifted body, quantified subformulas abstracted, is in the
quantifier-free fragment of `Fml.Covered` (`LFml.Src false`, the size
bounds on its cut, `LFml.cutAll`); and each abstracted subformula is a Presburger formula
(`LFml.qfrag`): `¬`, `∧`, `→`, `∀` over equations of the checked
compiler's scalar or Boolean terms over value locals and literals
(`LTm.Num`, `LTm.BoolV`: `+`, `-`, products by a literal, comparisons,
`seq`, a failed term; no transaction field, no storage).  The fragment
asks no quantifier to be left: a quantifier-free body passes too.
-/

namespace Solidity.Decide

open Linear ScalarCode ReadRealization

variable {C : Contract}

/-! ## Recognizing Presburger terms -/

/-- A product with a literal factor of scalar terms, with its evidence. -/
def LTm.mulNum? {P : Parameter → Prop} {E : EnvKey → Prop} {p : PrimTy}
    (h : BinOp.mul.accepts p = true) (a b : LTm C (.val p))
    (sa : Option (PLift (a.Num P E))) (sb : Option (PLift (b.Num P E))) :
    Option (PLift ((LTm.app2 (.binop .mul h) a b).Num P E)) :=
  match a.lit?, b.lit? with
  | some ⟨v, hv⟩, _ => sb.map fun ⟨hb⟩ => ⟨by subst hv; exact .mulL h v hb⟩
  | none, some ⟨v, hv⟩ => sa.map fun ⟨ha⟩ => ⟨by subst hv; exact .mulR h v ha⟩
  | none, none => none

/-- `LTm.Num` at a value sort, `False` elsewhere. -/
def LTm.NumS (P : Parameter → Prop) (E : EnvKey → Prop) : {s : Srt} → LTm C s → Prop
  | .val _, t => t.Num P E
  | _, _ => False

/-- The scalar terms of value locals `ps` and literals, with evidence. -/
def LTm.num? (ps : List Parameter) : {s : Srt} → (t : LTm C s) →
    Option (PLift (t.NumS (· ∈ ps) (· ∈ ([] : List EnvKey))))
  | _, .var (p := p) k => if h : (⟨p, k⟩ : Parameter) ∈ ps then some ⟨.var k h⟩ else none
  | _, .app0 o =>
    match o with
    | .lit v => some ⟨.lit v⟩
    | _ => none
  | s, .err =>
    match s with
    | .val _ => some ⟨.err⟩
    | _ => none
  | _, .app2 (.binop op (p := p) h) a b =>
    match op with
    | .add => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.add h ha hb⟩
    | .sub => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.sub h ha hb⟩
    | .mul => LTm.mulNum? h a b ((LTm.num? ps a).map fun ⟨h⟩ => ⟨h⟩) ((LTm.num? ps b).map fun ⟨h⟩ => ⟨h⟩)
    | _ => none
  | s, .seq (s' := s') d a =>
    match s', s with
    | .val _, .val _ => do
      let ⟨hd⟩ ← LTm.num? ps d
      let ⟨ha⟩ ← LTm.num? ps a
      return ⟨.seq hd ha⟩
    | _, _ => none
  | _, _ => none

/-- `LTm.BoolV` at the Boolean sort, `False` elsewhere. -/
def LTm.BoolS (P : Parameter → Prop) (E : EnvKey → Prop) : {s : Srt} → LTm C s → Prop
  | .val .bool, t => t.BoolV P E
  | _, _ => False

/-- The Boolean terms of value locals `ps` and literals, with evidence. -/
def LTm.bool? (ps : List Parameter) : {s : Srt} → (t : LTm C s) →
    Option (PLift (t.BoolS (· ∈ ps) (· ∈ ([] : List EnvKey))))
  | _, .var (p := p) k =>
    match p with
    | .bool => if h : (⟨.bool, k⟩ : Parameter) ∈ ps then some ⟨.var k h⟩ else none
    | _ => none
  | _, .app0 o =>
    match o with
    | .lit (p := .bool) v => some ⟨.lit v⟩
    | _ => none
  | s, .err =>
    match s with
    | .val .bool => some ⟨.err⟩
    | _ => none
  | _, .app1 (.unop op (p := p) _) a =>
    match op, p with
    | .not, .bool => (LTm.bool? ps a).map fun ⟨h⟩ => ⟨.not h⟩
    | _, _ => none
  | _, .app2 (.binop op (p := p) h) a b =>
    match op, p with
    | .and, .bool => do
      let ⟨ha⟩ ← LTm.bool? ps a
      let ⟨hb⟩ ← LTm.bool? ps b
      return ⟨.and ha hb⟩
    | .or, .bool => do
      let ⟨ha⟩ ← LTm.bool? ps a
      let ⟨hb⟩ ← LTm.bool? ps b
      return ⟨.or ha hb⟩
    | .eqB, .bool => do
      let ⟨ha⟩ ← LTm.bool? ps a
      let ⟨hb⟩ ← LTm.bool? ps b
      return ⟨.eqB ha hb⟩
    | .neB, .bool => do
      let ⟨ha⟩ ← LTm.bool? ps a
      let ⟨hb⟩ ← LTm.bool? ps b
      return ⟨.neB ha hb⟩
    | .eqB, .uint => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.eqN rfl ha hb⟩
    | .eqB, .int => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.eqN rfl ha hb⟩
    | .neB, .uint => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.neN rfl ha hb⟩
    | .neB, .int => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.neN rfl ha hb⟩
    | .lt, _ => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.lt h ha hb⟩
    | .gt, _ => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.gt h ha hb⟩
    | .le, _ => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.le h ha hb⟩
    | .ge, _ => do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.ge h ha hb⟩
    | _, _ => none
  | s, .seq (s' := s') d a =>
    match s', s with
    | .val .bool, .val .bool => do
      let ⟨hd⟩ ← LTm.bool? ps d
      let ⟨ha⟩ ← LTm.bool? ps a
      return ⟨.seqB hd ha⟩
    | .val .uint, .val .bool => do
      let ⟨hd⟩ ← LTm.num? ps d
      let ⟨ha⟩ ← LTm.bool? ps a
      return ⟨.seqN rfl hd ha⟩
    | .val .int, .val .bool => do
      let ⟨hd⟩ ← LTm.num? ps d
      let ⟨ha⟩ ← LTm.bool? ps a
      return ⟨.seqN rfl hd ha⟩
    | _, _ => none
  | _, _ => none

/-- An equation of Presburger terms, with evidence for the checked compiler. -/
def eqArith? (ps : List Parameter) : {p : PrimTy} → (a b : LTm C (.val p)) →
    Option (PLift ((LFml.eq a b).Arith (· ∈ ps) (· ∈ ([] : List EnvKey))))
  | .bool, a, b =>
    if hd : a.depth ≤ 1023 ∧ b.depth ≤ 1023 then do
      let ⟨ha⟩ ← LTm.bool? ps a
      let ⟨hb⟩ ← LTm.bool? ps b
      return ⟨.eqB ha hb hd.1 hd.2⟩
    else none
  | .uint, a, b =>
    if hd : a.depth ≤ 1023 ∧ b.depth ≤ 1023 then do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.eqN rfl ha hb hd.1 hd.2⟩
    else none
  | .int, a, b =>
    if hd : a.depth ≤ 1023 ∧ b.depth ≤ 1023 then do
      let ⟨ha⟩ ← LTm.num? ps a
      let ⟨hb⟩ ← LTm.num? ps b
      return ⟨.eqN rfl ha hb hd.1 hd.2⟩
    else none

/-- **The Presburger fragment of a quantified subformula**: connectives and
`∀` over equations of scalar and Boolean terms of value locals and
literals. -/
def LFml.qfrag : LFml C → Bool
  | .tt => true
  | .eq a b => (eqArith? (uniq (LFml.eq a b).parameters) a b).isSome
  | .not φ => φ.qfrag
  | .and φ ψ | .imp φ ψ => φ.qfrag && ψ.qfrag
  | .all _ _ φ => φ.qfrag

/-! ## The compiler never refuses the fragment -/

theorem QArith.eqn?_isSome (pos : Parameter → Nat) (start : Nat) {p : PrimTy} (a b : LTm C (.val p))
    (h : (eqArith? (uniq (LFml.eq a b).parameters) a b).isSome = true) :
    (QArith.eqn? pos start a b).isSome = true := by
  obtain ⟨⟨harith⟩, -⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨enc, henc, good⟩ := StorageEncoding.ofFormula?_good harith
  obtain ⟨rf, hrf, hrf0⟩ := harith.readFree
  have hrfree : readFreeFormula? (LFml.eq a b) = some ⟨rf, hrf0⟩ := by
    simp only [readFreeFormula?, hrf, Option.bind_eq_bind, Option.bind_some, hrf0, dif_pos]
    rfl
  have hr := (Layout.unique_spec enc.refs).1
  have hc : ∀ q ∈ enc.refs, q ∈ Layout.unique enc.refs := fun q hq => ((Layout.unique_spec _).2 q).mpr hq
  have hw : (enc.lower (Layout.unique enc.refs)).width ≤
      (uniq (LFml.eq a b).parameters).length + (Layout.unique enc.refs).length := by
    have := good _ hc
    simpa only [List.length_nil, Nat.zero_add] using this
  simp only [QArith.eqn?, henc, hrfree, Option.bind_eq_bind, Option.bind_some, hr, hw, dif_pos]
  rw [dif_pos hc]
  rfl

theorem QArith.compile_isSome (pos : Parameter → Nat) (P : List Parameter)
    (hinj : ∀ q ∈ P, ∀ q' ∈ P, pos q = pos q' → q = q') :
    ∀ (φ : LFml C) (start : Nat) (h : ∀ q, pos q < start), φ.qfrag = true →
      (∀ q ∈ φ.parameters, q ∈ P) → (∀ q ∈ φ.binders, q ∈ P) →
      (QArith.compile pos P hinj φ start h).isSome = true
  | .tt, _, _, _, _, _ => rfl
  | .eq a b, start, _, hq, _, _ => QArith.eqn?_isSome pos start a b hq
  | .not φ, start, h, hq, hp, hb => by
    have := QArith.compile_isSome pos P hinj φ start h hq hp hb
    simp only [QArith.compile, Option.isSome_map, this]
  | .and φ ψ, start, h, hq, hp, hb | .imp φ ψ, start, h, hq, hp, hb => by
    simp only [LFml.qfrag, Bool.and_eq_true] at hq
    obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp (QArith.compile_isSome pos P hinj φ start h hq.1
      (fun q h' => hp q (List.mem_append_left _ h')) (fun q h' => hb q (List.mem_append_left _ h')))
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp (QArith.compile_isSome pos P hinj ψ A.next
      (fun q => Nat.lt_of_lt_of_le (h q) A.start_le) hq.2
      (fun q h' => hp q (List.mem_append_right _ h')) (fun q h' => hb q (List.mem_append_right _ h')))
    simp only [QArith.compile, hA, Option.bind_eq_bind, Option.bind_some, hB]
    rfl
  | .all k p φ, start, h, hq, hp, hb => by
    have hc : (⟨p, k⟩ : Parameter) ∈ P ∧ ∀ q ∈ φ.freeParams, q ∈ P :=
      ⟨hb _ List.mem_cons_self, fun q hq' => hp q (LFml.freeParams_sub φ q hq')⟩
    have := QArith.compile_isSome pos P hinj φ start h hq hp (fun q h' => hb q (List.mem_cons_of_mem _ h'))
    simp only [QArith.compile, dif_pos hc, Option.isSome_map, this]

theorem QDefs.compile_isSome (pos : Parameter → Nat) (P : List Parameter)
    (hinj : ∀ q ∈ P, ∀ q' ∈ P, pos q = pos q' → q = q') :
    ∀ (es : List (Nat × LFml C)) (start : Nat) (h : ∀ q, pos q < start),
      (∀ e ∈ es, e.2.qfrag = true ∧ (∀ q ∈ e.2.parameters, q ∈ P) ∧ ∀ q ∈ e.2.binders, q ∈ P) →
      (QDefs.compile pos P hinj es start h).isSome = true
  | [], _, _, _ => rfl
  | e :: es, start, h, he => by
    obtain ⟨hq, hp, hb⟩ := he e List.mem_cons_self
    obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp (QArith.compile_isSome pos P hinj e.2 start h hq hp hb)
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (QDefs.compile_isSome pos P hinj es A.next
      (fun q => Nat.lt_of_lt_of_le (h q) A.start_le) (fun e' h' => he e' (List.mem_cons_of_mem _ h')))
    simp only [QDefs.compile, hA, Option.bind_eq_bind, Option.bind_some, hD]
    rfl

/-! ## The fragment and totality -/

/-- **The eliminated leaf's quantified fragment**: a universal prefix
(shorter than 1024) binding the body's free parameters; the body lifted
within `liftBudget` (checked first: an unbounded lift is exponential), its
quantified subformulas abstracted, in
`LFml.Src false`, its cut within the size bounds; each abstracted subformula
Presburger (`LFml.qfrag`). -/
def LFml.quantCovered (ψ : LFml C) : Bool :=
  decide (ψ.allDepth < 1024) && ψ.stripAll.2.freeParams.all (fun q => decide (q ∈ ψ.stripAll.1)) &&
    (ψ.stripAll.2.liftCondB condLiftFuel liftBudget).isSome &&
    ((abstracted ψ.stripAll.2).1.src? false).isSome &&
    decide ((abstracted ψ.stripAll.2).1.cutAll.nodes ≤ 511) &&
    decide ((abstracted ψ.stripAll.2).1.cutAll.words * (abstracted ψ.stripAll.2).1.cutAll.words ≤ 2048) &&
    (abstracted ψ.stripAll.2).2.all (·.2.qfrag)

/-- **The fragment of the quantified decision**, on the eliminated leaf. -/
def _root_.Solidity.Fml.quantCovered (φ : Fml C []) : Bool :=
  match leafOf? φ with
  | some ψ => ψ.quantCovered
  | none => false

/-- **The quantified decision never refuses its fragment.** -/
theorem quantReduction?_isSome (φ : Fml C []) (h : φ.quantCovered = true) :
    (quantReduction? φ).isSome = true := by
  unfold Fml.quantCovered at h
  cases hl : leafOf? φ with
  | none => rw [hl] at h; cases h
  | some ψ =>
    rw [hl] at h
    simp only [leafOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨d, hd, r, hr, rfl⟩ := hl
    simp only [LFml.quantCovered, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hdepth, hcov⟩, hnodes⟩, hsrc⟩, hn⟩, hw⟩, hq⟩ := h
    obtain ⟨u, hu, hup, hub⟩ := UniversalPrefix.ofFormula?_strip _ 1024 hdepth
    have hc : ∀ q ∈ u.body.freeParams, q ∈ u.parameters := by
      rw [hub, hup]; exact hcov
    have hcap : (u.body.liftCondB condLiftFuel liftBudget).isSome = true := by rw [hub]; exact hnodes
    have hnone : (u.body.liftCondB condLiftFuel liftBudget).isNone = false := by
      cases hX : u.body.liftCondB condLiftFuel liftBudget with
      | none => rw [hX] at hcap; cases hcap
      | some _ => rfl
    obtain ⟨⟨hs⟩, -⟩ := Option.isSome_iff_exists.mp hsrc
    obtain ⟨M, hM⟩ := Option.isSome_iff_exists.mp
      (flattenedArithmetic?_isSome (abstracted u.body).1 (hub ▸ hs) (hub ▸ hn) (hub ▸ hw))
    have hW := layoutOf_W M (abstracted u.body).2
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (QDefs.compile_isSome
      (layoutOf M (abstracted u.body).2).pos (layoutOf M (abstracted u.body).2).P
      ((layoutOf M _).pos_inj hW) (abstracted u.body).2
      (layoutOf M _).top ((layoutOf M _).pos_lt hW) (fun e he =>
        ⟨hq e (by rw [← hub]; exact he),
          fun q hq' => layoutOf_P M _ q (List.mem_flatMap.2 ⟨e, he, List.mem_cons_of_mem _ (List.mem_append_left _ hq')⟩),
          fun q hq' => layoutOf_P M _ q (List.mem_flatMap.2 ⟨e, he, List.mem_cons_of_mem _ (List.mem_append_right _ hq')⟩)⟩))
    simp only [quantReduction?, hd, hr, hu, Option.bind_eq_bind, Option.bind_some, dif_pos hc, hnone,
      Bool.false_eq_true, if_false, hM, hD]
    rfl

/-- info: 'Solidity.Decide.quantReduction?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms quantReduction?_isSome

/-- info: 'Solidity.Decide.QuantReduction.valid_of_sentence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantReduction.valid_of_sentence

/-- info: 'Solidity.Decide.QuantReduction.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantReduction.verify

end Solidity.Decide
