import Solidity.Calculus.QuantTotality
import Solidity.Calculus.LedgerReduction

/-!
# Quantifiers beside ledger reads

Cut the ledger before quantifier abstraction. The main arithmetic retains
one shared typed ledger layout, two unrestricted natural codes per integer.
Only the primitive inputs have range constraints; quantified definitions keep
`QArith.compile`'s typed parameters. `netOK` remains unchanged: ledger reads
under remaining binders are refused. The original negative scalar quantifier
beside a ledger read satisfies this guard.
-/

namespace Solidity.Decide

open Linear ScalarCode ReadRealization QuantReduction

variable {C : Contract}

/-- The sentence's variables, from the main layout. -/
def ledgerLayoutOf {L : LFml C} (M : FlattenedArithmeticZ L) (Qs : List (Nat × LFml C)) : QLayout where
  es := M.encoding.environment
  ps := M.encoding.parameters
  W := Inputs.width M.encoding.environment M.encoding.parameters M.encoding.refs + 2 * M.encoding.ledger.length
  extras := (uniq (quantParams Qs)).filter (· ∉ M.encoding.parameters)

theorem ledgerLayoutOf_W {L : LFml C} (M : FlattenedArithmeticZ L) (Qs : List (Nat × LFml C)) :
    (ledgerLayoutOf M Qs).es.length + (ledgerLayoutOf M Qs).ps.length ≤ (ledgerLayoutOf M Qs).W := by
  simp only [ledgerLayoutOf, Inputs.width]
  omega

theorem ledgerLayoutOf_extras {L : LFml C} (M : FlattenedArithmeticZ L) (Qs : List (Nat × LFml C)) :
    ∀ q ∈ (ledgerLayoutOf M Qs).extras, q ∉ (ledgerLayoutOf M Qs).ps := by
  intro q hq
  simpa only [ledgerLayoutOf, decide_eq_true_eq] using (List.mem_filter.1 hq).2

theorem ledgerLayoutOf_P {L : LFml C} (M : FlattenedArithmeticZ L) (Qs : List (Nat × LFml C)) :
    ∀ q ∈ quantParams Qs, q ∈ (ledgerLayoutOf M Qs).P := by
  intro q hq
  by_cases h : q ∈ M.encoding.parameters
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_filter.2 ⟨(mem_uniq q _).2 hq,
      by simp only [h, not_false_eq_true, decide_true]⟩)

/-- Every parameter index is at most the layout length, including a miss. -/
theorem Parameters.index_le_length_quantLedger (q : Parameter) (ps : List Parameter) :
    Parameters.index q ps ≤ ps.length := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    simp only [Parameters.index, List.length_cons]
    split <;> omega

/-- A closed formula's compiled truth is independent of outer parameter
positions. The certificate, including fresh-reference bounds, is retained. -/
def QArith.repositionClosedLedger {φ : LFml C} {localPos globalPos : Parameter → Nat} {start : Nat}
    (A : QArith φ localPos start) (hc : φ.freeParams = []) : QArith φ globalPos start :=
  ⟨A.formula, A.refs, A.next, A.start_le, A.refs_mem,
    fun g ν x _ hrefs => A.correct g ν x (fun _q hq => by rw [hc] at hq; cases hq) hrefs⟩

/-- Compact only genuinely closed definitions. Binders may lexically reuse
outer positions; fresh references remain above the original GLOBAL start.
A failed recognition or bound check falls back to the original compiler. -/
def QArith.compileClosedLedger? (globalPos : Parameter → Nat) (φ : LFml C) (start : Nat) :
    Option (QArith φ globalPos start) := do
  if hc : φ.freeParams = [] then
    let ps := uniq (φ.parameters ++ φ.binders)
    if hn : ps.length < start then
      let A ← QArith.compile (fun q => Parameters.index q ps) ps
        (fun _q hq _q' hq' he => Parameters.index_inj hq hq' he) φ start
        (fun q => Nat.lt_of_le_of_lt (Parameters.index_le_length_quantLedger q ps) hn)
      return A.repositionClosedLedger hc
    else none
  else none

namespace QDefs

/-- Compile every definition. -/
def compileQuantLedger (pos : Parameter → Nat) (P : List Parameter)
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
    let A ← (QArith.compileClosedLedger? pos e.2 start).orElse
      (fun _ => QArith.compile pos P hinj e.2 start h)
    let D ← compileQuantLedger pos P hinj es A.next (fun q => Nat.lt_of_lt_of_le (h q) A.start_le)
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

/-- An exactly decided closed quantified subformula, at every typed state. -/
structure ClosedLedgerTruth (φ : LFml C) where
  truth : Bool
  correct : ∀ (g : State C []) (ν : AEnv), φ.holds g ν ↔ truth = true

/-- Without free parameters or fresh references, a compiled formula is a
constant proposition. Its verified decision transports in BOTH directions. -/
def QArith.closedLedgerTruth {φ : LFml C} {pos : Parameter → Nat} {start : Nat}
    (A : QArith φ pos start) (hc : φ.freeParams = []) (hr : A.refs = []) : ClosedLedgerTruth φ :=
  match A.formula.verify with
  | .inl hv => ⟨true, fun g ν => iff_of_true
      ((A.correct g ν (fun _ => 0) (fun _q hq => by rw [hc] at hq; cases hq)
        (fun _r hm => by rw [hr] at hm; cases hm)).1 (hv.down _)) rfl⟩
  | .inr cm => ⟨false, fun g ν => iff_of_false
      (fun hφ => cm.2 ((A.correct g ν cm.1 (fun _q hq => by rw [hc] at hq; cases hq)
        (fun _r hm => by rw [hr] at hm; cases hm)).2 hφ)) Bool.false_ne_true⟩

/-- An intrinsic formula with exactly the same truth, including polarity. -/
structure ClosedLedgerPrep (φ : LFml C) where
  formula : LFml C
  correct : ∀ (g : State C []) (ν : AEnv), formula.holds g ν ↔ φ.holds g ν

/-- Identity preparation when no certified closed replacement is available. -/
def ClosedLedgerPrep.id (φ : LFml C) : ClosedLedgerPrep φ := ⟨φ, fun _ _ => Iff.rfl⟩

/-- Eliminate only closed quantified subformulas with an exact, reference-free
compiled certificate. Unsupported or nonclosed binders remain unchanged. -/
def closeLedgerQuantifiers : (φ : LFml C) → ClosedLedgerPrep φ
  | .tt => .id _
  | .eq _ _ => .id _
  | .not φ =>
    let P := closeLedgerQuantifiers φ
    ⟨.not P.formula, fun g ν => not_congr (P.correct g ν)⟩
  | .and φ ψ =>
    let P := closeLedgerQuantifiers φ
    let Q := closeLedgerQuantifiers ψ
    ⟨.and P.formula Q.formula, fun g ν => and_congr (P.correct g ν) (Q.correct g ν)⟩
  | .imp φ ψ =>
    let P := closeLedgerQuantifiers φ
    let Q := closeLedgerQuantifiers ψ
    ⟨.imp P.formula Q.formula, fun g ν => imp_congr (P.correct g ν) (Q.correct g ν)⟩
  | .all k p φ =>
    let B := LFml.all k p φ
    if hc : B.freeParams = [] then
      match QArith.compileClosedLedger? (fun _ => 0) B
          ((uniq (B.parameters ++ B.binders)).length + 1) with
      | none => .id _
      | some A =>
        if hr : A.refs = [] then
          let T := A.closedLedgerTruth hc hr
          ⟨if T.truth then .tt else .not .tt, fun g ν => by
            rw [T.correct g ν]
            cases T.truth <;>
              simp only [ Bool.false_eq_true, ↓reduceIte, LFml.holds,
                not_true_eq_false, iff_self]⟩
        else .id _
    else .id _

/-- A quantified body, its abstracted arithmetic retaining ledger entries. -/
structure QuantLedgerBody (ψ : LFml C) where
  main : FlattenedArithmeticZ (abstracted ψ).1
  defs : QDefs (abstracted ψ).2 (ledgerLayoutOf main (abstracted ψ).2).pos
    (ledgerLayoutOf main (abstracted ψ).2).top

namespace QuantLedgerBody

variable {ψ : LFml C} (r : QuantLedgerBody ψ)

abbrev L : QLayout := ledgerLayoutOf r.main (abstracted ψ).2
abbrev Qs (_r : QuantLedgerBody ψ) : List (Nat × LFml C) := (abstracted ψ).2
abbrev A : AFml := r.main.encoding.formula

/-- The ledger-code tail is excluded from the primitive range domain. -/
def domainF : QFml :=
  .and (.atom (domain (Inputs.types r.L.es r.L.ps r.main.encoding.refs))
    (List.range (Inputs.types r.L.es r.L.ps r.main.encoding.refs).length))
    (.and (QFml.conj ((r.L.extras.filter (· ∈ freeQ r.Qs)).map fun q => QFml.inRange (r.L.pos q) q.prim))
      (QFml.conj (r.defs.refs.map fun e => QFml.inRange e.1 e.2)))

/-- All definitions and the main arithmetic share the same code positions. -/
def sentenceF : QFml :=
  QFml.imp r.domainF (QFml.imp r.defs.formula (.atom r.A (List.range r.L.W)))

/-- A typed state and parameter valuation refuting the body. -/
structure Countermodel (_r : QuantLedgerBody ψ) where
  state : State C []
  atoms : AEnv
  refutes : ¬ ψ.holds state atoms

/-- **A valid sentence makes the body valid.** -/
theorem body_of_sentence (h : r.sentenceF.Valid) (g : State C []) (ν' : AEnv) :
    ψ.holds g ν' := by
  let L0 := ψ.liftCond condLiftFuel
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
  have hL0 : L0.holds g ν1 ↔ ψ.holds g ν' :=
    (LFml.holds_agree g L0 fun q hq => hagree1 q (LFml.index_lt_atomBound L0 q hq)).trans
      (LFml.liftCond_holds g _ _ ν')
  have hhat : (abstracted ψ).1.holds g ν1 ↔ L0.holds g ν1 :=
    LFml.abstractQ_holds g ν1 L0 n fun e he => (hkey e he).trans (hQ1 e he).symm
  -- the cut's fresh atoms, defined past every atom of the abstracted body
  let B := (abstracted ψ).1
  have hF : CutFml.Good B B.atomBound [] (B.cut [] B.atomBound) := LFml.cut_good_top B
  obtain ⟨μ, hμ, hd⟩ := hF.defs.extend g ν1
  have hcut : B.cutAll.holds g μ → B.holds g ν1 := fun h =>
    (LFml.holds_agree_below g B hμ).mpr
      ((hF.holds g μ (fun _ h => nomatch h) hd).mp ((LFml.cutAll_holds_iff B g μ).mp h hd))
  let fl := r.main.flattening
  let ν2 := fl.layout.fill g μ
  have hfill : fl.flat.formula.holds g ν2 ↔ B.cutAll.holds g μ := fl.fill_iff g μ
  have hcons : (ReadOccurrence.constraints fl.flat.reads).holds g ν2 :=
    (fl.layout.constraints_iff g ν2).2 (fl.layout.entries_consistent g ν2 (fl.layout.fill_interpreted g μ))
  have hagree2 : ν1.AgreesBelow B.atomBound ν2 :=
    hμ.trans ((fl.layout.fill_agrees g μ).mono (LFml.atomBound_le_cutAll B))
  have hQ2 : ∀ e ∈ r.Qs, (e.2.holds g ν2 ↔ e.2.holds g ν1) := fun e he =>
    LFml.holds_agree g e.2 fun q hq => (hagree2 q.prim q.index (Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (hQparams e he q hq) (hkge e he))
      (Nat.le_of_lt (LFml.abstractQ_bound L0 n e he)))).symm
  have hkey2 : ∀ e ∈ r.Qs, ν2.get .bool e.1 = ν1.get .bool e.1 := fun e he =>
    (hagree2 .bool e.1 (LFml.abstractQ_bound L0 n e he)).symm
  let obs := Inputs.observe r.main.encoding.environment r.main.encoding.parameters r.main.encoding.refs g ν2
  let zcodes := codesZ r.L.es r.L.ps r.main.encoding.refs r.main.encoding.ledger g ν2
  let x := assignmentOf r.L zcodes ν2
  have hW : r.L.es.length + r.L.ps.length ≤ r.L.W := ledgerLayoutOf_W r.main r.Qs
  have hrep : ∀ q ∈ r.L.P, x (r.L.pos q) = q.code ν2 :=
    assignmentOf_rep r.L hW zcodes ν2 fun q hq => by
      have hi : Parameters.index q r.L.ps < r.L.ps.length := Parameters.index_lt_of_mem hq
      have hk : r.L.es.length + Parameters.index q r.L.ps < Inputs.width r.L.es r.L.ps r.main.encoding.refs := by
        simp only [Inputs.width]; omega
      simp only [zcodes, codesZ, if_pos hk]
      exact Inputs.codes_param _ _ _ g ν2 q hq
  have hlow : ∀ i < r.L.W, x i = zcodes i := fun i hi => by simp only [x, assignmentOf, hi, ↓reduceIte]
  have hx0 : ∀ i, r.L.top ≤ i → x i = 0 := fun i hi => assignmentOf_top _ _ _ _ hi
  have hs : r.sentenceF.holds x := h x
  simp only [sentenceF, QFml.holds_imp] at hs
  have hdom : r.domainF.holds x := by
    refine ⟨?_, ?_, ?_⟩
    · show (QFml.atom _ (List.range (Inputs.types _ _ _).length)).holds x
      rw [holds_atom_domain]
      have : (domain (Inputs.types r.L.es r.L.ps r.main.encoding.refs)).holds obs.codes :=
        domain_codes obs
      rw [domain, domainFrom_iff] at this ⊢
      intro k p hk
      have hk0 : k < Inputs.width r.L.es r.L.ps r.main.encoding.refs := by
        have ht : k < (Inputs.types r.L.es r.L.ps r.main.encoding.refs).length :=
          (List.getElem?_eq_some_iff.1 hk).1
        rw [Inputs.length_types] at ht
        exact ht
      have hk' : k < r.L.W := Nat.lt_of_lt_of_le hk0 (Nat.le_add_right _ _ )
      have h' : obs.codes (0 + k) < ScalarCode.bound p := this k p hk
      simp only [Nat.zero_add] at h' ⊢
      rw [hlow k hk']
      simp only [zcodes, codesZ, if_pos hk0]
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
    hrep q (ledgerLayoutOf_P r.main r.Qs q (List.mem_flatMap.2 ⟨e, he, List.mem_cons_of_mem _
      (List.mem_append_left _ (LFml.freeParams_sub e.2 q hq))⟩))
  have hrefs : ∀ e ∈ r.defs.refs, x e.1 < bound e.2 := fun e he => by
    rw [hx0 _ (r.defs.refs_mem e he).1]; exact bound_pos _
  have hdefs : r.defs.formula.holds x := by
    rw [r.defs.correct g ν2 x hrepQ hrefs]
    intro e he
    rw [hrep _ (ledgerLayoutOf_P r.main r.Qs _ (List.mem_flatMap.2 ⟨e, he, List.mem_cons_self⟩)), code_bool,
      hkey2 e he, hkey e he, hQ2 e he, hQ1 e he]
  have hA : (QFml.atom r.A (List.range r.L.W)).holds x := hs hdom hdefs
  rw [QFml.holds_atom_range r.A r.L.W r.main.encoding.width] at hA
  have hA' : r.A.holds zcodes := (AFml.holds_agree _ _ _ fun i hi =>
    hlow i (Nat.lt_of_lt_of_le hi r.main.encoding.width)).1 hA
  have hflat : r.main.flattening.formula.holds g ν2 :=
    (r.main.encoding.correct g ν2 zcodes (codesZ_agree _ _ _ _ g ν2)).1 hA'
  exact hL0.1 (hhat.1 (hcut (hfill.1 (hflat hcons))))

/-- **A false assignment gives a refuting state**: the main layout's
values realized, the extras read from the assignment, the flattening's
countermodel; its definitions make each atom agree with its subformula. -/
def countermodelOf (x : Nat → Nat) (hx : ¬ r.sentenceF.holds x) : r.Countermodel := by
  have hx' : r.domainF.holds x ∧ r.defs.formula.holds x ∧
      ¬ (QFml.atom r.A (List.range r.L.W)).holds x := by
    simp only [sentenceF, QFml.holds_imp] at hx
    exact Classical.byContradiction fun h => hx fun h1 h2 =>
      Classical.byContradiction fun h3 => h ⟨h1, h2, h3⟩
  have hdomM : (domain (Inputs.types r.main.encoding.environment r.main.encoding.parameters
      r.main.encoding.refs)).holds x := (holds_atom_domain _ x).1 hx'.1.1
  let model := r.main.encoding.realize x hdomM
  let gM := model.1
  let νM := model.2
  let ν := Parameters.setAll r.L.extras (extraValue r.L x) νM
  have hmodel : Inputs.AgreeZ r.L.es r.L.ps r.main.encoding.refs r.main.encoding.ledger gM νM x :=
    r.main.encoding.realize_agree x hdomM
  have hobs : Inputs.observe r.L.es r.L.ps r.main.encoding.refs gM ν =
      Inputs.observe r.L.es r.L.ps r.main.encoding.refs gM νM :=
    Inputs.observe_setAll _ _ _ gM νM _ r.L.extras (ledgerLayoutOf_extras r.main r.Qs)
  have hxrep : Inputs.AgreeZ r.L.es r.L.ps r.main.encoding.refs r.main.encoding.ledger gM ν x :=
    ⟨fun k hk => by rw [hobs]; exact hmodel.1 k hk, hmodel.2⟩
  have hnA : ¬ r.A.holds x := fun h => hx'.2.2
    ((QFml.holds_atom_range r.A r.L.W r.main.encoding.width x).2 h)
  have hflat : ¬ r.main.flattening.formula.holds gM ν := fun h =>
    hnA ((r.main.encoding.correct gM ν x hxrep).2 h)
  have hc : (ReadOccurrence.constraints r.main.flattening.flat.reads).holds gM ν :=
    Classical.byContradiction fun h => hflat fun hh => (h hh).elim
  have hf : ¬ r.main.flattening.flat.formula.holds gM ν := fun h => hflat fun _ => h
  let st := r.main.flattening.countermodel gM ν ((r.main.flattening.layout.constraints_iff gM ν).1 hc) hf
  have hW : r.L.es.length + r.L.ps.length ≤ r.L.W := ledgerLayoutOf_W r.main r.Qs
  have hrep : ∀ q ∈ freeQ r.Qs, x (r.L.pos q) = q.code ν := by
    intro q hqf
    have hq : q ∈ r.L.P := ledgerLayoutOf_P r.main r.Qs q (freeQ_sub r.Qs q hqf)
    by_cases h1 : q ∈ r.L.ps
    · have hl : Parameters.index q r.L.ps < r.L.ps.length := Parameters.index_lt_of_mem h1
      have hp : r.L.pos q = r.L.es.length + Parameters.index q r.L.ps := by
        simp only [QLayout.pos, h1, ↓reduceIte]
      have hk : r.L.es.length + Parameters.index q r.L.ps < Inputs.width r.L.es r.L.ps r.main.encoding.refs := by
        simp only [Inputs.width]; omega
      rw [hp, hxrep.1 _ hk]
      exact Inputs.codes_param _ _ _ gM ν q h1
    · have h2 : q ∈ r.L.extras := (List.mem_append.1 hq).resolve_left h1
      have hin : x (r.L.pos q) < ScalarCode.bound q.prim := by
        have : (QFml.inRange (r.L.pos q) q.prim).holds x :=
          (QFml.holds_conj x _).1 hx'.1.2.1 _ (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨h2,
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
  have hdefs : ∀ e ∈ r.Qs, (x (r.L.pos ⟨.bool, e.1⟩) = 1 ↔ e.2.holds st.1 ν) :=
    (r.defs.correct st.1 ν x hrepQ hrefs).1 hx'.2.1
  have hkey : ∀ e ∈ r.Qs, (ν.get .bool e.1 = true ↔ e.2.holds st.1 ν) := fun e he => by
    rw [← code_bool, ← hrep _ (List.mem_flatMap.2 ⟨e, he, List.mem_cons_self⟩)]
    exact hdefs e he
  let L0 := ψ.liftCond condLiftFuel
  have hL0 : ¬ L0.holds st.1 ν := fun h =>
    st.2 (LFml.holds_cutAll _ st.1 ν ((LFml.abstractQ_holds st.1 ν L0 L0.atomBound hkey).2 h))
  have hB : ¬ ψ.holds st.1 ν := fun h => hL0 ((LFml.liftCond_holds st.1 _ _ ν).2 h)
  exact ⟨st.1, ν, hB⟩

/-- Exactness includes reconstructing a typed countermodel. -/
theorem valid_iff : ψ.Valid ↔ r.sentenceF.Valid := by
  refine ⟨fun h x => Classical.byContradiction fun hx => ?_, r.body_of_sentence⟩
  let cm := r.countermodelOf x hx
  exact cm.refutes (h cm.state cm.atoms)

/-- The generic quantified decision retains its original exact certificate. -/
def verifyQuantified : Sum (PLift ψ.Valid) r.Countermodel :=
  match r.sentenceF.verify with
  | .inl h => .inl ⟨r.body_of_sentence h.down⟩
  | .inr cm => .inr (r.countermodelOf cm.1 cm.2)

/-- Closed definitions are decided separately, preserving their polarity;
the resulting quantifier-free ledger leaf uses the existing arithmetic
backend. Both answers are transported by exact equivalence. The original
quantified decision remains the fallback, with unchanged budgets. -/
def verify : Sum (PLift ψ.Valid) r.Countermodel :=
  let P := closeLedgerQuantifiers ψ
  if P.formula.cutAll.nodes ≤ 511 then
    match flattenedArithmeticZ? (readBudget P.formula.cutAll) P.formula with
    | none => r.verifyQuantified
    | some A =>
      match A.verify with
      | .inl h => .inl ⟨fun g ν => (P.correct g ν).1 (h.down g ν)⟩
      | .inr cm => .inr ⟨cm.state, cm.atoms, fun h => cm.refutes ((P.correct _ _).2 h)⟩
  else r.verifyQuantified

end QuantLedgerBody

/-- Compilation keeps the existing lift, read and 511-node bounds. -/
def quantLedgerBody? (ψ : LFml C) : Option (QuantLedgerBody ψ) := do
  if (ψ.liftCondB condLiftFuel liftBudget).isNone then none
  else if (abstracted ψ).1.cutAll.nodes ≤ 511 then
    let M ← flattenedArithmeticZ? (readBudget (abstracted ψ).1.cutAll) (abstracted ψ).1
    let L := ledgerLayoutOf M (abstracted ψ).2
    let D ← QDefs.compileQuantLedger L.pos L.P (L.pos_inj (ledgerLayoutOf_W M _))
      (abstracted ψ).2 L.top (L.pos_lt (ledgerLayoutOf_W M _))
    return ⟨M, D⟩
  else none

/-- Exact scalar-quantifier preparation. Array-property flooring is left to
its existing lanes; it is unnecessary for the ledger-free binders here. -/
def quantLedgerPrep (B : LFml C) : Prep B :=
  (expandPrep B).trans (hoistPrep _)

/-- Negative scalar quantifiers beside ledger reads, decided exactly. -/
structure QuantLedgerReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  sentence : UniversalPrefix (source.leaf.elim.condSimp.prenex.liftCond condLiftFuel)
  covered : ∀ q ∈ sentence.body.freeParams, q ∈ sentence.parameters
  prep : Prep sentence.body
  netOK : prep.body.netOK = true
  netLen : prep.body.netReads.length ≤ 2 ^ 256
  reads : List (Σ' a : LTm C (.val .uint), ReadExpr a)
  readsEq : reads.map (·.1) = prep.body.netReads
  body : QuantLedgerBody prep.body.ledgerCut

/-- Expand and hoist with `quantLedgerPrep`, then cut the ledger before
quantifier abstraction. No array-property ledger regions are rebuilt. -/
def quantLedgerReduction? (φ : Fml C []) : Option (QuantLedgerReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  if (r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget).isNone then none
  let sentence ← UniversalPrefix.ofFormula? 1024 (r.leaf.elim.condSimp.prenex.liftCond condLiftFuel)
  if hc : ∀ q ∈ sentence.body.freeParams, q ∈ sentence.parameters then
    let P := quantLedgerPrep sentence.body
    if P.body.netReads.isEmpty then none
    else if hok : P.body.netOK = true then
      if hn : P.body.netReads.length ≤ 2 ^ 256 then
        let qs ← readExprs? P.body.netReads
        return ⟨d, r, sentence, hc, P, hok, hn, qs.1, qs.2,
          ← quantLedgerBody? P.body.ledgerCut⟩
      else none
    else none
  else none

namespace QuantLedgerReduction

variable {φ : Fml C []} (r : QuantLedgerReduction φ)

/-- **A valid prepared body makes the leaf valid.** -/
theorem valid_of_body (h : r.prep.body.Valid) : Fml.Valid φ := fun g =>
  (r.normalization.correct g).mp ((r.source.elim_holds_iff g).mp ((LFml.condSimp_holds g _ _).mp
    ((LFml.prenex_holds g _ _).mp ((LFml.liftCond_holds g _ _ _).mp
      (r.sentence.close g AEnv.dflt (fun ν => r.prep.sound h g ν))))))

/-- **A state where the prepared body fails refutes the leaf**: the
preparation's state, the prefix instantiated at the same atoms. -/
def countermodelOfBody (st : State C []) (ν : AEnv) (hB : ¬ r.prep.body.holds st ν) :
    {σ : State C [] // ¬ holds σ φ} :=
  let st' := r.prep.refute st ν hB
  ⟨st'.1, fun hφ => by
    have hinst : r.sentence.body.holds st'.1 (Parameters.assign r.sentence.parameters ν AEnv.dflt) :=
      r.sentence.instantiate st'.1 AEnv.dflt ν ((LFml.liftCond_holds _ _ _ _).mpr
      ((LFml.prenex_holds _ _ _).mpr ((LFml.condSimp_holds _ _ _).mpr ((r.source.elim_holds_iff _).mpr
        ((r.normalization.correct _).mpr hφ)))))
    refine st'.2 ((LFml.holds_agree_free st'.1 _ fun q hq => ?_).1 hinst)
    rw [Parameters.read_assign, if_pos (r.covered q hq)]⟩

/-- **Proof or refutation**: the cut body's arithmetic decided; a false
assignment's state, its ledger pulled back to the reads' addresses, preserving its observations. -/
def verify : Sum (PLift (Fml.Valid φ)) {σ : State C [] // ¬ holds σ φ} :=
  match r.body.verify with
  | .inl h => .inl ⟨r.valid_of_body ((LFml.ledgerCut_valid_iff _ r.netOK r.netLen).mpr h.down)⟩
  | .inr cm =>
    .inr (r.countermodelOfBody (LFml.ledgerPull cm.state (readValsQ cm.state cm.atoms r.reads)) cm.atoms
      (LFml.ledgerCut_refutes _ r.netOK cm.state cm.atoms _
        (by rw [readValsQ_eq, r.readsEq]) cm.refutes))

end QuantLedgerReduction

/-- The successfully certified ledger/quantifier reductions. This is an
additional covered class, not a characterization of `inTarget`. -/
def _root_.Solidity.Fml.quantLedgerCovered (φ : Fml C []) : Bool :=
  (quantLedgerReduction? φ).isSome

/-- Recognition supplies a reduction carrying both soundness directions. -/
theorem quantLedgerReduction?_isSome (φ : Fml C []) (h : φ.quantLedgerCovered = true) :
    (quantLedgerReduction? φ).isSome = true := h

/-- info: 'Solidity.Decide.QuantLedgerBody.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantLedgerBody.valid_iff
/-- info: 'Solidity.Decide.QuantLedgerBody.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantLedgerBody.verify
/-- info: 'Solidity.Decide.QuantLedgerReduction.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantLedgerReduction.verify

/-- info: 'Solidity.Decide.QArith.repositionClosedLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QArith.repositionClosedLedger
/-- info: 'Solidity.Decide.QArith.closedLedgerTruth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QArith.closedLedgerTruth
/-- info: 'Solidity.Decide.closeLedgerQuantifiers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms closeLedgerQuantifiers
/-- info: 'Solidity.Decide.QDefs.compileQuantLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QDefs.compileQuantLedger

end Solidity.Decide
