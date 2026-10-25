import Solidity.Calculus.LedgerTotality

/-!
# Leaves that read the ledger (M7, plan step 3)

The automatic pipeline of `Calculus/DependentReduction.lean` on a leaf whose
lifted body reads the ledger of its starting state (`net(a)`, an address a
scalar): the body's reads are cut to reads at constants
(`LFml.ledgerCut`, `Calculus/LedgerCut.lean`), and the cut body is decided
with its ledger entries as atoms (`FlattenedArithmeticZ`,
`Calculus/LedgerArithmetic.lean`).  A countermodel's ledger is the cut
one's entries pulled back to the reads' addresses, which the reads' queries
compute (`ReadExpr.query`), so the verdict stays computable.
-/

namespace Solidity.Decide

open ReadRealization Linear ScalarCode

variable {C : Contract}

/-- The reads' addresses, each with its query. -/
def readExprs? : (rs : List (LTm C (.val .uint))) →
    Option {qs : List (Σ' a : LTm C (.val .uint), ReadExpr a) // qs.map (·.1) = rs}
  | [] => some ⟨[], rfl⟩
  | a :: rs => do
    let e ← ReadExpr.ofTerm? a
    let qs ← readExprs? rs
    return ⟨⟨a, e⟩ :: qs.1, by simp only [List.map_cons, qs.2]⟩

/-- The values of the reads' addresses, by their queries. -/
def readValsQ (g : State C []) (ν : AEnv) (qs : List (Σ' a : LTm C (.val .uint), ReadExpr a)) :
    List (Option PrimTy.uint.Denote) :=
  qs.map fun q => ((q.2.query g ν).runStorage g.storage).map (ReadDen.erase g)

theorem readValsQ_eq (g : State C []) (ν : AEnv) (qs : List (Σ' a : LTm C (.val .uint), ReadExpr a)) :
    readValsQ g ν qs = readVals g ν (qs.map (·.1)) := by
  simp only [readValsQ, readVals, List.map_map]
  apply List.map_congr_left
  intro q _
  exact ReadExpr.query_sound g ν q.2 g.storage

theorem readExprs?_isSome : ∀ {rs : List (LTm C (.val .uint))},
    (∀ a ∈ rs, ∃ e, ReadExpr.ofTerm? a = some e) → (readExprs? rs).isSome = true
  | [], _ => rfl
  | a :: rs, h => by
    obtain ⟨e, he⟩ := h a List.mem_cons_self
    obtain ⟨qs, hqs⟩ := Option.isSome_iff_exists.mp
      (readExprs?_isSome (rs := rs) fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [readExprs?, he, hqs, Option.bind_eq_bind, Option.bind_some]
    rfl

/-- **A leaf that reads the ledger, decided by arithmetic.** -/
structure LedgerReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  sentence : UniversalPrefix (source.leaf.elim.condSimp.prenex.liftCond condLiftFuel)
  bodyRead : ReadFormula sentence.body
  covered : ∀ p ∈ sentence.body.parameters, p ∈ sentence.parameters
  netOK : sentence.body.netOK = true
  netLen : sentence.body.netReads.length ≤ 2 ^ 256
  reads : List (Σ' a : LTm C (.val .uint), ReadExpr a)
  readsEq : reads.map (·.1) = sentence.body.netReads
  body : FlattenedArithmeticZ sentence.body.ledgerCut

def ledgerReduction? (φ : Fml C []) : Option (LedgerReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  if (r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget).isNone then none
  let sentence ← UniversalPrefix.ofFormula? 1024 (r.leaf.elim.condSimp.prenex.liftCond condLiftFuel)
  let bodyRead ← ReadFormula.ofFormula? sentence.body
  if hc : ∀ p ∈ sentence.body.parameters, p ∈ sentence.parameters then
    if hok : sentence.body.netOK = true then
      if hn : sentence.body.netReads.length ≤ 2 ^ 256 then
        let qs ← readExprs? sentence.body.netReads
        return ⟨d, r, sentence, bodyRead, hc, hok, hn, qs.1, qs.2,
          ← flattenedArithmeticZ? 2048 sentence.body.ledgerCut⟩
      else none
    else none
  else none

namespace LedgerReduction

theorem body_valid_iff {φ : Fml C []} (r : LedgerReduction φ) :
    Fml.Valid φ ↔ r.sentence.body.Valid := by
  constructor
  · intro h g ν
    exact (r.bodyRead.holds_assign g r.sentence.parameters r.covered AEnv.dflt ν).mp
      (r.sentence.instantiate g AEnv.dflt ν ((LFml.liftCond_holds g _ _ _).mpr
        ((LFml.prenex_holds g _ _).mpr ((LFml.condSimp_holds g _ _).mpr
          ((r.source.elim_holds_iff g).mpr ((r.normalization.correct g).mpr (h g)))))))
  · intro h g
    exact (r.normalization.correct g).mp ((r.source.elim_holds_iff g).mp
      ((LFml.condSimp_holds g _ _).mp ((LFml.prenex_holds g _ _).mp
        ((LFml.liftCond_holds g _ _ _).mp (r.sentence.close g AEnv.dflt (h g))))))

theorem valid_iff {φ : Fml C []} (r : LedgerReduction φ) :
    Fml.Valid φ ↔ r.body.encoding.guarded.Valid :=
  r.body_valid_iff.trans ((LFml.ledgerCut_valid_iff _ r.netOK r.netLen).trans r.body.valid_iff)

structure Countermodel {φ : Fml C []} (r : LedgerReduction φ) where
  state : State C []
  refutes : ¬ holds state φ

def countermodelOf {φ : Fml C []} (r : LedgerReduction φ) (cm : r.body.Countermodel) :
    r.Countermodel := by
  refine ⟨LFml.ledgerPull cm.state (readValsQ cm.state cm.atoms r.reads), fun hv => ?_⟩
  have hvs : readValsQ cm.state cm.atoms r.reads = readVals cm.state cm.atoms r.sentence.body.netReads := by
    rw [readValsQ_eq, r.readsEq]
  apply LFml.ledgerCut_refutes _ r.netOK cm.state cm.atoms _ hvs cm.refutes
  exact (r.bodyRead.holds_assign _ r.sentence.parameters r.covered AEnv.dflt _).mp
    (r.sentence.instantiate _ AEnv.dflt cm.atoms ((LFml.liftCond_holds _ _ _ _).mpr
      ((LFml.prenex_holds _ _ _).mpr ((LFml.condSimp_holds _ _ _).mpr
        ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr hv))))))

def verify {φ : Fml C []} (r : LedgerReduction φ) : Sum (PLift (Fml.Valid φ)) r.Countermodel :=
  match r.body.verify with
  | .inl h => .inl ⟨r.body_valid_iff.mpr
      ((LFml.ledgerCut_valid_iff _ r.netOK r.netLen).mpr h.down)⟩
  | .inr cm => .inr (r.countermodelOf cm)

end LedgerReduction

/-! ## The fragment -/

/-- **The eliminated leaf's fragment with ledger reads**: `LFml.inExact`
with reads of the starting ledger at scalar addresses. -/
def LFml.inLedger (ψ : LFml C) : Bool :=
  decide (ψ.allDepth < 1024) && (ψ.stripAll.2.srcL? .pre true).isSome &&
    decide (ψ.stripAll.2.condMax < condLiftFuel) &&
    ψ.stripAll.2.parameters.all (fun q => decide (q ∈ ψ.stripAll.1))

/-- The size bounds, on the lifted body and on its ledger cut then cut. -/
def LFml.ledgerBounded (ψ : LFml C) : Bool :=
  let body := (ψ.liftCond condLiftFuel).stripAll.2
  decide (body.nodes ≤ 511) && decide (body.netReads.length ≤ 2 ^ 256) &&
    decide (body.ledgerCut.cutAll.nodes ≤ 511) &&
    decide (body.ledgerCut.cutAll.words * body.ledgerCut.cutAll.words ≤ 2048)

/-- **The fragment of the decision with ledger reads.** -/
def _root_.Solidity.Fml.ledgerCovered (φ : Fml C []) : Bool :=
  match leafOf? φ with
  | some ψ => ψ.inLedger && ψ.ledgerBounded
  | none => false

/-- **The decision with ledger reads never refuses its fragment.** -/
theorem ledgerReduction?_isSome (φ : Fml C []) (h : φ.ledgerCovered = true) :
    (ledgerReduction? φ).isSome = true := by
  unfold Fml.ledgerCovered at h
  cases hl : leafOf? φ with
  | none => rw [hl] at h; cases h
  | some ψ =>
    rw [hl, Bool.and_eq_true] at h
    obtain ⟨h, hb⟩ := h
    simp only [leafOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨d, hd, r, hr, rfl⟩ := hl
    simp only [LFml.inLedger, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hdepth0, hsrc0⟩, hm⟩, hc0⟩ := h
    obtain ⟨⟨hs0⟩, -⟩ := Option.isSome_iff_exists.mp hsrc0
    obtain ⟨e1, e2⟩ := LFml.liftCond_stripAll 63 r.leaf.elim.condSimp.prenex
    have hlift : ((r.leaf.elim.condSimp.prenex.liftCond condLiftFuel).stripAll.2).SrcL false true .pre := by
      rw [show condLiftFuel = 63 + 1 from rfl, e2]
      exact LFml.liftCond_src condLiftFuel hs0 hm
    have hdepth : (r.leaf.elim.condSimp.prenex.liftCond condLiftFuel).allDepth < 1024 := by
      rw [show condLiftFuel = 63 + 1 from rfl, e1]; exact hdepth0
    have hcov : ∀ q ∈ (r.leaf.elim.condSimp.prenex.liftCond condLiftFuel).stripAll.2.parameters,
        q ∈ (r.leaf.elim.condSimp.prenex.liftCond condLiftFuel).stripAll.1 := by
      intro q hq
      have hq' : q ∈ (r.leaf.elim.condSimp.prenex.stripAll.2.liftCond (63 + 1)).parameters := by
        have := hq
        rw [show condLiftFuel = 63 + 1 from rfl, e2] at this
        exact this
      show q ∈ (r.leaf.elim.condSimp.prenex.liftCond (63 + 1)).stripAll.1
      rw [e2]
      exact hc0 q (LFml.liftCond_params _ _ q hq')
    simp only [LFml.ledgerBounded, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨hn, hlen⟩, hcn⟩, hw⟩ := hb
    obtain ⟨u, hu, hup, hub⟩ := UniversalPrefix.ofFormula?_strip _ 1024 hdepth
    have hs : u.body.SrcL false true .pre := hub ▸ hlift
    have hc : ∀ p ∈ u.body.parameters, p ∈ u.parameters := by
      rw [hub, hup]
      exact hcov
    obtain ⟨hcut, hok⟩ := LFml.ledgerCut_src hs
    obtain ⟨rf, hrf⟩ := hs.readFormula
    obtain ⟨-, hreads, -⟩ := LFml.SrcL.netCut hs 0
    obtain ⟨qs, hqs⟩ := Option.isSome_iff_exists.mp
      (readExprs?_isSome (rs := u.body.netReads) fun a ha => (hreads a ha).readExpr)
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp
      (flattenedArithmeticZ?_isSome u.body.ledgerCut hcut (hub ▸ hcn) (hub ▸ hw))
    have hcap := LFml.liftCondB_isSome _ hdepth hn
    have hnone : (r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget).isNone = false := by
      cases hX : r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget with
      | none => rw [hX] at hcap; cases hcap
      | some _ => rfl
    have hlen' : u.body.netReads.length ≤ 2 ^ 256 := hub ▸ hlen
    simp only [ledgerReduction?, hd, hr, hu, hrf, Option.bind_eq_bind, Option.bind_some,
      hnone, Bool.false_eq_true, if_false]
    rw [dif_pos hc, dif_pos hok, dif_pos hlen', hqs]
    simp only [Option.bind_some, hF]
    rfl

end Solidity.Decide
