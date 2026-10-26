import Solidity.Calculus.LedgerReduction
import Solidity.Calculus.QuantReduction

/-!
# Leaves with blocks over the ledger (M7, feature 21)

`ledgerReduction?` (`Calculus/LedgerReduction.lean`) takes a leaf whose
body reads the starting ledger and holds no quantifier; the quantified
pipeline (`quantReduction?`) reads no ledger.  A negative block over the
ledger (`(∀ uint a; a > 5 → net(a) == 1) → net(3) == 1`) reached neither.
This pipeline is the ledger's with a preparation stage between the prefix
and the cut: the body's blocks instantiated at the index set (`apfPrep`,
`Calculus/ArrayProperty.lean`, the ledger floored as a mapping is), the
instance cut and decided as `ledgerReduction?` decides it.

The verdict is exact (`Prep.valid_iff`), and a refutation of the instance
is one of the leaf in the state whose ledger is rebuilt at the floors of
the index set (`netRebuild`): region by region, a region of zeros left
out, so a refuting ledger whose regions past the goal's addresses hold
`1` is a term listing `2^256 - 6` entries that no evaluation builds, and
one whose far region holds `0` lists the regions near the goal's
addresses only.
-/

namespace Solidity.Decide

open ReadRealization Linear ScalarCode

variable {C : Contract}

/-- **A leaf with blocks over the ledger, decided by arithmetic.** -/
structure LedgerBlockReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  sentence : UniversalPrefix (source.leaf.elim.condSimp.prenex.liftCond condLiftFuel)
  covered : ∀ q ∈ sentence.body.freeParams, q ∈ sentence.parameters
  prep : Prep sentence.body
  netOK : prep.body.netOK = true
  netLen : prep.body.netReads.length ≤ 2 ^ 256
  reads : List (Σ' a : LTm C (.val .uint), ReadExpr a)
  readsEq : reads.map (·.1) = prep.body.netReads
  body : FlattenedArithmeticZ prep.body.ledgerCut

/-- **The pipeline**: the ledger's (`ledgerReduction?`), the body prepared
by array property instantiation (`apfPrep`) before the ledger cut. -/
def ledgerBlockReduction? (φ : Fml C []) : Option (LedgerBlockReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  if (r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget).isNone then none
  let sentence ← UniversalPrefix.ofFormula? 1024 (r.leaf.elim.condSimp.prenex.liftCond condLiftFuel)
  if hc : ∀ q ∈ sentence.body.freeParams, q ∈ sentence.parameters then
    let P := apfPrep sentence.body
    if hok : P.body.netOK = true then
      if hn : P.body.netReads.length ≤ 2 ^ 256 then
        let qs ← readExprs? P.body.netReads
        return ⟨d, r, sentence, hc, P, hok, hn, qs.1, qs.2,
          ← flattenedArithmeticZ? (readBudget P.body.ledgerCut.cutAll) P.body.ledgerCut⟩
      else none
    else none
  else none

namespace LedgerBlockReduction

variable {φ : Fml C []} (r : LedgerBlockReduction φ)

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
    have hinst := r.sentence.instantiate st'.1 AEnv.dflt ν ((LFml.liftCond_holds _ _ _ _).mpr
      ((LFml.prenex_holds _ _ _).mpr ((LFml.condSimp_holds _ _ _).mpr ((r.source.elim_holds_iff _).mpr
        ((r.normalization.correct _).mpr hφ)))))
    refine st'.2 ((LFml.holds_agree_free st'.1 _ fun q hq => ?_).1 hinst)
    rw [Parameters.read_assign, if_pos (r.covered q hq)]⟩

/-- **Proof or refutation**: the cut body's arithmetic decided; a false
assignment's state, its ledger pulled back to the reads' addresses, then
rebuilt at the floors. -/
def verify : Sum (PLift (Fml.Valid φ)) {σ : State C [] // ¬ holds σ φ} :=
  match r.body.verify with
  | .inl h => .inl ⟨r.valid_of_body ((LFml.ledgerCut_valid_iff _ r.netOK r.netLen).mpr h.down)⟩
  | .inr cm =>
    .inr (r.countermodelOfBody (LFml.ledgerPull cm.state (readValsQ cm.state cm.atoms r.reads)) cm.atoms
      (LFml.ledgerCut_refutes _ r.netOK cm.state cm.atoms _
        (by rw [readValsQ_eq, r.readsEq]) cm.refutes))

end LedgerBlockReduction

/-! ## The fragment -/

/-- **The eliminated leaf's fragment with ledger blocks**: a universal
prefix (shorter than 1024) of the lifted leaf binding the body's free
parameters, the lift within `liftBudget`; the prepared body
(`apfPrep`) in the ledger fragment with no conditional
(`LFml.srcL? .pre false`), fewer than `2^256` ledger reads, its ledger cut
then cut within the size bound. -/
def LFml.ledgerBlockCovered (ψ : LFml C) : Bool :=
  let body := (ψ.liftCond condLiftFuel).stripAll
  let P := apfPrep body.2
  decide ((ψ.liftCond condLiftFuel).allDepth < 1024) &&
    (ψ.liftCondB condLiftFuel liftBudget).isSome &&
    body.2.freeParams.all (fun q => decide (q ∈ body.1)) &&
    (P.body.srcL? .pre false).isSome &&
    decide (P.body.netReads.length ≤ 2 ^ 256) &&
    decide (P.body.ledgerCut.cutAll.nodes ≤ 511)

/-- **The fragment of the decision with ledger blocks.** -/
def _root_.Solidity.Fml.ledgerBlockCovered (φ : Fml C []) : Bool :=
  match leafOf? φ with
  | some ψ => ψ.ledgerBlockCovered
  | none => false

/-- **The decision with ledger blocks never refuses its fragment.** -/
theorem ledgerBlockReduction?_isSome (φ : Fml C []) (h : φ.ledgerBlockCovered = true) :
    (ledgerBlockReduction? φ).isSome = true := by
  unfold Fml.ledgerBlockCovered at h
  cases hl : leafOf? φ with
  | none => rw [hl] at h; cases h
  | some ψ =>
    rw [hl] at h
    simp only [leafOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨d, hd, r, hr, rfl⟩ := hl
    simp only [LFml.ledgerBlockCovered, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hdepth, hcap⟩, hcov⟩, hsrc⟩, hlen⟩, hnodes⟩ := h
    obtain ⟨u, hu, hup, hub⟩ := UniversalPrefix.ofFormula?_strip _ 1024 hdepth
    have hc : ∀ q ∈ u.body.freeParams, q ∈ u.parameters := by
      rw [hub, hup]; exact hcov
    have hnone : (r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget).isNone = false := by
      cases hX : r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget with
      | none => rw [hX] at hcap; cases hcap
      | some _ => rfl
    obtain ⟨⟨hs⟩, -⟩ := Option.isSome_iff_exists.mp (hub ▸ hsrc)
    obtain ⟨hcut, hok⟩ := LFml.ledgerCut_src hs
    obtain ⟨-, hreads, -⟩ := LFml.SrcL.netCut hs 0
    obtain ⟨qs, hqs⟩ := Option.isSome_iff_exists.mp
      (readExprs?_isSome (rs := (apfPrep u.body).body.netReads) fun a ha => (hreads a ha).readExpr)
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp
      (flattenedArithmeticZ?_isSome (apfPrep u.body).body.ledgerCut hcut (hub ▸ hnodes))
    have hlen' : (apfPrep u.body).body.netReads.length ≤ 2 ^ 256 := hub ▸ hlen
    simp only [ledgerBlockReduction?, hd, hr, hu, Option.bind_eq_bind, Option.bind_some,
      hnone, Bool.false_eq_true, if_false]
    rw [dif_pos hc, dif_pos hok, dif_pos hlen', hqs]
    simp only [Option.bind_some, hF]
    rfl

/-- info: 'Solidity.Decide.ledgerBlockReduction?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ledgerBlockReduction?_isSome

/-- info: 'Solidity.Decide.LedgerBlockReduction.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LedgerBlockReduction.verify

end Solidity.Decide
