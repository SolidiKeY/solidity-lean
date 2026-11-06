import Solidity.Calculus.Decision
import Solidity.Calculus.DecisionNormalizationResidue
import Solidity.Calculus.DecisionPrefixNormalizationResidue
import Solidity.Calculus.DecisionMappingFieldReason
import Solidity.Calculus.DecisionArrayReasons

/-!
# The residue and `DecisionTheorem'` (M7-next, AU01)

`Fml.Residue` is the set of leaves on which **every route of `decideGoal`
refuses**, each route's refusal named (`RouteRefusal`). A leaf route's refusal
is computed from its own front end, never from `decideGoal`: a reduction
returning `none`, a source answer returning `none`, or a guard that does not
hold. The one exception is the hash route: a hash try is itself a decision
(it runs `decideLeaf` on its swapped leaf and instances), so `Fml.hashRefuses`
is stated on each try's own verdict. The residue is decidable and evaluates
in the kernel.

The user chose this form on 2026-11-06 (question Q1 of the `m7-decision`
lane, `docs/feature-work/m7-next.md`). **It is exact by construction**:
`residue_iff_unknown` proves `φ.Residue ↔ decideGoal φ = .unknown`, so
`DecisionTheorem'`'s totality off the residue holds *by definition* and is
**not a completeness result**: it does not say which in-target leaves are
answered. What it does prove beyond the definition is that every answer
off the residue is correct (a proof is validity under the goal's own hash
premise, a refutation a certified countermodel) and that the verdict is
exact there (`decideGoal_proved_iff_off_residue`). The structural question,
which source shapes fall in the residue, stays open: VA1's source classes
(`Fml.sourceReasons`) are attached as labels to residue leaves
(`Fml.residueReasons`), but nothing proves that a member of a class is in the
residue.
-/

namespace Solidity.Decide

open Linear

variable {C : Contract}

/-- `true` when the verdict is `unknown`. -/
def LeafVerdict.isUnknown : LeafVerdict C → Bool
  | .unknown => true
  | _ => false

theorem LeafVerdict.isUnknown_iff {v : LeafVerdict C} : v.isUnknown = true ↔ v = .unknown := by
  cases v <;> simp only [LeafVerdict.isUnknown, reduceCtorEq, Bool.false_eq_true]

/-! ## The routes and their refusals -/

/-- **The routes of `decideGoal`**, each named by what refuses. On a leaf
without a hash the first ten are tried in this order (`leafRoutes`); on a leaf
with a hash `decideGoal` tries only `hash`, in their place. -/
inductive RouteRefusal where
  /-- `dependentReduction?` returns `none` (M4's exact fragment: a universal
  prefix over quantifier-free arithmetic). -/
  | dependent
  /-- `quantReduction?` returns `none` (Presburger quantifiers, APF blocks). -/
  | quant
  /-- `arrayReduction?` returns `none` (storage arrays at symbolic indices). -/
  | array
  /-- `ledgerReduction?` returns `none` (reads of the starting ledger). -/
  | ledger
  /-- `ledgerBlockReduction?` returns `none` (blocks over the ledger). -/
  | ledgerBlock
  /-- `arrayBlockReduction?` returns `none` (blocks over storage arrays). -/
  | arrayBlock
  /-- The memory route refuses: with fresh allocation, the fresh-array cut's
  leaf refuses every reduction above, or there is no cut and no fresh-struct
  answer; without, no given-heap answer. -/
  | memory
  /-- The KeY `int` route refuses: its guard fails or the ledger reading
  refuses every reduction above. -/
  | kint
  /-- The two-word KeY `int` route refuses: no encoding, or the encoded leaf
  refuses every reduction above and the `int` route. -/
  | kenc
  /-- `quantLedgerReduction?` returns `none` (quantified ledger leaves). -/
  | quantLedger
  /-- Every hash try (one, two, three kinds, written memory) answers `unknown`. -/
  | hash
  deriving DecidableEq, Repr

/-- One-line reason per route. -/
def RouteRefusal.reason : RouteRefusal → String
  | .dependent => "dependentReduction? refuses: outside M4's exact fragment (universal prefix, quantifier-free body)."
  | .quant => "quantReduction? refuses: a quantifier left that is neither Presburger nor an APF block."
  | .array => "arrayReduction? refuses: storage array reads it cannot cut."
  | .ledger => "ledgerReduction? refuses: ledger reads it cannot cut."
  | .ledgerBlock => "ledgerBlockReduction? refuses: no instantiable block over the ledger."
  | .arrayBlock => "arrayBlockReduction? refuses: no instantiable block over storage arrays."
  | .memory => "The memory route refuses: its fresh-array cut, fresh-struct or given-heap branch refuses."
  | .kint => "The KeY int route refuses: its guard fails or the ledger reading is refused."
  | .kenc => "The two-word KeY int route refuses: no encoding or the encoded leaf is refused."
  | .quantLedger => "quantLedgerReduction? refuses: no ledger cut before abstraction."
  | .hash => "Every hash try (one, two, three kinds, written memory) answers unknown."

/-- The routes tried on a leaf without a hash, in order. -/
def leafRoutes : List RouteRefusal :=
  [.dependent, .quant, .array, .ledger, .ledgerBlock, .arrayBlock, .memory, .kint, .kenc,
    .quantLedger]

/-- **The six reductions of `decideLeafA` all refuse.** -/
def _root_.Solidity.Fml.leafARefuses (φ : Fml C []) : Bool :=
  (dependentReduction? φ).isNone && (quantReduction? φ).isNone && (arrayReduction? φ).isNone &&
    (ledgerReduction? φ).isNone && (ledgerBlockReduction? φ).isNone &&
    (arrayBlockReduction? φ).isNone

/-- **The memory route refuses** (`decideMem`'s three branches). -/
def _root_.Solidity.Fml.memRefuses (φ : Fml C []) : Bool :=
  if φ.hasAllocAll then
    match ((mxNegativePrepare φ).body.hoist 1024).mxTop with
    | some ψ => ψ.leafARefuses
    | none => (structAnswerWithCompound φ).isNone
  else (givenHeapAnswerWithFixed φ).isNone

/-- **The KeY `int` route refuses** (`decideKInt`). -/
def _root_.Solidity.Fml.kintRefuses (φ : Fml C []) : Bool :=
  !(φ.hasZ && φ.zOK && decide (φ.zDepth ≤ 2 ^ 256)) || (φ.zT 0).leafARefuses

/-- **The two-word KeY `int` route refuses** (`decideKEnc`). -/
def _root_.Solidity.Fml.kencRefuses (φ : Fml C []) : Bool :=
  !φ.kencB.2 || (φ.kencB.1.leafARefuses && φ.kencB.1.kintRefuses)

/-- **The quantified-ledger route refuses** (`decideQuantLedger`). -/
def _root_.Solidity.Fml.quantLedgerRefuses (φ : Fml C []) : Bool :=
  (quantLedgerReduction? φ).isNone

/-- **Every route for a leaf without a hash refuses** (`decideLeaf`). -/
def _root_.Solidity.Fml.leafRefuses (φ : Fml C []) : Bool :=
  φ.leafARefuses && φ.memRefuses && φ.kintRefuses && φ.kencRefuses && φ.quantLedgerRefuses

/-- **Every hash try refuses** (`decideHash`). -/
def _root_.Solidity.Fml.hashRefuses (φ : Fml C []) : Bool :=
  (hashTries (C := C)).all (fun T => (T.run φ).isUnknown)

/-- **The residue, computed**: on a leaf with a hash, every hash try refuses;
on one without, every leaf route refuses. -/
def _root_.Solidity.Fml.residue (φ : Fml C []) : Bool :=
  if φ.hasHash then φ.hashRefuses else φ.leafRefuses

/-- **`Fml.Residue`**: the leaves every route of `decideGoal` refuses. -/
def _root_.Solidity.Fml.Residue (φ : Fml C []) : Prop := φ.residue = true

instance (φ : Fml C []) : Decidable φ.Residue := inferInstanceAs (Decidable (φ.residue = true))

/-! ## Each refusal is exactly its route's `unknown` -/

theorem decideLeafA_unknown_iff {φ : Fml C []} :
    decideLeafA φ = .unknown ↔ φ.leafARefuses = true := by
  unfold decideLeafA Fml.leafARefuses
  cases dependentReduction? φ with
  | some r => simp only [Option.isNone_some, Bool.false_and]; split <;> simp only [reduceCtorEq]
  | none =>
  cases quantReduction? φ with
  | some r => simp only [Option.isNone_some, Option.isNone_none, Bool.true_and, Bool.false_and]
              split <;> simp only [reduceCtorEq]
  | none =>
  cases arrayReduction? φ with
  | some r => simp only [Option.isNone_some, Option.isNone_none, Bool.true_and, Bool.false_and]
              split <;> simp only [reduceCtorEq]
  | none =>
  cases ledgerReduction? φ with
  | some r => simp only [Option.isNone_some, Option.isNone_none, Bool.true_and, Bool.false_and]
              split <;> simp only [reduceCtorEq]
  | none =>
  cases ledgerBlockReduction? φ with
  | some r => simp only [Option.isNone_some, Option.isNone_none, Bool.true_and, Bool.false_and]
              split <;> simp only [reduceCtorEq]
  | none =>
  cases arrayBlockReduction? φ with
  | some r => simp only [Option.isNone_some, Option.isNone_none, Bool.true_and]
              split <;> simp only [reduceCtorEq]
  | none => simp only [Option.isNone_none, Bool.and_self]

theorem decideStruct_unknown_iff {φ : Fml C []} :
    decideStruct φ = .unknown ↔ (structAnswerWithCompound φ).isNone = true := by
  unfold decideStruct
  cases structAnswerWithCompound φ with
  | none => simp only [Option.isNone_none]
  | some a => cases a <;> simp only [reduceCtorEq, Option.isNone_some, Bool.false_eq_true]

theorem decideGiven_unknown_iff {φ : Fml C []} :
    decideGiven φ = .unknown ↔ (givenHeapAnswerWithFixed φ).isNone = true := by
  unfold decideGiven
  cases givenHeapAnswerWithFixed φ with
  | none => simp only [Option.isNone_none]
  | some a => cases a <;> simp only [reduceCtorEq, Option.isNone_some, Bool.false_eq_true]

theorem decideMem_unknown_iff {φ : Fml C []} :
    decideMem φ = .unknown ↔ φ.memRefuses = true := by
  unfold decideMem Fml.memRefuses
  split
  · cases ((mxNegativePrepare φ).body.hoist 1024).mxTop with
    | some ψ => exact decideLeafA_unknown_iff
    | none => exact decideStruct_unknown_iff
  · exact decideGiven_unknown_iff

theorem decideKInt_unknown_iff {φ : Fml C []} :
    decideKInt φ = .unknown ↔ φ.kintRefuses = true := by
  unfold decideKInt Fml.kintRefuses
  split
  · rename_i hc
    rw [hc]
    simp only [Bool.not_true, Bool.false_or]
    exact decideLeafA_unknown_iff
  · rename_i hc
    simp only [Bool.not_eq_true] at hc
    rw [hc]
    simp only [Bool.not_false, Bool.true_or]

theorem decideKEnc_unknown_iff {φ : Fml C []} :
    decideKEnc φ = .unknown ↔ φ.kencRefuses = true := by
  unfold decideKEnc Fml.kencRefuses
  split
  · rename_i hb
    rw [hb]
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
    cases ha : decideLeafA φ.kencB.1 with
    | unknown =>
      simp only
      exact ⟨fun h => ⟨decideLeafA_unknown_iff.1 ha, decideKInt_unknown_iff.1 h⟩,
        fun h => decideKInt_unknown_iff.2 h.2⟩
    | proved =>
      simp only [reduceCtorEq, false_iff, not_and]
      exact fun h => absurd (decideLeafA_unknown_iff.2 h) (by rw [ha]; exact fun h => nomatch h)
    | refuted σ =>
      simp only [reduceCtorEq, false_iff, not_and]
      exact fun h => absurd (decideLeafA_unknown_iff.2 h) (by rw [ha]; exact fun h => nomatch h)
  · rename_i hb
    simp only [Bool.not_eq_true] at hb
    rw [hb]
    simp only [Bool.not_false, Bool.true_or]

theorem decideQuantLedger_unknown_iff {φ : Fml C []} :
    decideQuantLedger φ = .unknown ↔ φ.quantLedgerRefuses = true := by
  unfold decideQuantLedger Fml.quantLedgerRefuses
  cases quantLedgerReduction? φ with
  | none => simp only [Option.isNone_none]
  | some r => simp only [Option.isNone_some, Bool.false_eq_true, iff_false]; split <;> simp only [reduceCtorEq, not_false_eq_true]

theorem decideLeaf_unknown_iff {φ : Fml C []} :
    decideLeaf φ = .unknown ↔ φ.leafRefuses = true := by
  unfold decideLeaf Fml.leafRefuses
  simp only [Bool.and_eq_true]
  rw [← decideLeafA_unknown_iff, ← decideMem_unknown_iff, ← decideKInt_unknown_iff,
    ← decideKEnc_unknown_iff, ← decideQuantLedger_unknown_iff]
  cases decideLeafA φ <;> cases decideMem φ <;> cases decideKInt φ <;> cases decideKEnc φ <;>
    simp only [reduceCtorEq, false_and, and_false, and_true, true_and, iff_self]

theorem firstKnown_unknown_iff {φ : Fml C []} :
    (ts : List (Fml C [] → LeafVerdict C)) →
      firstKnown ts φ = .unknown ↔ ts.all (fun t => (t φ).isUnknown) = true
  | [] => by simp only [firstKnown, List.all_nil]
  | t :: ts => by
    unfold firstKnown
    simp only [List.all_cons, Bool.and_eq_true, LeafVerdict.isUnknown_iff]
    split
    · rename_i hu
      simp only [hu, true_and]
      exact firstKnown_unknown_iff ts
    · rename_i hv
      exact ⟨fun h => absurd h hv, fun h => absurd h.1 hv⟩

theorem decideHash_unknown_iff {φ : Fml C []} :
    decideHash φ = .unknown ↔ φ.hashRefuses = true := by
  unfold decideHash Fml.hashRefuses
  rw [firstKnown_unknown_iff, List.all_map]
  rfl

/-- **The residue is exact**: a leaf is in it exactly when `decideGoal`
answers `unknown`. This is why totality off the residue below holds by
definition. -/
theorem residue_iff_unknown {φ : Fml C []} : φ.Residue ↔ decideGoal φ = .unknown := by
  unfold Fml.Residue Fml.residue decideGoal
  split
  · exact decideHash_unknown_iff.symm
  · exact decideLeaf_unknown_iff.symm

/-! ## The theorem -/

/-- **`DecisionTheorem'`** (M7-next). On every leaf in the target (any
`Waivers`) and outside `Fml.Residue`, `decideGoal` either proves it, and the
leaf is valid under its own hash premise (`Fml.ValidH`, e3′; no global
premise), or refutes it with a state whose instance meets that premise and
falsifies the leaf.

**Totality off the residue holds by definition, so this is not a
completeness result.** `Fml.Residue` is exactly the set of leaves every route
refuses (`residue_iff_unknown`); the theorem does not say which in-target
leaves avoid it. The content beyond the definition is the correctness of
each answer. The target premise is not used by the proof: it is stated to
keep the theorem about the user's fragment, as `DecisionTheorem` is. -/
theorem DecisionTheorem' (w : Waivers := {}) (C : Contract) (φ : Fml C [])
    (_hφ : φ.inTarget w = true) (hr : ¬ φ.Residue) :
    (decideGoal φ = .proved ∧ Fml.ValidH φ) ∨
      (∃ σ : State C [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ) := by
  cases hd : decideGoal φ with
  | proved => exact .inl ⟨rfl, decideGoal_sound hd⟩
  | refuted σ => exact .inr ⟨σ, rfl, decideGoal_refutes hd⟩
  | unknown => exact absurd (residue_iff_unknown.2 hd) hr

/-- Off the residue the verdict is exact: `proved` exactly on the leaves
valid under their hash premise. -/
theorem decideGoal_proved_iff_off_residue {φ : Fml C []} (hr : ¬ φ.Residue) :
    decideGoal φ = .proved ↔ Fml.ValidH φ := by
  refine ⟨decideGoal_sound, fun hv => ?_⟩
  cases hd : decideGoal φ with
  | proved => rfl
  | refuted σ => exact absurd (hv σ) (decideGoal_refutes hd)
  | unknown => exact absurd (residue_iff_unknown.2 hd) hr

/-- The original, unchanged goal `DecisionTheorem` says exactly that the
residue meets no in-target leaf. The milestone policy is that later rounds
shrink the residue; nothing here enforces it (a changed route can grow it). -/
theorem decisionTheorem_iff_residue_disjoint (w : Waivers) :
    DecisionTheorem w ↔ ∀ (C : Contract) (φ : Fml C []), φ.inTarget w = true → ¬ φ.Residue := by
  unfold DecisionTheorem
  exact ⟨fun h C φ hφ hr => h C φ hφ (residue_iff_unknown.1 hr),
    fun h C φ hφ hu => h C φ hφ (residue_iff_unknown.2 hu)⟩

/-! ## Finer source reasons (VA1)

Where a source class VA1 named applies to a residue leaf, it is reported
before the route refusals, as a label. These classes are decidable from the
source alone and consult no route; they are not unknown tests (a member of a
class may be answered by another route, and none is proved to be in the
residue), so they are reported only for residue leaves. VA1's halting-`||`
class is parameterized by contract roots and is not reported. -/

/-- The finer source reasons that hold of the leaf, VA1's names. -/
def _root_.Solidity.Fml.sourceReasons (φ : Fml C []) : List String :=
  (if φ.twoUIntPrefixOverNormalizationBudget then
      [ResidueReason.twoUIntPrefixOverNormalizationBudgetReason] else []) ++
  (if decide φ.PrimitivePrefixNormalizationResidue then
      [ResidueReason.primitivePrefixNormalizationReason] else []) ++
  (if φ.freshStructMappingReversedPrimitiveEquation then
      [ResidueReason.mappingReversedFreshFieldReason] else []) ++
  (match ResidueReason.sourceArrayKind? φ with
    | some k => [k.reason]
    | none => [])

/-- The route refusals of a leaf, in `decideGoal`'s order. -/
def _root_.Solidity.Fml.routeRefusals (φ : Fml C []) : List RouteRefusal :=
  if φ.hasHash then (if φ.hashRefuses then [.hash] else [])
  else leafRoutes.filter fun r => match r with
    | .dependent => (dependentReduction? φ).isNone
    | .quant => (quantReduction? φ).isNone
    | .array => (arrayReduction? φ).isNone
    | .ledger => (ledgerReduction? φ).isNone
    | .ledgerBlock => (ledgerBlockReduction? φ).isNone
    | .arrayBlock => (arrayBlockReduction? φ).isNone
    | .memory => φ.memRefuses
    | .kint => φ.kintRefuses
    | .kenc => φ.kencRefuses
    | .quantLedger => φ.quantLedgerRefuses
    | .hash => false

/-- **The reasons of a residue leaf**: VA1's finer source reasons that
apply, then every route's refusal. Empty exactly off the residue. -/
def _root_.Solidity.Fml.residueReasons (φ : Fml C []) : List String :=
  if φ.residue then φ.sourceReasons ++ φ.routeRefusals.map RouteRefusal.reason else []

theorem residueReasons_eq_nil_iff {φ : Fml C []} : φ.residueReasons = [] ↔ ¬ φ.Residue := by
  unfold Fml.residueReasons Fml.Residue
  cases h : φ.residue with
  | false => simp only [Bool.false_eq_true, ite_false, not_false_eq_true]
  | true =>
    simp only [ite_true, List.append_eq_nil_iff, List.map_eq_nil_iff, not_true_eq_false, iff_false,
      not_and]
    intro _
    unfold Fml.routeRefusals
    unfold Fml.residue at h
    split
    · rename_i hh; rw [hh] at h; simp only [ite_true] at h; simp only [h, ite_true]; exact fun h => nomatch h
    · rename_i hh
      simp only [Bool.not_eq_true] at hh
      rw [hh] at h
      simp only [Bool.false_eq_true, ite_false, Fml.leafRefuses, Fml.leafARefuses,
        Bool.and_eq_true] at h
      simp only [leafRoutes, List.filter_cons, h.1.1.1.1.1.1.1.1.1, ite_true]
      exact fun h => nomatch h

/-- info: 'Solidity.Decide.DecisionTheorem'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DecisionTheorem'

/-- info: 'Solidity.Decide.residue_iff_unknown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms residue_iff_unknown

/-- info: 'Solidity.Decide.decideGoal_proved_iff_off_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_proved_iff_off_residue

/-- info: 'Solidity.Decide.decisionTheorem_iff_residue_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decisionTheorem_iff_residue_disjoint

end Solidity.Decide
