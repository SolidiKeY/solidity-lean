import Solidity.Calculus.Completeness
import Solidity.Calculus.Uniqueness

/-!
# Exclusivity-based construction of `FirstStepCase`

`find_pinned_step` used to establish `FirstStepCase` by walking the ~190-entry
`Rules.stepCases` list, discharging a "this rule does not apply" obligation for
every rule before the pinned one (`rule_simp`+`decide` each). Mutual exclusion
(`UniquenessAux.stepCases_exclusive`) makes that walk redundant: once the
pinned rule *applies*, no other rule can, so every skip follows abstractly.

`firstStepCase_box`/`firstStepCase_diamond` package this: three decidable
side conditions (membership of the rule name, mode applicability, the rule's
own condition) yield the full `FirstStepCase` in one application, independent
of the rule's position in the list.

`firstStepCase_both` is the same claim for the block modality `.both`, where
the mode check says nothing and exclusivity genuinely fails -- a twin pair
applies at one statement. What replaces it there is the box and the diamond
oracle *agreeing* on the pinned rule, which a twin pair is exactly the case
that cannot. The worked derivations are all written `<[ … ]>`, so until this
existed every step of every one of them walked the list.

(Added during the Lean 4.24 migration: per-skip `simp` slowed ~60× versus
4.29, so the O(#rules) search became the build bottleneck. This module is also
the dispatch core reused by `Wp/StepSoundness.lean`.)
-/

namespace Solidity
namespace UniquenessAux

open Rules

/-- Any two applicable steps of `Rules.stepCases` coincide (mutual
exclusion, membership form). -/
theorem stepApplicable_eq {m : Modality} {stmt : Stmt} {s₁ s₂ : StepCase}
    (h₁ : s₁ ∈ Rules.stepCases) (h₂ : s₂ ∈ Rules.stepCases)
    (ha₁ : StepApplicable m stmt s₁) (ha₂ : StepApplicable m stmt s₂) :
    s₁ = s₂ := by
  rcases List.get_of_mem h₁ with ⟨i, rfl⟩
  rcases List.get_of_mem h₂ with ⟨j, rfl⟩
  by_cases hij : i = j
  · rw [hij]
  · exact absurd ha₂ (stepCases_exclusive m stmt i j hij ha₁)

/-- Core induction: an applicable step drawn from `Rules.stepCases` is the
first applicable step of any sublist containing it. -/
theorem firstStepCase_of_applicable_aux {sm : SolidityModality} {m : Modality}
    (hsm : ∀ cm, sm.appliesCaseMode cm = cm.applies m)
    {stmt : Stmt} {step : StepCase}
    (hmode : (step.effect.mode stmt).applies m = true)
    (hcond : step.effect.cond stmt)
    (hglobal : step ∈ Rules.stepCases) :
    ∀ cases : List StepCase, step ∈ cases ->
      (∀ x ∈ cases, x ∈ Rules.stepCases) ->
      FirstStepCase sm stmt cases step
        (step.effect.cond stmt) (step.effect.block stmt hcond)
  | [], hmem, _ => nomatch hmem
  | hd :: tl, hmem, hsub => by
      by_cases happ :
          sm.appliesCaseMode (hd.effect.mode stmt) = true ∧
            hd.effect.cond stmt
      · have hhd : StepApplicable m stmt hd := by
          refine ⟨?_, happ.2⟩
          rw [← hsm]
          exact happ.1
        have heq : hd = step :=
          stepApplicable_eq (hsub hd List.mem_cons_self) hglobal
            hhd ⟨hmode, hcond⟩
        subst heq
        exact FirstStepCase.here happ.1 happ.2
      · rcases List.mem_cons.mp hmem with heq | htl
        · subst heq
          refine absurd ⟨?_, hcond⟩ happ
          rw [hsm]
          exact hmode
        · exact FirstStepCase.there happ
            (firstStepCase_of_applicable_aux hsm hmode hcond hglobal tl htl
              (fun x hx => hsub x (List.mem_cons_of_mem hd hx)))

/-- A rule of the calculus's step case is a member of the generated rule list. -/
theorem stepCase_mem_stepCases {r : RuleName}
    (h : r ∈ Rules.ruleNames) :
    Rules.stepCase r ∈ Rules.stepCases := by
  exact Rules.mem_stepCases_iff.mpr ⟨r, h, rfl⟩

/-- `FirstStepCase` for a pinned rule of the calculus under the box modality: the
rule's membership, mode check, and condition suffice — no per-rule skip
proofs. -/
theorem firstStepCase_box {stmt : Stmt} {r : RuleName}
    (hmem : r ∈ Rules.ruleNames)
    (hmode : ((Rules.stepCase r).effect.mode stmt).applies Modality.box = true)
    (hcond : (Rules.stepCase r).effect.cond stmt) :
    FirstStepCase SolidityModality.box stmt Rules.stepCases
      (Rules.stepCase r)
      ((Rules.stepCase r).effect.cond stmt)
      ((Rules.stepCase r).effect.block stmt hcond) :=
  firstStepCase_of_applicable_aux (m := Modality.box) (fun _ => rfl)
    hmode hcond (stepCase_mem_stepCases hmem) Rules.stepCases
    (stepCase_mem_stepCases hmem) (fun _ hx => hx)

/-- `FirstStepCase` for a pinned rule of the calculus under the diamond modality. -/
theorem firstStepCase_diamond {stmt : Stmt} {r : RuleName}
    (hmem : r ∈ Rules.ruleNames)
    (hmode :
      ((Rules.stepCase r).effect.mode stmt).applies Modality.diamond = true)
    (hcond : (Rules.stepCase r).effect.cond stmt) :
    FirstStepCase SolidityModality.diamond stmt Rules.stepCases
      (Rules.stepCase r)
      ((Rules.stepCase r).effect.cond stmt)
      ((Rules.stepCase r).effect.block stmt hcond) :=
  firstStepCase_of_applicable_aux (m := Modality.diamond) (fun _ => rfl)
    hmode hcond (stepCase_mem_stepCases hmem) Rules.stepCases
    (stepCase_mem_stepCases hmem) (fun _ hx => hx)

/-- Every case mode admits at least one modality. -/
theorem applies_box_or_diamond (cm : CaseMode) :
    cm.applies Modality.box = true ∨ cm.applies Modality.diamond = true := by
  cases cm <;> decide

/-- Core induction for the block modality `.both`.  `appliesCaseMode .both` is
constantly `true`, so the mode half of `StepApplicable` says nothing there and
the exclusivity `firstStepCase_box` rests on is *false*: a box twin and its
diamond twin apply at the same statement.

What survives is that every case mode admits box or diamond
(`applies_box_or_diamond`), so an applicable rule is the box candidate or the
diamond candidate.  A rule that is both is therefore the only applicable one,
and the skips follow abstractly again. -/
theorem firstStepCase_both_aux {stmt : Stmt} {r : RuleName}
    (hbox : candidate Modality.box stmt = some r)
    (hdia : candidate Modality.diamond stmt = some r)
    (hcond : (Rules.stepCase r).effect.cond stmt) :
    ∀ cases : List StepCase, Rules.stepCase r ∈ cases ->
      (∀ x ∈ cases, x ∈ Rules.stepCases) ->
      FirstStepCase SolidityModality.both stmt cases (Rules.stepCase r)
        ((Rules.stepCase r).effect.cond stmt)
        ((Rules.stepCase r).effect.block stmt hcond)
  | [], hmem, _ => nomatch hmem
  | hd :: tl, hmem, hsub => by
      by_cases happ :
          SolidityModality.both.appliesCaseMode (hd.effect.mode stmt) = true ∧
            hd.effect.cond stmt
      · obtain ⟨y, hy, rfl⟩ :=
          Rules.mem_stepCases_iff.mp (hsub hd List.mem_cons_self)
        have hyr : y = r := by
          rcases applies_box_or_diamond ((Rules.stepCase y).effect.mode stmt)
            with h | h
          · exact Option.some.inj
              ((applicable_eq_candidate hy h happ.2).symm.trans hbox)
          · exact Option.some.inj
              ((applicable_eq_candidate hy h happ.2).symm.trans hdia)
        subst hyr
        exact FirstStepCase.here happ.1 happ.2
      · rcases List.mem_cons.mp hmem with heq | htl
        · subst heq
          exact absurd ⟨rfl, hcond⟩ happ
        · exact FirstStepCase.there happ
            (firstStepCase_both_aux hbox hdia hcond tl htl
              (fun x hx => hsub x (List.mem_cons_of_mem hd hx)))

/-- `FirstStepCase` for a pinned rule under the **block** modality `.both`,
the one the worked derivations are written in (`<[ … ]>`): the two oracle
queries and the rule's own condition, and no per-rule skip proof.

Both queries are one `decide`: `candidate` is a total structural dispatch, not
a search.  They are what fails for the twelve box twins -- their diamond
partner is the diamond candidate, so a statement covered by a twin pair still
takes the positional walk, which is what picks the box twin. -/
theorem firstStepCase_both {stmt : Stmt} {r : RuleName}
    (hmem : r ∈ Rules.ruleNames)
    (hbox : candidate Modality.box stmt = some r)
    (hdia : candidate Modality.diamond stmt = some r)
    (hcond : (Rules.stepCase r).effect.cond stmt) :
    FirstStepCase SolidityModality.both stmt Rules.stepCases
      (Rules.stepCase r)
      ((Rules.stepCase r).effect.cond stmt)
      ((Rules.stepCase r).effect.block stmt hcond) :=
  firstStepCase_both_aux hbox hdia hcond Rules.stepCases
    (stepCase_mem_stepCases hmem) (fun _ hx => hx)

/-! ### Box/diamond twins are effect-identical up to mode

Under the block modality `.both` a twin pair is applicable simultaneously
(`SolidityModality.appliesCaseMode`), and `FirstStepCase` picks the box
twin, listed first in `ruleNames`.  These certificates show that the
choice is one of name only: each diamond twin's effect *is* the box twin's
effect with the mode replaced. -/

theorem storageIndexWriteCopySource_twin :
    Rules.ruleEffect .storageIndexWriteArrayCopySourceDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexWriteArrayCopySourceBox) := rfl

theorem memoryToStorageIndexArrayCopyRoot_twin :
    Rules.ruleEffect .memoryToStorageIndexArrayCopyRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryToStorageIndexArrayCopyRootBox) := rfl

theorem storageIndexWriteSave_twin :
    Rules.ruleEffect .storageIndexWriteArraySaveDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexWriteArraySaveBox) := rfl

theorem storageIndexReadFind_twin :
    Rules.ruleEffect .storageIndexReadArrayFindDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexReadArrayFindBox) := rfl

theorem storageIndexReadBindLocalRoot_twin :
    Rules.ruleEffect .storageIndexReadArrayBindLocalRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexReadArrayBindLocalRootBox) := rfl

theorem storageIndexReadStoreRoot_twin :
    Rules.ruleEffect .storageIndexReadArrayStoreRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexReadArrayStoreRootBox) := rfl

theorem storagePopSave_twin :
    Rules.ruleEffect .storagePopSaveDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storagePopSaveBox) := rfl

theorem memoryIndexWriteCopy_twin :
    Rules.ruleEffect .memoryIndexWriteCopyDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexWriteCopyBox) := rfl

theorem memoryIndexWriteStore_twin :
    Rules.ruleEffect .memoryIndexWriteStoreDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexWriteStoreBox) := rfl

theorem memoryIndexReadHeap_twin :
    Rules.ruleEffect .memoryIndexReadHeapDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexReadHeapBox) := rfl

theorem memoryIndexReadAliasRoot_twin :
    Rules.ruleEffect .memoryIndexReadAliasRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexReadAliasRootBox) := rfl

theorem revert_twin :
    Rules.ruleEffect .revertDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .revertBox) := rfl

/-- The twelve twin pairs, as one fact (`twinEffects`). -/
theorem twinEffects :
    Rules.ruleEffect .storageIndexWriteArrayCopySourceDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexWriteArrayCopySourceBox) ∧
    Rules.ruleEffect .memoryToStorageIndexArrayCopyRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryToStorageIndexArrayCopyRootBox) ∧
    Rules.ruleEffect .storageIndexWriteArraySaveDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexWriteArraySaveBox) ∧
    Rules.ruleEffect .storageIndexReadArrayFindDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexReadArrayFindBox) ∧
    Rules.ruleEffect .storageIndexReadArrayBindLocalRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexReadArrayBindLocalRootBox) ∧
    Rules.ruleEffect .storageIndexReadArrayStoreRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storageIndexReadArrayStoreRootBox) ∧
    Rules.ruleEffect .storagePopSaveDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .storagePopSaveBox) ∧
    Rules.ruleEffect .memoryIndexWriteCopyDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexWriteCopyBox) ∧
    Rules.ruleEffect .memoryIndexWriteStoreDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexWriteStoreBox) ∧
    Rules.ruleEffect .memoryIndexReadHeapDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexReadHeapBox) ∧
    Rules.ruleEffect .memoryIndexReadAliasRootDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .memoryIndexReadAliasRootBox) ∧
    Rules.ruleEffect .revertDiamond =
      Rules.withMode CaseMode.diamond
        (Rules.ruleEffect .revertBox) :=
  ⟨storageIndexWriteCopySource_twin, memoryToStorageIndexArrayCopyRoot_twin,
    storageIndexWriteSave_twin, storageIndexReadFind_twin,
    storageIndexReadBindLocalRoot_twin, storageIndexReadStoreRoot_twin,
    storagePopSave_twin, memoryIndexWriteCopy_twin, memoryIndexWriteStore_twin,
    memoryIndexReadHeap_twin, memoryIndexReadAliasRoot_twin, revert_twin⟩

end UniquenessAux

/-! ### The box twin comes first

The twelve pairs above are effect-identical up to mode, so under the block
modality `.both` *both* members apply and `FirstStepCase` takes whichever
`Rules.ruleNames` lists first (`FirstStepCase.here`/`.there` walk the list
in order, and `steps!` asks the `.box` oracle on the strength of that).  Which
name comes out is therefore observable — it is the name a `⇝[.rule]`
derivation has to pin — and until now nothing checked it.

This is that check.  It is a statement about the *order* of `ruleNames`,
so it is what a reordering of that list has to preserve; `Rules.lean`'s module
docstring states the convention it enforces. -/

/-- Every box twin precedes its diamond twin in `Rules.ruleNames`. -/
theorem twins_box_first :
    ([ (RuleName.storageIndexWriteArraySaveBox, RuleName.storageIndexWriteArraySaveDiamond),
       (.storageIndexWriteArrayCopySourceBox, .storageIndexWriteArrayCopySourceDiamond),
       (.storageIndexReadArrayFindBox, .storageIndexReadArrayFindDiamond),
       (.storageIndexReadArrayBindLocalRootBox, .storageIndexReadArrayBindLocalRootDiamond),
       (.storageIndexReadArrayStoreRootBox, .storageIndexReadArrayStoreRootDiamond),
       (.storagePopSaveBox, .storagePopSaveDiamond),
       (.memoryIndexWriteStoreBox, .memoryIndexWriteStoreDiamond),
       (.memoryIndexWriteCopyBox, .memoryIndexWriteCopyDiamond),
       (.memoryIndexReadHeapBox, .memoryIndexReadHeapDiamond),
       (.memoryIndexReadAliasRootBox, .memoryIndexReadAliasRootDiamond),
       (.memoryToStorageIndexArrayCopyRootBox, .memoryToStorageIndexArrayCopyRootDiamond),
       (.revertBox, .revertDiamond) ] : List (RuleName × RuleName)).all
      (fun p => Rules.ruleNames.idxOf p.1 < Rules.ruleNames.idxOf p.2)
      = true := by
  native_decide


/-- `FirstStepCase` is a partial function of the block modality and the
statement: two first steps over the same case list agree on the step
case, the condition and the residual block.  In particular the step
relation is deterministic under `.both`, where a twin pair is applicable
simultaneously (the box twin, listed first, is the one taken). -/
theorem FirstStepCase.functional {sm : SolidityModality} {stmt : Stmt}
    {cases : List StepCase} {s₁ s₂ : StepCase} {c₁ c₂ : Prop}
    {b₁ b₂ : Block}
    (h₁ : FirstStepCase sm stmt cases s₁ c₁ b₁)
    (h₂ : FirstStepCase sm stmt cases s₂ c₂ b₂) :
    s₁ = s₂ ∧ c₁ = c₂ ∧ b₁ = b₂ := by
  induction h₁ with
  | here hmode hcond =>
      cases h₂ with
      | here _ _ => exact ⟨rfl, rfl, rfl⟩
      | there hskip _ => exact absurd ⟨hmode, hcond⟩ hskip
  | there hskip _ ih =>
      cases h₂ with
      | here hmode hcond => exact absurd ⟨hmode, hcond⟩ hskip
      | there _ h => exact ih h

end Solidity
