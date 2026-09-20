import Solidity.Calculus.Rules

/-!
# First steps, and what "the calculus covers this statement" means

`FirstStepCase sm stmt cases step cond block` is the evidence that `step` is
the *first* rule of `cases` whose condition holds at `stmt` — the pinned rule,
plus the obligation that every rule before it does not apply.  `RuleStep` is
that evidence with the rule existentially closed, and it is the relation
`MultiStep.lean`'s arrows are built from.

The pair `step_of_ruleApplies` / `ruleApplies_of_ruleStep` is a definitional
equivalence, not a completeness result: `ruleApplies` *means* "some rule's
condition holds", so a first step characterizes rule coverage in both
directions.  Completeness proper is `RuleStep.complete_of_wellTyped` in
`Coverage.lean`, which is a statement about the *typed* fragment and so needs
the typing layer; the two are deliberately separate files for that reason.

What makes the list walk avoidable is mutual exclusion — see
`CandidateStep.lean`, which rebuilds a `FirstStepCase` from three decidable
side conditions instead of ~190 skip proofs.
-/

set_option maxHeartbeats 2000000

namespace Solidity

open Rules

namespace Rules

def stepCases : List StepCase :=
  rules

/-- The rule list as seen from a concrete statement.  It does not depend on
the statement (dispatch is by `FirstStepCase`); kept as a named entry point
for the counterexample files that filter it. -/
def concreteStepCases (_stmt : Stmt) : List StepCase :=
  stepCases

theorem mem_stepCases_iff {step : StepCase} :
    step ∈ stepCases ↔ ∃ rule ∈ ruleNames, step = stepCase rule := by
  simp only [stepCases, rules, ruleCases, List.mem_map]
  constructor
  · rintro ⟨rule, hmem, rfl⟩; exact ⟨rule, hmem, rfl⟩
  · rintro ⟨rule, hmem, rfl⟩; exact ⟨rule, hmem, rfl⟩

end Rules

inductive FirstStepCase (sm : SolidityModality) (stmt : Stmt) :
    List StepCase -> StepCase -> Prop -> Block -> Prop where
  | here {step : StepCase} {rest : List StepCase}
      (hmode : sm.appliesCaseMode (step.effect.mode stmt) = true)
      (hcond : step.effect.cond stmt) :
      FirstStepCase sm stmt (step :: rest) step
        (step.effect.cond stmt) (step.effect.block stmt hcond)
  | there {head step : StepCase} {rest : List StepCase}
      {cond : Prop} {block : Block}
      (hskip :
        ¬ (sm.appliesCaseMode (head.effect.mode stmt) = true ∧
          head.effect.cond stmt))
      (hfirst : FirstStepCase sm stmt rest step cond block) :
      FirstStepCase sm stmt (head :: rest) step cond block

namespace FirstStepCase

theorem cond_holds {sm : SolidityModality} {stmt : Stmt}
    {cases : List StepCase} {step : StepCase} {cond : Prop}
    {block : Block} :
    FirstStepCase sm stmt cases step cond block -> cond := by
  intro hfirst
  induction hfirst with
  | here _ hcond => exact hcond
  | there _ _ ih => exact ih

theorem mode_holds {sm : SolidityModality} {stmt : Stmt}
    {cases : List StepCase} {step : StepCase} {cond : Prop}
    {block : Block} :
    FirstStepCase sm stmt cases step cond block ->
      sm.appliesCaseMode (step.effect.mode stmt) = true := by
  intro hfirst
  induction hfirst with
  | here hmode _ => exact hmode
  | there _ _ ih => exact ih

theorem effect_cond_holds {sm : SolidityModality} {stmt : Stmt}
    {cases : List StepCase} {step : StepCase} {cond : Prop}
    {block : Block} :
    FirstStepCase sm stmt cases step cond block -> step.effect.cond stmt := by
  intro hfirst
  induction hfirst with
  | here _ hcond => exact hcond
  | there _ _ ih => exact ih

theorem mem {sm : SolidityModality} {stmt : Stmt}
    {cases : List StepCase} {step : StepCase} {cond : Prop}
    {block : Block} :
    FirstStepCase sm stmt cases step cond block -> step ∈ cases := by
  intro hfirst
  induction hfirst with
  | here _ _ => simp
  | there _ _ ih => simp [ih]

end FirstStepCase

inductive RuleStep (sm : SolidityModality) :
    Stmt -> Prop -> Block -> Prop where
  | ofStepCase {lhs : Stmt} {step : StepCase} {cond : Prop}
      {block : Block} :
      FirstStepCase sm lhs Rules.stepCases step cond block ->
      RuleStep sm lhs cond block

namespace CompletenessAux

theorem firstStepCase_of_exists {sm : SolidityModality} {stmt : Stmt} :
    ∀ cases : List StepCase,
      (∃ step, step ∈ cases ∧
        sm.appliesCaseMode (step.effect.mode stmt) = true ∧
          step.effect.cond stmt) ->
        ∃ step cond block,
          FirstStepCase sm stmt cases step cond block := by
  intro cases
  induction cases with
  | nil =>
      intro h
      rcases h with ⟨_, hmem, _⟩
      cases hmem
  | cons head tail ih =>
      intro h
      by_cases hhead :
          sm.appliesCaseMode (head.effect.mode stmt) = true ∧
            head.effect.cond stmt
      · exact ⟨head, head.effect.cond stmt,
          head.effect.block stmt hhead.2,
          FirstStepCase.here hhead.1 hhead.2⟩
      · have htail :
            ∃ step, step ∈ tail ∧
              sm.appliesCaseMode (step.effect.mode stmt) = true ∧
                step.effect.cond stmt := by
          rcases h with ⟨step, hmem, hmode, hcond⟩
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact False.elim (hhead ⟨hmode, hcond⟩)
          · exact ⟨step, hmem, hmode, hcond⟩
        rcases ih htail with ⟨step, cond, block, hfirst⟩
        exact ⟨step, cond, block, FirstStepCase.there hhead hfirst⟩

theorem stepCases_has_applicable {mode : Modality}
    (lhs : Stmt) (hrule : Rules.ruleApplies mode lhs) :
    ∃ step, step ∈ Rules.stepCases ∧
      (step.effect.mode lhs).applies mode = true ∧
        step.effect.cond lhs := by
  rcases hrule with ⟨rule, hmem, hmode, hcond⟩
  exact ⟨Rules.stepCase rule,
    Rules.mem_stepCases_iff.mpr ⟨rule, hmem, rfl⟩, hmode, hcond⟩

theorem appliesCaseMode_of_ofModality (m : Modality) (cm : CaseMode) :
    (SolidityModality.ofModality m).appliesCaseMode cm = cm.applies m := by
  cases m <;> simp [SolidityModality.ofModality, SolidityModality.appliesCaseMode]

theorem stepCases_has_applicable_ofModality (m : Modality) (lhs : Stmt)
    (hrule : Rules.ruleApplies m lhs) :
    ∃ step, step ∈ Rules.stepCases ∧
      (SolidityModality.ofModality m).appliesCaseMode (step.effect.mode lhs) = true ∧
        step.effect.cond lhs := by
  rcases stepCases_has_applicable (mode := m) lhs hrule with
    ⟨step, hmem, hmode, hcond⟩
  exact ⟨step, hmem, by rw [appliesCaseMode_of_ofModality]; exact hmode, hcond⟩

/-- Statements covered by a rule of the calculus have a first step.  The converse is
`RuleStep.ruleApplies_of_ruleStep`: the calculus has no catch-all
rule, so a first step *characterizes* rule coverage. -/
theorem firstStepCase_of_ruleApplies (m : Modality) (lhs : Stmt)
    (hrule : Rules.ruleApplies m lhs) :
    ∃ step cond block,
      FirstStepCase (.ofModality m) lhs Rules.stepCases step cond block :=
  firstStepCase_of_exists Rules.stepCases
    (stepCases_has_applicable_ofModality m lhs hrule)

end CompletenessAux

namespace RuleStep

/-- Definitional plumbing, not a completeness result: `ruleApplies`
*means* "some rule of the calculus's condition holds", and this unpacks it into a
`RuleStep`.  The completeness theorem proper —
`RuleStep.complete_of_wellTyped` in `Coverage.lean` — is stated over the
rule-independent fragment (`stmtWt`-typed statements outside the explicit
`Coverage.ResidueShape` list). -/
theorem step_of_ruleApplies (m : Modality) :
    ∀ lhs : Stmt, Rules.ruleApplies m lhs →
      ∃ cond rhs, cond ∧ RuleStep (.ofModality m) lhs cond rhs := by
  intro lhs hrule
  rcases CompletenessAux.firstStepCase_of_exists Rules.stepCases
    (CompletenessAux.stepCases_has_applicable_ofModality m lhs hrule) with
    ⟨step, cond, block, hfirst⟩
  exact ⟨cond, block, FirstStepCase.cond_holds hfirst,
    RuleStep.ofStepCase hfirst⟩

/-- The converse: every step is an application of a rule whose
condition holds.  Every `CaseMode` admits box or diamond, so the step's
modality gate is not needed — this holds for `.both` as well. -/
theorem ruleApplies_of_ruleStep {sm : SolidityModality} {stmt : Stmt}
    {cond : Prop} {rhs : Block} (h : RuleStep sm stmt cond rhs) :
    ∃ m, Rules.ruleApplies m stmt := by
  obtain ⟨hfirst⟩ := h
  have hmem := FirstStepCase.mem hfirst
  have hcond := FirstStepCase.effect_cond_holds hfirst
  obtain ⟨rule, hrule, rfl⟩ := Rules.mem_stepCases_iff.mp hmem
  obtain ⟨m, hm⟩ : ∃ m : Modality,
      ((Rules.ruleEffect rule).mode stmt).applies m = true := by
    generalize (Rules.ruleEffect rule).mode stmt = cm
    cases cm <;> first | exact ⟨.box, rfl⟩ | exact ⟨.diamond, rfl⟩
  exact ⟨m, rule, hrule, hm, hcond⟩

end RuleStep

namespace CompletenessExamples

def alice : PlaceExpr :=
  splace!{ alice }

def bob : PlaceExpr :=
  splace!{ bob }

def carol : PlaceExpr :=
  splace!{ carol }

def account : PlaceExpr :=
  splace!{ alice.account }

def balance : PlaceExpr :=
  splace!{ alice.account.balance }

def storageDeclSimple : Stmt :=
  sstmt!{ Person storage p = bob }

def complexStorageFieldAssignment : Stmt :=
  sstmt!{ alice.account.balance = amount }

def complexIndex : WrappedExpr :=
  sexpr!{ nextIndex() }

def complexIndexedAssignment : Stmt :=
  Stmt.assign
    (PlaceExpr.index Kind.storage StandardExample.personTy alice complexIndex)
    (SoliditySyntax.memoryCallExpr StandardExample.personRef "makePerson" [] rfl)

def memoryDeclaration : Stmt :=
  sstmt!{ Person memory m = carol }

def memoryToStorageAssignment : Stmt :=
  sstmt!{ alice.account = carol }

def mappingPath : WrappedExpr :=
  SoliditySyntax.varExpr Kind.storage
    (Ty.ref (RefTy.mapping Ty.uint StandardExample.personTy)) "ledger"

def memoryUintArrayPath : WrappedExpr :=
  SoliditySyntax.varExpr Kind.memory (Ty.ref (RefTy.array Ty.uint)) "memValues"

def memoryPersonArrayPath : WrappedExpr :=
  SoliditySyntax.varExpr Kind.memory
    (Ty.ref (RefTy.array StandardExample.personTy)) "memPeople"

def storageArrayWriteCopySource : Stmt :=
  sstmt!{ people[i] = bob }

def storageArrayWriteSave : Stmt :=
  sstmt!{ people[i] = amount }

def storageArrayReadFind : Stmt :=
  sstmt!{ amount = people[i] }

def storageArrayDelete : Stmt :=
  sstmt!{ delete people[i] }

def storageMappingWriteCopySource : Stmt :=
  Stmt.assign (PlaceExpr.index Kind.storage StandardExample.personTy mappingPath (sexpr!{ i }))
    (sexpr!{ bob })

def storageMappingWriteSave : Stmt :=
  Stmt.assign (PlaceExpr.index Kind.storage StandardExample.personTy mappingPath (sexpr!{ i }))
    (sexpr!{ amount })

def storageMappingReadFind : Stmt :=
  Stmt.assign (splace!{ amount })
    (WrappedExpr.index Kind.storage StandardExample.personTy mappingPath (sexpr!{ i }))

def storageMappingDelete : Stmt :=
  Stmt.delete (PlaceExpr.index Kind.storage StandardExample.personTy mappingPath (sexpr!{ i }))

def memoryIndexWriteHeap : Stmt :=
  Stmt.assign (PlaceExpr.index Kind.memory Ty.uint memoryUintArrayPath (sexpr!{ i }))
    (sexpr!{ amount })

def memoryIndexReadHeap : Stmt :=
  Stmt.assign (splace!{ amount })
    (WrappedExpr.index Kind.memory Ty.uint memoryUintArrayPath (sexpr!{ i }))

def memoryIndexReadAliasRoot : Stmt :=
  Stmt.assign (splace!{ carol })
    (WrappedExpr.index Kind.memory StandardExample.personTy
      memoryPersonArrayPath (sexpr!{ i }))

def memoryIndexDeletePrimitive : Stmt :=
  Stmt.delete (PlaceExpr.index Kind.memory Ty.uint memoryUintArrayPath (sexpr!{ i }))

def memoryIndexDeleteIdentity : Stmt :=
  Stmt.delete
    (PlaceExpr.index Kind.memory StandardExample.personTy
      memoryPersonArrayPath (sexpr!{ i }))

def memoryDeclInitSplit : Stmt :=
  sstmt!{ Person memory m = carol }

end CompletenessExamples

end Solidity
