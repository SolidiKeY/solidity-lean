import Solidity.Correctness.Lowering.Unchecked.SourceOne
import Solidity.Correctness.Lowering.Unchecked.NamedOne

/-!
# Initial raw and typed Source spelling association

Guards associating an increment with a differently named, directed, or
prefix/postfix Source input. This total syntax checker inspects both supplied
trees before composing the actual StmtD.toR checker. It does not reconstruct
or totalize uncheckStmts, mapM or narrowPure, and accepts no semantic premise.

Canonical decimal-one syntax is the initial covered compound family. Other
literal spellings, parentheses and remaining statements are coverage gaps,
not exclusions for the final validator. The supplied contexts and final model
program still need their prescribed production endpoint association.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- One syntax relation for the initial compound and prefix/postfix spellings.
The operator semantics are proved separately, once, in SourceOne. -/
inductive SourceOneSpelling {k : Source.SCtx} : RawStmt → Source.Syn (.stmt k) → Type where
  | compound (inc : Bool) (name : String) : SourceOneSpelling
      (.opAssign (if inc then .add else .sub) (.name name) (.num 1))
      (.simpleStmt (.exprStmt (.assign (if inc then .add else .sub)
        (.ident name) (.lit (.num (.dec 1 0 0))))))
  | prefix (inc : Bool) (name : String) : SourceOneSpelling
      (.incDec (if inc then .preInc else .preDec) (.name name))
      (.simpleStmt (.exprStmt (.unaryPrefix (if inc then .inc else .dec) (.ident name))))
  | suffix (inc : Bool) (name : String) : SourceOneSpelling
      (.incDec (if inc then .postInc else .postDec) (.name name))
      (.simpleStmt (.exprStmt (.unarySuffix (if inc then .inc else .dec) (.ident name))))

/-- Total initial-tree association; every accepted name/token/literal is
inspected. Rejections remain explicit incomplete coverage. -/
def checkSourceSpelling {k : Source.SCtx} :
    (input : RawStmt) → (syn : Source.Syn (.stmt k)) → Option (SourceOneSpelling input syn)
  | .opAssign .add (.name x) (.num 1),
      .simpleStmt (.exprStmt (.assign .add (.ident y) (.lit (.num (.dec 1 0 0))))) =>
    if name : x = y then some (by cases name; exact .compound true x) else none
  | .opAssign .sub (.name x) (.num 1),
      .simpleStmt (.exprStmt (.assign .sub (.ident y) (.lit (.num (.dec 1 0 0))))) =>
    if name : x = y then some (by cases name; exact .compound false x) else none
  | .incDec .preInc (.name x), .simpleStmt (.exprStmt (.unaryPrefix .inc (.ident y))) =>
    if name : x = y then some (by cases name; exact .prefix true x) else none
  | .incDec .preDec (.name x), .simpleStmt (.exprStmt (.unaryPrefix .dec (.ident y))) =>
    if name : x = y then some (by cases name; exact .prefix false x) else none
  | .incDec .postInc (.name x), .simpleStmt (.exprStmt (.unarySuffix .inc (.ident y))) =>
    if name : x = y then some (by cases name; exact .suffix true x) else none
  | .incDec .postDec (.name x), .simpleStmt (.exprStmt (.unarySuffix .dec (.ident y))) =>
    if name : x = y then some (by cases name; exact .suffix false x) else none
  | _, _ => none

/-- Both the actual initial syntax and its actual typed resolved result are
checked. Source/model context consistency and the final endpoint are absent. -/
structure TypedSourceOneAssociation {C : Source.Ctx} {k : Source.SCtx}
    {L L' : List (String × Source.STy)} {syn : Source.Syn (.stmt k)}
    (input : RawStmt) (derivation : Source.StmtD C L syn L') where
  raw : RawOneInput input
  spelling : SourceOneSpelling input syn
  resolved : SourceOneAssociation (C.at L) raw derivation.toR

/-- Total composition at the supplied typed Source boundary. All certificate
fields follow from inspected syntax, lookup or the production toR result. -/
def checkTypedSourceSpelling {C : Source.Ctx} {k : Source.SCtx}
    {L L' : List (String × Source.STy)} {syn : Source.Syn (.stmt k)}
    (input : RawStmt) (derivation : Source.StmtD C L syn L') :
    Option (TypedSourceOneAssociation input derivation) := do
  let raw ← checkRawOneInput input
  let spelling ← checkSourceSpelling input syn
  let resolved ← checkTypedSourceOne raw derivation
  pure ⟨raw, spelling, resolved⟩

/-- The checked initial spelling and actual typing derivation yield the
shared full Source normalization law. No equality for elaboration or Source
execution is assumed, and every failure/poststate is retained. This remains
a Source-only theorem, with no model state or pipeline endpoint assertion. -/
theorem typedSourceSpelling_normalize {C : Source.Ctx} {k : Source.SCtx}
    {L : List (String × Source.STy)} {syn : Source.Syn (.stmt k)}
    (input : RawStmt) (derivation : Source.StmtD C L syn L)
    (certificate : TypedSourceOneAssociation input derivation)
    (G : Source.Glob C.env) (F : Source.Fr) (horizon nps : Nat)
    (ph : Option (Source.Ph C.env)) (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (ls : Source.Locals C.env.layout (Source.tysOf L)) (st : Source.St C.env) :
    (Source.execS G F horizon nps ph derivation.toR ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) =
    (Source.execS G F horizon nps ph
      (.expr (.incDec certificate.raw.inc true (.local certificate.resolved.slot))
        : Source.RStmt C.env C.rets C.inModifier k (Source.tysOf L) (Source.tysOf L)) ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) := by
  exact sourceOne_normalize (C.at L) certificate.raw derivation.toR certificate.resolved
    G F horizon nps ph plan known ls st

/-- Transport only intrinsic context indices, never a semantic assumption. -/
def sourceStatementV4 {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (alignment : Γ = Δ)
    (statement : Source.RStmt E R M k Γ Γ) : Source.RStmt E R M k Δ Δ :=
  alignment ▸ statement

/-- The corresponding initial locals use the same intrinsic type transport. -/
def sourceLocalsV4 {D : Source.Layout} {Γ Δ : Source.RCtx} (alignment : Γ = Δ)
    (locals : Source.Locals D Γ) : Source.Locals D Δ := alignment ▸ locals

/-- Retain the supplied model program while aligning its context indices. -/
def modelProgramV4 {C : Contract} {Γ Δ : Ctx} (alignment : Γ = Δ)
    (program : Prog C Γ Γ) : Prog C Δ Δ := alignment ▸ program

/-- Context transport retains every field of the supplied model state. -/
def modelStateV4 {C : Contract} {Γ Δ : Ctx} (alignment : Γ = Δ)
    (state : State C Γ) : State C Δ := alignment ▸ state

/-- Static association of the supplied raw input/rewrite, actual Source
typing result and model program. Both named resolvers are checked on their
supplied contexts; type alignment is decidable syntax, not a state/run oracle.
The primitive/local one-update family remains incremental coverage, not a
production-domain exclusion. The partial producer route and full pass remain. -/
structure TypedPairV4 {S : Source.Ctx} {loop : Bool}
    {L : List (String × Source.STy)} {syn : Source.Syn (.stmt ⟨loop, true⟩)}
    {C : Contract} [FreshNames] (pre tail : List PrimTy) (context : NCtx)
    (input output : RawStmt) (derivation : Source.StmtD S L syn L)
    (program : Prog C context.ctx context.ctx) where
  sourceTypes : Source.tysOf L = Source.Agreement.sourceContext (pre ++ .uint :: tail)
  modelTypes : context.ctx = Source.Agreement.modelContext (pre ++ .uint :: tail)
  source : TypedSourceOneAssociation input derivation
  named : NamedOneAssociation context input output program
  paired : PairedUpdateV3 pre tail
    (sourceStatementV4 sourceTypes derivation.toR) (modelProgramV4 modelTypes program)
  name : source.raw.name = named.raw.source.name
  sourceDirection : source.raw.inc = named.raw.source.inc
  pairedDirection : paired.inc = named.raw.source.inc

/-- Total inspection of all four supplied syntax objects and both actual
typing contexts. No correctness equation for toR, elaboration or execution is
an argument. Other types, statements and producer stages remain obligations. -/
def checkTypedPairV4 {S : Source.Ctx} {loop : Bool}
    {L : List (String × Source.STy)} {syn : Source.Syn (.stmt ⟨loop, true⟩)}
    {C : Contract} [FreshNames] (pre tail : List PrimTy) (context : NCtx)
    (input output : RawStmt) (derivation : Source.StmtD S L syn L)
    (program : Prog C context.ctx context.ctx) :
    Option (TypedPairV4 pre tail context input output derivation program) := do
  if sourceTypes : Source.tysOf L = Source.Agreement.sourceContext (pre ++ .uint :: tail) then
    if modelTypes : context.ctx = Source.Agreement.modelContext (pre ++ .uint :: tail) then
      let source ← checkTypedSourceSpelling input derivation
      let named ← checkNamedOne context input output program
      let paired ← checkPairedUpdateV3 pre tail
        (sourceStatementV4 sourceTypes derivation.toR) (modelProgramV4 modelTypes program)
      if name : source.raw.name = named.raw.source.name then
        if sourceDirection : source.raw.inc = named.raw.source.inc then
          if pairedDirection : paired.inc = named.raw.source.inc then
            some ⟨sourceTypes, modelTypes, source, named, paired, name, sourceDirection, pairedDirection⟩
          else none
        else none
      else none
    else none
  else none

private theorem sourceRun_pullbackV4 {E : Source.Env} {R : List Source.STy}
    {M : Bool} {k : Source.SCtx} {Γ Δ : Source.RCtx}
    (alignment : Γ = Δ) (statement : Source.RStmt E R M k Γ Γ)
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat) (ph : Option (Source.Ph E))
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    {τ : Source.STy} (slot : Source.Idx Δ τ) (value : Source.Val E.layout τ)
    (run : (Source.execS G F horizon nps ph (sourceStatementV4 alignment statement)
      (sourceLocalsV4 alignment locals) (plan := plan) (calldataKnown := known)).run (.nil, state) =
      (.ok (.normal ((sourceLocalsV4 alignment locals).set slot value)), (.nil, state))) :
    (Source.execS G F horizon nps ph statement locals
      (plan := plan) (calldataKnown := known)).run (.nil, state) =
      (.ok (.normal (locals.set (alignment.symm ▸ slot) value)), (.nil, state)) := by
  cases alignment
  exact run

private theorem modelRun_pullbackV4 {C : Contract} {Γ Δ : Ctx}
    (alignment : Γ = Δ) (program : Prog C Γ Γ) (state : State C Γ)
    {p : PrimTy} (slot : Idx Δ (.val p)) (value : p.Denote)
    (run : (modelProgramV4 alignment program).run (modelStateV4 alignment state) =
      .ok (⟨(modelStateV4 alignment state).setLocal slot value, List.prefix_refl _⟩ :
        Out C (modelStateV4 alignment state).H Δ)) :
    program.run state = .ok (⟨state.setLocal (alignment.symm ▸ slot) value, List.prefix_refl _⟩ :
      Out C state.H Γ) := by
  cases alignment
  exact run

private theorem sourceLocals_setV4 {D : Source.Layout} {Γ Δ : Source.RCtx}
    (alignment : Γ = Δ) (locals : Source.Locals D Γ)
    {τ : Source.STy} (slot : Source.Idx Δ τ) (value : Source.Val D τ) :
    sourceLocalsV4 alignment (locals.set (alignment.symm ▸ slot) value) =
      (sourceLocalsV4 alignment locals).set slot value := by
  cases alignment
  rfl

private theorem modelState_setV4 {C : Contract} {Γ Δ : Ctx}
    (alignment : Γ = Δ) (state : State C Γ)
    {p : PrimTy} (slot : Idx Δ (.val p)) (value : p.Denote) :
    modelStateV4 alignment (state.setLocal (alignment.symm ▸ slot) value) =
      (modelStateV4 alignment state).setLocal slot value := by
  cases alignment
  rfl

/-- Actual supplied Source typing and model executions, in their original
contexts, follow from static validation and initial local correspondence.
Only type indices are transported in the initial/post-local relation. The
complete Source state and all model nonlocals are preserved. This does not
prove the remaining partial producer route, unchecked entry, resources,
concrete global encoding, all-arm completeness or PassCorrect. -/
theorem typedPairV4_run {S : Source.Ctx} {loop : Bool}
    {L : List (String × Source.STy)} {syn : Source.Syn (.stmt ⟨loop, true⟩)}
    {C : Contract} [FreshNames] (pre tail : List PrimTy) (context : NCtx)
    (input output : RawStmt) (derivation : Source.StmtD S L syn L)
    (program : Prog C context.ctx context.ctx)
    (certificate : TypedPairV4 pre tail context input output derivation program)
    (G : Source.Glob S.env) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph S.env))
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (locals : Source.Locals S.env.layout (Source.tysOf L)) (state : Source.St S.env)
    (model : State C context.ctx)
    (initial : Source.Agreement.LocalsRel S.env.layout C
      (modelStateV4 certificate.modelTypes model).H (pre ++ .uint :: tail)
      (sourceLocalsV4 certificate.sourceTypes locals)
      (modelStateV4 certificate.modelTypes model).env) :
    ∃ (sourceResult : Source.Val S.env.layout (.int Source.IntTy.u256))
      (modelResult : PrimTy.uint.Denote),
      (Source.execS G { F with checked := false } (fuel + 3) nps ph derivation.toR locals
        (plan := plan) (calldataKnown := known)).run (.nil, state) =
        (.ok (.normal (locals.set
          (certificate.sourceTypes.symm ▸ Source.Agreement.sourcePrimitiveSlot .uint tail pre)
          sourceResult)), (.nil, state)) ∧
      program.run model = .ok (⟨model.setLocal
        (certificate.modelTypes.symm ▸ Source.Agreement.modelPrimitiveSlot .uint tail pre)
        modelResult, List.prefix_refl _⟩ : Out C model.H context.ctx) ∧
      Source.Agreement.StateLocalsRel S.env C (pre ++ .uint :: tail)
        (sourceLocalsV4 certificate.sourceTypes (locals.set
          (certificate.sourceTypes.symm ▸ Source.Agreement.sourcePrimitiveSlot .uint tail pre)
          sourceResult))
        (modelStateV4 certificate.modelTypes (model.setLocal
          (certificate.modelTypes.symm ▸ Source.Agreement.modelPrimitiveSlot .uint tail pre)
          modelResult)) ∧
      (model.setLocal
        (certificate.modelTypes.symm ▸ Source.Agreement.modelPrimitiveSlot .uint tail pre)
        modelResult).glob = model.glob := by
  obtain ⟨sourceResult, modelResult, sourceRun, modelRun, post, globals⟩ :=
    pairedUpdateV3_run pre tail
      (sourceStatementV4 certificate.sourceTypes derivation.toR)
      (modelProgramV4 certificate.modelTypes program) certificate.paired
      G F fuel nps ph plan known (sourceLocalsV4 certificate.sourceTypes locals) state
      (modelStateV4 certificate.modelTypes model) initial
  refine ⟨sourceResult, modelResult,
    sourceRun_pullbackV4 certificate.sourceTypes derivation.toR G _ (fuel + 3)
      nps ph plan known locals state _ sourceResult sourceRun,
    modelRun_pullbackV4 certificate.modelTypes program model _ modelResult modelRun, ?_, rfl⟩
  rw [sourceLocals_setV4, modelState_setV4]
  exact post

#print axioms typedPairV4_run

#print axioms typedSourceSpelling_normalize

end Solidity.Correctness.Lowering.Unchecked
