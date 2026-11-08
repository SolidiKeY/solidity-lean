import Solidity.Correctness.Lowering.Unchecked.SourceOne

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

#print axioms typedSourceSpelling_normalize

end Solidity.Correctness.Lowering.Unchecked
