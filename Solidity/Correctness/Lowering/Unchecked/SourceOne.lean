import Solidity.Correctness.Lowering.Unchecked.RawOne
import Solidity.Correctness.Lowering.Unchecked.Discarded

/-!
# Supplied typed Source one-update boundary

Guards associating a raw update with a differently typed or shadowed Source
local. Recognition reads the actual supplied resolved statement, including
its integer width, and the production Source name resolver. The typed wrapper
reads StmtD.toR itself; it accepts no equation about that elaboration.

This is a Source normalization boundary, not a Source/model state bridge.
Initial syntax-to-raw provenance, consistency of the supplied named contexts,
unchecked frame entry, the partial producer route and the prescribed canonical
endpoint remain obligations. Unrecognized shapes and structurally noncanonical
rational spellings of one are coverage gaps, not final source exclusions.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- Two actual resolved Source spellings, retaining their common integer type
and local position. Evidence is syntactic, never an execution equation. -/
inductive SourceOneShape {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {t : Source.IntTy}
    (inc : Bool) (slot : Source.Idx Γ (.int t)) : {Γ' : Source.RCtx} → Source.RStmt E R M k Γ Γ' → Type where
  | increment (pre : Bool) : SourceOneShape inc slot (.expr (.incDec inc pre (.local slot)))
  | compound (fits : (if inc then Source.AssignOp.add else .sub).fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
      SourceOneShape inc slot (.expr (.compound (if inc then .add else .sub)
        (.local slot) (.const (Source.Q.ofInt 1)) fits))

/-- The actual Source width is retained instead of recovered from the model's
width-erasing NCtx. The raw name must resolve to this exact Source position. -/
structure SourceOneAssociation {input : RawStmt} (context : Source.Ctx)
    (raw : RawOneInput input) {k : Source.SCtx} {Γ' : Source.RCtx}
    (statement : Source.RStmt context.env context.rets context.inModifier k context.tys Γ') where
  type : Source.IntTy
  slot : Source.Idx context.tys (.int type)
  shape : SourceOneShape raw.inc slot statement
  binding : context.resolve raw.name = some (.loc slot.toNat)

private def sourceOneAt {input : RawStmt} (context : Source.Ctx) (raw : RawOneInput input)
    {k : Source.SCtx} {Γ' : Source.RCtx}
    (statement : Source.RStmt context.env context.rets context.inModifier k context.tys Γ')
    (t : Source.IntTy) (slot : Source.Idx context.tys (.int t))
    (shape : SourceOneShape raw.inc slot statement) : Option (SourceOneAssociation context raw statement) :=
  match resolution : context.resolve raw.name with
  | some (.loc n) =>
    if index : n = slot.toNat then
      some ⟨t, slot, shape, by rw [resolution, index]⟩
    else none
  | _ => none

private def checkSourceOneExpression {input : RawStmt} (context : Source.Ctx)
    (raw : RawOneInput input) {k : Source.SCtx} {τ : Source.STy}
    (expression : Source.RExpr context.env context.tys τ) :
    Option (SourceOneAssociation context raw (Source.RStmt.expr (k := k) expression)) :=
  match expression with
  | .incDec inc pre l =>
    match l with
    | .local slot =>
      match τ with
      | .int t =>
        if direction : inc = raw.inc then
          sourceOneAt context raw _ t slot (by cases direction; exact .increment pre)
        else none
      | _ => none
    | _ => none
  | .compound (σ := σ) op l rhs fits =>
    match l with
    | .local slot =>
      match τ with
      | .int t =>
        match σ, rhs with
        | _, .const q =>
          if literal : q = Source.Q.ofInt 1 then
            if operation : op = (if raw.inc then Source.AssignOp.add else .sub) then
              sourceOneAt context raw _ t slot (by cases literal; cases operation; exact .compound fits)
            else none
          else none
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Total structural recognition of this resolved integer/local family.
Both operator direction and the exact Source binding are inspected. -/
def checkSourceOne {input : RawStmt} (context : Source.Ctx) (raw : RawOneInput input)
    {k : Source.SCtx} {Γ' : Source.RCtx} :
    (statement : Source.RStmt context.env context.rets context.inModifier k context.tys Γ') →
      Option (SourceOneAssociation context raw statement)
  | .expr expression => checkSourceOneExpression context raw expression
  | _ => none

/-- Read the actual production resolved result of a supplied typing derivation;
no assumed correctness or equality for Typed.toR/StmtD.toR is accepted. -/
def checkTypedSourceOne {input : RawStmt} {C : Source.Ctx} {k : Source.SCtx}
    {L L' : List (String × Source.STy)} {syn : Source.Syn (.stmt k)}
    (raw : RawOneInput input) (derivation : Source.StmtD C L syn L') :
    Option (SourceOneAssociation (C.at L) raw derivation.toR) :=
  checkSourceOne (C.at L) raw derivation.toR

/-- One accepted-shape Source law, lifted from the existing shared update
lemmas. All checkedness modes, horizons, failures and poststates remain;
there is no success or no-panic premise. This does not compare model states. -/
theorem sourceOne_normalize {input : RawStmt} (context : Source.Ctx) (raw : RawOneInput input)
    {k : Source.SCtx}
    (statement : Source.RStmt context.env context.rets context.inModifier k context.tys context.tys)
    (certificate : SourceOneAssociation context raw statement)
    (G : Source.Glob context.env) (F : Source.Fr) (horizon nps : Nat)
    (ph : Option (Source.Ph context.env)) (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (ls : Source.Locals context.env.layout context.tys) (st : Source.St context.env) :
    (Source.execS G F horizon nps ph statement ls (plan := plan) (calldataKnown := known)).run (.nil, st) =
    (Source.execS G F horizon nps ph
      (.expr (.incDec raw.inc true (.local certificate.slot))
        : Source.RStmt context.env context.rets context.inModifier k context.tys context.tys)
      ls (plan := plan) (calldataKnown := known)).run (.nil, st) := by
  cases certificate with
  | mk t slot shape binding =>
    cases shape with
    | increment pre =>
      exact incDec_statement G F horizon nps ph plan known ls st raw.inc pre (.local slot)
    | compound fits =>
      exact compoundOne_statement G F horizon nps ph plan known ls st t raw.inc true (.local slot) fits

#print axioms sourceOne_normalize

end Solidity.Correctness.Lowering.Unchecked
