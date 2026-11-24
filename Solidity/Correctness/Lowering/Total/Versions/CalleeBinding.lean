import Solidity.Correctness.Lowering.Total.Contract
import Solidity.Source.Elaborate

/-!
# Proposed callee binding obligations

Statement-only proposal for review. No producer or inhabitant of `Contract` is
supplied. In particular, the existing plain-request decoder cannot satisfy its
coverage field. This module neither changes admission nor claims that a body
binding proves semantic preservation.

`Output` retains the complete resolved declaration body, including modifiers.
`Declared` checks selection of the prospective declaration output, its frame
and its elaboration, independently of the lowered output. One fixed prospective
declaration producer reads the full original request, including its contract,
declaration, renaming and frame flags. Parameter/return value
agreement, modifier/initializer translation and the full state/outcome relation
remain additional semantic obligations, not consequences of `Declared`.
-/
namespace Solidity.Correctness.Lowering.Total.Version.CalleeBinding

/-- Prospective additive decoder output. No copy of a traversal or decoder.
The output carries a Source program, including its initializer/base-argument
tables. Correspondence with and complete retention of the model contract remain
obligations; the type alone does not establish them. -/
structure Output where
  source : Source.Elaborated
  declaration : Source.Decl
  frame : Source.Frame
  body : Source.RBody source.res.env

/-- Exact declared-body association proposed for review. The body comes from
Source elaboration of the selected declaration, including its complete modifier
list, rather than an arbitrary `RBody.Derived` witness or lowered raw output.
This is a structural relation; it does not establish type/value faithfulness of
model parameters, reference locations, widths or contract metadata. -/
def Declared (spellDeclaration : Request → Option Source.Decl)
    (r : Request) (c : CalleeRequest) (s : Output) : Prop :=
  r.callee = some c ∧ r.input.raw = c.declaration.body ∧
  s.declaration ∈ s.source.res.env.decls ∧
  s.declaration.frame? s.source.res.env = some s.frame ∧
  s.source.prog.body s.declaration = some s.body ∧
  (Source.elabBody s.source.res.env s.declaration).map Subtype.val = some s.body ∧
  s.frame.names = c.declaration.params.map (fun p => some p.1) ∧
  s.frame.rnames = c.declaration.rets.map (fun p => some p.1) ∧
  spellDeclaration r = some s.declaration

/-- Parameters of the actual callee-body producer. These are observations of
the existing request, not independently chosen decoder metadata. Return slots
come from the declaration and renaming, never `input.returnSlots`. -/
def returnSlots (c : CalleeRequest) : List String :=
  c.declaration.rets.map fun (n, _) => (Semantics.lookupBy n c.names).getD n

/-- The ordinary body endpoint retains both checker state layers. Its context,
scope and state are exactly the existing Request projections. Constructor and
self-frame flags, renaming, modifiers, initializers and block freshening are
retained by `Request.success` through `calleeBody`, not reimplemented here. -/
def Ordinary (r : Request) (o : ProductionOutput) (after : Checker.Snapshot)
    (parts : SProg r.contract) (p : Blk r.contract r.context.ctx) : Prop :=
  r.pipeline o after parts p

/-- A recursive frame is separate input from the actual call site.
Its depth, parameter/return variables and below-thunk must not be fabricated
from `CalleeRequest`, which does not carry them. This endpoint mirrors the
recursive frame elaboration: keep the recursive scope, add the supplied frame,
and start the memo empty. It does not assert that the supplied frame was
constructed by `elabCallRet`, nor that ordinary memo threading proves recursion.
The full successful elaboration retains the resulting memo as well. -/
def Recursive (r : Request) (c : CalleeRequest) (o : ProductionOutput)
    (rf : RecFrame) (after : Checker.Snapshot) (parts : SProg r.contract)
    (placementNames : List Var) (F : Ctx) (p : Blk r.contract F) : Prop :=
  r.callee = some c ∧ r.success o ∧
  SuccessfulElaboration r.input.names r.contract F
    { r.elabScope o with recs := rf :: r.input.scope.recs }
    { locals := (c.locals, o.after.locals.2), memo := {} }
    after o.raw parts placementNames p

/-- Proposed first-stage obligations for one fixed additive producer.
Coverage is required on every successful ordinary callee pipeline; a producer
returning `none` for all callees is not certified by conditional soundness.
The fixed declaration producer reads the complete original request,
including declaration, body and frame metadata, not `o.raw`. Its correctness is an outstanding
obligation: these equations do not certify an arbitrary translator as faithful.

This is NOT the semantic-faithfulness contract: no assertion here equates
`RBody.items` execution with the full modified body, drops initializers, or
identifies ordinary and recursive runs. The user review must decide whether
this structural checkpoint is the intended P2 binding layer before any proofs
are attempted. Recursive-site provenance and semantic preservation stay open. -/
structure Contract
    (spellDeclaration : Request → Option Source.Decl)
    (produce : Request → Option Output) : Prop where
  declared : ∀ r c s, r.callee = some c → produce r = some s → Declared spellDeclaration r c s
  coverage : ∀ r c o after parts p, r.callee = some c → Ordinary r o after parts p →
    ∃ s, produce r = some s
  recursiveCoverage : ∀ r c o rf after parts names F p,
    Recursive r c o rf after parts names F p → ∃ s, produce r = some s
  success : ∀ (r : Request) (c : CalleeRequest) (o : ProductionOutput), r.callee = some c →
    (r.success o ↔ r.input.raw = c.declaration.body ∧
      SuccessfulCalleeBodyRun r.input.names r.contract c.declaration c.names
        c.constructor c.selfFrame c.locals r.input.scope r.input.before o)
  context : ∀ (r : Request) (c : CalleeRequest), r.callee = some c →
    r.context = @ECtx.toNCtx r.input.names c.locals
  scope : ∀ (r : Request) (c : CalleeRequest) (o : ProductionOutput), r.callee = some c →
    r.elabScope o = { r.input.scope with
      funs := c.scope, top := false, selfFrame := c.selfFrame, unchecked := false,
      inlined := List.cons (c.start, o.after.locals.2) r.input.scope.inlined }
  state : ∀ (r : Request) (c : CalleeRequest) (o : ProductionOutput), r.callee = some c →
    r.elabState o = { o.after with locals := (c.locals, o.after.locals.2) }
  returns : ∀ c, returnSlots c =
    c.declaration.rets.map (fun (n, _) => (Semantics.lookupBy n c.names).getD n)

end Solidity.Correctness.Lowering.Total.Version.CalleeBinding
