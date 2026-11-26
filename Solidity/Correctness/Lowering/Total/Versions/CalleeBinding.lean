import Solidity.Correctness.Lowering.Total.Contract
import Solidity.Source.Elaborate
import Solidity.Correctness.Lowering.Total.Decode.WithExpr

/-!
# Structural callee binding obligations

No producer or inhabitant of `Contract` is supplied. The existing plain-request
decoder cannot satisfy its coverage field. This module neither changes admission nor claims that a body
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

/-- Additive decoder output carrying the selected declaration and resolved body.
The output carries a Source program, including its initializer/base-argument
tables. Correspondence with and complete retention of the model contract remain
obligations; the type alone does not establish them. -/
structure Output where
  source : Source.Elaborated
  declaration : Source.Decl
  frame : Source.Frame
  body : Source.RBody source.res.env

/-- Exact declared-body association. The body comes from
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

/-- Structural obligations for one fixed additive producer.
Coverage is required on every successful ordinary callee pipeline; a producer
returning `none` for all callees is not certified by conditional soundness.
The fixed declaration producer reads the complete original request,
including declaration, body and frame metadata, not `o.raw`. Its correctness is an outstanding
obligation: these equations do not certify an arbitrary translator as faithful.

This is NOT the semantic-faithfulness contract: no assertion here equates
`RBody.items` execution with the full modified body, drops initializers, or
identifies ordinary and recursive runs. Recursive-site provenance and semantic
preservation remain additional obligations. -/
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

/-! ## Request-level binding of the e2b callee output (P2, statement level)

Additive; nothing above changes. `Site` collects the inputs of the e2b callee
producer (`fromFunctions` in `CalleeBinding/Functions.lean`, which imports this
module, so its instance is stated downstream). `Bound` is the proposed relation
between a callee request and one producer output: the request's callee, an
ordinary (non-constructor) entry at the site index, the additive spelling of
the declared body as the bound frame body, the Source-resolved body and the
frame's parameter and return names. `Renaming` is the call site's exact frame
renaming, a request-side premise, not a decoder fact. Ordinary threading
(`Request.elabScope`, `Request.elabState`) and the recursive endpoint
(`Recursive`: pushed recursive frame, empty memo) are told apart by the bridges
below. Statements still to prove are `Prop` definitions, not theorems; no
semantic preservation or coverage is claimed.
-/

/-- Inputs of the e2b callee producer at one call site. -/
structure Site where
  tables : Decode.Tables
  registry : CallSpellExt.Registry
  settings : Source.Settings
  scope : String
  leadingParts : Source.Syn (.list (.part false))
  index : Nat

/-- Renamed parameter slots in declaration order, as `returnSlots`. -/
def paramSlots (c : CalleeRequest) : List String :=
  c.declaration.params.map fun (n, _) => (Semantics.lookupBy n c.names).getD n

/-- Exact frame renaming of `elabCallRetCore`: `ρ` lists the returns, then the
parameters, each newest first; the frame `Γf = Γr ++ Γp` binds the renamed
names in the same order; renamed names are distinct. -/
def Renaming (c : CalleeRequest) : Prop :=
  c.names.map Prod.fst = ((c.declaration.params ++ c.declaration.rets).map Prod.fst).reverse ∧
  c.names.map Prod.snd = c.locals.map Prod.fst ∧ (c.names.map Prod.snd).Nodup

/-- **Proposed request-level binding** of one producer output `s` at site `σ`.
The frame body is the additive (registered-call) spelling of the declared
model body; the resolved body is Source elaboration of the selected
declaration, modifiers included. -/
structure Bound (σ : Site) (r : Request) (c : CalleeRequest) (s : Output) : Prop where
  callee : r.callee = some c
  ordinaryEntry : c.constructor = false
  entry : ∃ a, r.contract.funs[σ.index]? = some (a, c.declaration)
  spelledBody : Decode.Tables.WithExpr.items σ.tables (Decode.Calls.expr σ.tables σ.registry)
    .body c.declaration.body = some s.frame.body
  member : s.declaration ∈ s.source.res.env.decls
  frame : s.declaration.frame? s.source.res.env = some s.frame
  programBody : s.source.prog.body s.declaration = some s.body
  resolvedBody : (Source.elabBody s.source.res.env s.declaration).map Subtype.val = some s.body
  paramNames : s.frame.names = c.declaration.params.map (fun p => some p.1)
  returnNames : s.frame.rnames = c.declaration.rets.map (fun p => some p.1)

/-- Statement to prove: a producer's output at a selected ordinary entry is
`Bound`. Its instance is the e2b producer
`fun σ r => fromFunctions σ.tables σ.registry σ.settings σ.scope σ.leadingParts
r.contract.funs σ.index`. -/
def Publishes (produce : Site → Request → Option Output) : Prop :=
  ∀ σ r c s, r.callee = some c → c.constructor = false →
    (∃ a, r.contract.funs[σ.index]? = some (a, c.declaration)) →
    produce σ r = some s → Bound σ r c s

/-- Statement to prove: under the exact renaming with distinct original names,
parameter and return slots are the frame's locals, oldest first. -/
def slotsStatement : Prop :=
  ∀ c, Renaming c → ((c.declaration.params ++ c.declaration.rets).map Prod.fst).Nodup →
    paramSlots c ++ returnSlots c = (c.locals.map Prod.fst).reverse

/-! ### Ordinary callee endpoint: trivial bridges -/

section
variable {r : Request} {c : CalleeRequest} {o : ProductionOutput}

theorem success_callee (h : r.callee = some c) :
    r.success o ↔ r.input.raw = c.declaration.body ∧
      SuccessfulCalleeBodyRun r.input.names r.contract c.declaration c.names
        c.constructor c.selfFrame c.locals r.input.scope r.input.before o := by
  simp only [Request.success, h]

theorem context_callee (h : r.callee = some c) :
    r.context = @ECtx.toNCtx r.input.names c.locals := by
  simp only [Request.context, h, Option.map_some, Option.getD_some]

theorem elabScope_callee (h : r.callee = some c) :
    r.elabScope o = { r.input.scope with
      funs := c.scope, top := false, selfFrame := c.selfFrame, unchecked := false,
      inlined := List.cons (c.start, o.after.locals.2) r.input.scope.inlined } := by
  simp only [Request.elabScope, h]

theorem elabState_callee (h : r.callee = some c) :
    r.elabState o = { o.after with locals := (c.locals, o.after.locals.2) } := by
  simp only [Request.elabState, h, Option.map_some, Option.getD_some]

/-- Ordinary threading keeps the caller's recursive frames. -/
theorem elabScope_recs (h : r.callee = some c) : (r.elabScope o).recs = r.input.scope.recs := by
  rw [elabScope_callee h]

/-- Ordinary threading keeps the producer's memo. -/
theorem elabState_memo : (r.elabState o).memo = o.after.memo := rfl

/-- The bound frame body is the spelling of the request's raw input. -/
theorem Bound.spelledInput {σ : Site} {s : Output} (b : Bound σ r c s) (hs : r.success o) :
    Decode.Tables.WithExpr.items σ.tables (Decode.Calls.expr σ.tables σ.registry) .body
      r.input.raw = some s.frame.body := by
  rw [((success_callee b.callee).mp hs).1]
  exact b.spelledBody

/-- `Bound` with a successful run gives the earlier `Declared` interface at the
producer's own declaration. -/
theorem Bound.declared {σ : Site} {s : Output} (b : Bound σ r c s) (hs : r.success o) :
    Declared (fun _ => some s.declaration) r c s :=
  ⟨b.callee, ((success_callee b.callee).mp hs).1, b.member, b.frame, b.programBody,
    b.resolvedBody, b.paramNames, b.returnNames, rfl⟩

end

/-! ### Recursive endpoint: separate scope and empty memo -/

/-- The recursive elaboration scope: the ordinary one with the supplied frame
pushed on the caller's recursive frames. -/
def recursiveScope (r : Request) (o : ProductionOutput) (rf : RecFrame) : ElabScope :=
  { r.elabScope o with recs := rf :: r.input.scope.recs }

/-- The recursive elaboration state: the callee frame and an empty memo. -/
def recursiveState (c : CalleeRequest) (o : ProductionOutput) : Checker.Snapshot :=
  { locals := (c.locals, o.after.locals.2), memo := {} }

section
variable {r : Request} {c : CalleeRequest} {o : ProductionOutput} {rf : RecFrame}

theorem recursive_iff {after : Checker.Snapshot} {parts : SProg r.contract}
    {names : List Var} {F : Ctx} {p : Blk r.contract F} :
    Recursive r c o rf after parts names F p ↔ r.callee = some c ∧ r.success o ∧
      SuccessfulElaboration r.input.names r.contract F (recursiveScope r o rf)
        (recursiveState c o) after o.raw parts names p := Iff.rfl

/-- The recursive scope differs from ordinary threading exactly in `recs`. -/
theorem recursiveScope_eq (h : r.callee = some c) :
    recursiveScope r o rf = { r.elabScope o with recs := rf :: (r.elabScope o).recs } := by
  rw [elabScope_recs h]; rfl

theorem recursiveScope_ne (h : r.callee = some c) : recursiveScope r o rf ≠ r.elabScope o :=
  fun he => List.cons_ne_self rf r.input.scope.recs
    ((congrArg ElabScope.recs he).trans (elabScope_recs h))

theorem recursiveState_memo : (recursiveState c o).memo = {} := rfl

/-- Both endpoints bind the same callee frame locals. -/
theorem recursiveState_locals (h : r.callee = some c) :
    (recursiveState c o).locals = (r.elabState o).locals := by
  rw [elabState_callee h]; rfl

end

end Solidity.Correctness.Lowering.Total.Version.CalleeBinding
