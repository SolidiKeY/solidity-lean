import Solidity.Correctness.Lowering.Total.Relation

/-!
# Successful production runs for the candidate loop-lowering contract

Success is an equation for the real production computation, with its complete
reader, locals, fresh counter and memo. It is meaningful even while the
producer is opaque/partial: stating this equation does not unfold it, assert
termination, or depend on `loweringKernelTotal`. Quoting one external run does
not prove this equation universally.

No goal is bound here. The universal semantic contract and its raw/Source
coverage boundary are still to be supplied; successful runs below impose no
e1-family restriction. In particular, empty inputs and successful outputs
outside the e1 families are not silently excluded.
-/
namespace Solidity.Correctness.Lowering.Total

/-- All inputs to one production invocation, not a sampled initial state. -/
structure ProductionInput where
  names : FreshNames
  returnSlots : Option (List String)
  raw : List RawStmt
  scope : ElabScope
  before : Checker.Snapshot

/-- Complete successful result, retaining locals, counter and memo. -/
structure ProductionOutput where
  raw : List RawStmt
  after : Checker.Snapshot

/-- Successful execution of the actual `lowerLoops`, from arbitrary supplied
state. No reset to an empty memo or fixed fresh counter is permitted here. -/
def SuccessfulProductionRun (input : ProductionInput) (output : ProductionOutput) : Prop :=
  letI : FreshNames := input.names
  (((lowerLoops input.returnSlots input.raw).run input.scope).run input.before.locals).run
    input.before.memo = .ok ((output.raw, output.after.locals), output.after.memo)

/-- The successful-input domain includes exactly those inputs with a successful
production result. No semantic certificate or family membership is a premise. -/
def SuccessfulProductionInput (input : ProductionInput) : Prop :=
  ∃ output, SuccessfulProductionRun input output

/-- A subsequent intrinsic elaboration and placement, with complete states.
`raw` is explicit: normal loops elaborate the first pass output; return-family
bodies additionally run the callee-body/return pass. That pass must be linked
separately, never erased from the production trace. -/
def SuccessfulElaboration (names : FreshNames) (C : Contract) (Γ : Ctx)
    (scope : ElabScope) (before after : Checker.Snapshot) (raw : List RawStmt)
    (parts : SProg C) (placementNames : List Var) (program : Blk C Γ) : Prop :=
  letI : FreshNames := names
  ((((elabStmtsP C raw).run scope).run before.locals).run before.memo =
    .ok ((parts, after.locals), after.memo)) ∧
  SProg.chain placementNames Γ parts = .ok program

/-- The caller context decoded using this invocation's spelling policy. -/
def ProductionInput.caller (input : ProductionInput) : NCtx :=
  letI : FreshNames := input.names
  ECtx.toNCtx input.before.locals.1

/-- Normal pipeline provenance with mandatory phase continuity. The actual
lowering result is elaborated under the same reader and names, starting from
its returned state; placement uses the original caller context. This states
no raw/Source association or semantic preservation. -/
def SuccessfulLoopPipeline (input : ProductionInput) (output : ProductionOutput)
    (C : Contract) (afterElab : Checker.Snapshot) (parts : SProg C)
    (program : Blk C input.caller.ctx) : Prop :=
  SuccessfulProductionRun input output ∧
  SuccessfulElaboration input.names C input.caller.ctx input.scope output.after afterElab
    output.raw parts input.caller.names program

/-- Successful callee-body pass for return-family coverage. This is the real
pass, including renaming, loop lowering, return lowering, modifiers, frame
handling and block freshening. Its relation to an interior lowerLoops run and
the e1 return shapes is an outstanding coverage obligation. -/
def SuccessfulCalleeBodyRun (names : FreshNames) (C : Contract) (d : FunDecl)
    (calleeRenaming : List (String × String)) (ctor selfFrame : Bool) (calleeLocals : ECtx)
    (scope : ElabScope) (before : Checker.Snapshot) (output : ProductionOutput) : Prop :=
  letI : FreshNames := names
  (((calleeBody C d calleeRenaming ctor selfFrame calleeLocals).run scope).run before.locals).run
    before.memo = .ok ((output.raw, output.after.locals), output.after.memo)

end Solidity.Correctness.Lowering.Total
