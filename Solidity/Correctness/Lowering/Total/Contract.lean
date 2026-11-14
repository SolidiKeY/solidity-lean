import Solidity.Correctness.Lowering.Total.Relation
import Solidity.Roadmap.G49Final.PassCorrect

/-! H810 universal contract interface. Production equations retain complete
states and need no totalization premise. The candidate is relative to a fixed,
reviewed semantic boundary; E2B must freeze concrete parameters before binding
the legacy goal. No candidate inhabitant or general decoder is supplied. -/
namespace Solidity.Correctness.Lowering.Total

structure ProductionInput where
  names : FreshNames
  returnSlots : Option (List String)
  raw : List RawStmt
  scope : ElabScope
  before : Checker.Snapshot

structure ProductionOutput where
  raw : List RawStmt
  after : Checker.Snapshot

def SuccessfulProductionRun (input : ProductionInput) (output : ProductionOutput) : Prop :=
  letI : FreshNames := input.names
  (((lowerLoops input.returnSlots input.raw).run input.scope).run input.before.locals).run
    input.before.memo = .ok ((output.raw, output.after.locals), output.after.memo)

def SuccessfulProductionInput (input : ProductionInput) : Prop :=
  ∃ output, SuccessfulProductionRun input output
/-- Exact intrinsic elaboration and placement, retaining both state layers. -/
def SuccessfulElaboration (names : FreshNames) (C : Contract) (Γ : Ctx)
    (scope : ElabScope) (before after : Checker.Snapshot) (raw : List RawStmt)
    (parts : SProg C) (placementNames : List Var) (program : Blk C Γ) : Prop :=
  letI : FreshNames := names
  ((((elabStmtsP C raw).run scope).run before.locals).run before.memo =
    .ok ((parts, after.locals), after.memo)) ∧
  SProg.chain placementNames Γ parts = .ok program

def ProductionInput.caller (input : ProductionInput) : NCtx :=
  letI : FreshNames := input.names
  ECtx.toNCtx input.before.locals.1
/-- Normal phase continuity; this alone establishes no semantic preservation. -/
def SuccessfulLoopPipeline (input : ProductionInput) (output : ProductionOutput)
    (C : Contract) (afterElab : Checker.Snapshot) (parts : SProg C)
    (program : Blk C input.caller.ctx) : Prop :=
  SuccessfulProductionRun input output ∧
  SuccessfulElaboration input.names C input.caller.ctx input.scope output.after afterElab
    output.raw parts input.caller.names program
/-- The full callee-body pass: renaming, loops, returns, modifiers, frame and
block freshening. Interior-run/return-family coverage remains unproved. -/
def SuccessfulCalleeBodyRun (names : FreshNames) (C : Contract) (d : FunDecl)
    (calleeRenaming : List (String × String)) (ctor selfFrame : Bool) (calleeLocals : ECtx)
    (scope : ElabScope) (before : Checker.Snapshot) (output : ProductionOutput) : Prop :=
  letI : FreshNames := names
  (((calleeBody C d calleeRenaming ctor selfFrame calleeLocals).run scope).run before.locals).run
    before.memo = .ok ((output.raw, output.after.locals), output.after.memo)
/-- The raw producer obligation has NO semantic admission or family premise. -/
def UniversalProducerCorrect : Prop :=
  ∀ input output, SuccessfulProductionRun input output →
    @LowersTo input.names input.returnSlots input.raw output.raw input.scope input.before output.after

structure CalleeRequest where
  declaration : FunDecl
  names : List (String × String)
  constructor : Bool
  selfFrame : Bool
  locals : ECtx
  scope : List (Name × FunDecl)
  start : Nat

structure Request where
  contract : Contract
  input : ProductionInput
  callee : Option CalleeRequest := none

def Request.success (r : Request) (o : ProductionOutput) : Prop :=
  match r.callee with
  | none => SuccessfulProductionRun r.input o
  | some c => r.input.raw = c.declaration.body ∧
    SuccessfulCalleeBodyRun r.input.names r.contract c.declaration c.names c.constructor
      c.selfFrame c.locals r.input.scope r.input.before o
/-- The body endpoint of inlinedBody, excluding call binding and memo sharing. -/
def Request.context (r : Request) : NCtx :=
  letI : FreshNames := r.input.names
  ECtx.toNCtx (r.callee.map (·.locals) |>.getD r.input.before.locals.1)
def Request.elabScope (r : Request) (o : ProductionOutput) : ElabScope :=
  match r.callee with
  | none => r.input.scope
  | some c =>
    { r.input.scope with funs := c.scope, top := false, selfFrame := c.selfFrame,
                         unchecked := false, inlined := List.cons (c.start, o.after.locals.2) r.input.scope.inlined }
def Request.elabState (r : Request) (o : ProductionOutput) : Checker.Snapshot :=
  { o.after with locals := (r.callee.map (·.locals) |>.getD o.after.locals.1, o.after.locals.2) }
def Request.pipeline (r : Request) (o : ProductionOutput) (after : Checker.Snapshot)
    (parts : SProg r.contract) (p : Blk r.contract r.context.ctx) : Prop :=
  r.success o ∧ SuccessfulElaboration r.input.names r.contract r.context.ctx
    (r.elabScope o) (r.elabState o) after o.raw parts r.context.names p

/-- Allocation checks are scoped: callee-local rebinding and memo reuse must
not be confused with capture of a caller binding. The reference trace must
include ALL loop, callee and intrinsic allocations with their actual protected
names, including raw/specification binders, roots and earlier generated names
when simultaneously live; duplicate IDs alone do not establish freshness. -/
structure AllocationScope where
  protectedNames : List String
  generated : List (String × Nat)

structure SourceProgram where
  env : Source.Env
  returns : List Source.STy
  modifier : Bool
  control : Source.SCtx
  before : Source.RCtx
  after : Source.RCtx
  items : Source.RItems env returns modifier control before after

def SourceProgram.ofStmt {E R M k Γ Δ} (s : Source.RStmt E R M k Γ Δ) : SourceProgram :=
  ⟨E, R, M, k, Γ, Δ, .stmt s .nil⟩

structure SourceExecution (s : SourceProgram) where
  glob : Source.Glob s.env
  frame : Source.Fr
  nps : Nat
  placeholder : Option (Source.Ph s.env)
  initial : Source.EMState s.env s.before
  plan : Source.FailureExecution.RuntimePlan
  calldataKnown : Bool

abbrev SourceResult (s : SourceProgram) :=
  Source.R (Source.Out s.env.layout s.before s.after) × (Source.Locals s.env.layout [] × Source.St s.env)

def SourceExecution.result {s : SourceProgram} (e : SourceExecution s) (n : Nat) : SourceResult s :=
  (Source.execItems e.glob e.frame n e.nps e.placeholder s.items e.initial.1
    (plan := e.plan) (calldataKnown := e.calldataKnown)).run (.nil, e.initial.2)

open Solidity.Roadmap Solidity.Roadmap.G49Final
/-- A named observation/resource policy over the ACTUAL result family.
Source results retain all exit tags, halt data, journal and state. Timeout is
an approximation, not termination: the policy must interpret the whole horizon
family, preserving completion/divergence. Target results retain every THalt.
These policies require review: their type alone does not establish faithfulness
to a source/world, physical gas, assembled bytes or external EVM observation. -/
structure ObservationPolicy {Env : Type} {Result : Env → Type}
    (execute : (e : Env) → Nat → Result e) where
  allowed : Env → Prop
  admissible : Nat → Prop
  forward : Env → Nat → Prop
  guard : Env → Nat → Prop
  observe : (e : Env) → Nat → ((n : Nat) → Result e) → Prefix Event Outcome
  consistent : ∀ e, Prefixes.Consistent (fun n => observe e n (execute e))

def ObservationPolicy.behaviour {Env : Type} {Result : Env → Type}
    {execute : (e : Env) → Nat → Result e} (p : ObservationPolicy execute) : Behaviour :=
  ⟨Env, Nat, inferInstance, p.allowed, p.admissible, p.forward, p.guard,
    fun e n => p.observe e n (execute e), p.consistent⟩

/-- Proposed interpretation/observation adapters. Their admission and policies
must match the independently reviewed boundary below, never a chosen subset. -/
structure RawSourceInterpretation where
  associated : Request → SourceProgram → Prop
  entry : Request → Prop
  source : (s : SourceProgram) → ObservationPolicy (fun e n => @SourceExecution.result s e n)
  target : {C : Contract} → {Γ : Ctx} → (p : Blk C Γ) →
    ObservationPolicy (fun (e : State C Γ) (_ : Nat) => p.2.run e)

/-- Independently fixed specification parameters, not existential witnesses.
`reference` must state the preserved accepted fragment and faithful observable
outcomes/resources; `relates` is its FULL Source/model state/outcome relation,
not merely equal erased event prefixes. `allocations` specifies the COMPLETE
scoped allocation trace, not a caller-selected subset. Defining these
parameters and validating their faithfulness is open binding work: this record
is not proof or implementation acceptance. No concrete instance is supplied. -/
structure SemanticBoundary where
  reference : RawSourceInterpretation
  relates : SourceProgram → {C : Contract} → {Γ : Ctx} → Blk C Γ → Prop
  allocations : (r : Request) → ProductionOutput → Checker.Snapshot → SProg r.contract →
    Blk r.contract r.context.ctx → List AllocationScope → Prop

/-- The full reference relation specializes to the unchanged normal endpoint.
This equivalence alone is NOT observation-policy faithfulness. -/
def NormalCompatibility (b : SemanticBoundary) : Prop :=
  ∀ k {E srcΓ returns M l u C Γ} (m : Lowering.V07.ContextMap srcΓ Γ) (pair : Loops.Pair m)
    (extra : Loops.Shape.Extra E returns M u srcΓ C Γ k) names,
    b.relates (SourceProgram.ofStmt (Loops.Shape.source (l := l) k pair extra))
      (k.lowered pair extra names) ↔
    ∃ embedding, Loops.Endpoint (Loops.Shape.source (l := l) k pair extra) k.offset m
      (k.lowered pair extra names).2 embedding

/-- Return is the full callee-body endpoint, with the actual witness and
embedding. No replacement by the normal-outcome endpoint or by sample checks. -/
def ReturnCompatibility (b : SemanticBoundary) : Prop :=
  ∀ k {E srcΓ M l u C Γ} (m : Lowering.V07.ContextMap srcΓ Γ) (pair : Loops.Pair m)
    (extra : Loops.RetShape.Extra E srcΓ C Γ k) names,
    b.relates (SourceProgram.ofStmt (Loops.RetShape.source (M := M) (l := l) (u := u) k pair extra))
      ⟨_, k.program pair extra names⟩ ↔
    Loops.RetEndpoint (k.source (M := M) (l := l) (u := u) pair extra) k.offset m
      (k.program pair extra names) (k.embedding Γ) (k.witness Γ)

/-- Coverage is a conclusion to prove, not a certificate supplied to a theorem.
None of these universal obligations has been proved by the sample captures.
Both PassCorrect.need_ok and PassCorrect.back, environment soundness/onto and
all resource/guard fields survive unchanged. No termination assumption is used. -/
structure CoverageObligations (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) : Prop where
  admitted : ∀ r, i.entry r ↔ b.reference.entry r
  association : ∀ r s, i.associated r s ↔ b.reference.associated r s
  sourceFaithful : ∀ s, (i.source s).behaviour = (b.reference.source s).behaviour
  targetFaithful : ∀ {C Γ} (p : Blk C Γ), (i.target p).behaviour = (b.reference.target p).behaviour
  allocation : ∀ r o after parts program, i.entry r → r.pipeline o after parts program →
    ∃ scopes, b.allocations r o after parts program scopes ∧
      ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated
  source : ∀ r, i.entry r → ∃ s, i.associated r s
  decoder : ∀ r s, i.entry r → (decode r = some s ↔ i.associated r s)
  pipeline : ∀ r o after parts program s, i.entry r → decode r = some s →
    r.pipeline o after parts program →
    b.relates s program ∧ Nonempty (PassCorrect (i.source s).behaviour (i.target program).behaviour)
  normal : NormalCompatibility b
  returns : ReturnCompatibility b

/-- Exact relative candidate for E2B: universal producer correctness AND all
coverage duties AND unchanged e1 semantics. Never close it with an existential
boundary/interpretation: empty admissions or erasures are not acceptance.
Concrete reference semantics and its faithfulness review remain binding work. -/
def LowerLoopsCorrectContract (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) : Prop :=
  UniversalProducerCorrect ∧ CoverageObligations b i decode ∧ Loops.LoopFamilyCorrect

end Solidity.Correctness.Lowering.Total
