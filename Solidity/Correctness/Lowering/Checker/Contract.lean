import Solidity.Syntax.Elab.Stmt
import Solidity.Lowering.G19.AssignmentWhileBreak

/-!
# P1 feasibility contract (not an implemented semantic checker)

This is an unfrozen candidate for the normal Boolean while/break leaf. The
function type below specifies the desired checker boundary; no implementation
or inhabitant of `SemanticSoundnessStatement` is supplied. In particular, this module
claims neither output acceptance nor source/model association.

## Inventory at d4ad633a9624263a59b14fd2c520b9bc602f88f3

Anchors below are in `Solidity/Syntax/Elab/Lower.lean`. G19 anchors name
`correct` in `Solidity/Lowering/G19/`. Each named theorem covers a fixed family,
not arbitrary uses of a constructor or combinations of those families.

| Rewrite | Anchor | Existing semantic ingredient / gap |
| --- | --- | --- |
| Empty list, ordinary cons, abrupt propagation | 419-426 | Generic composition missing |
| Drop suffix after a direct jump | 427 | Fixed return/break/continue families only |
| Guard nonempty suffix after possible abrupt compound | 429-431 | ConditionalSequence:108, ConditionalReturnContinuation:54, ReturnTail:140 |
| Outside-loop block/unchecked/checked/if/try recursion | 439-447 | AssignmentBlocks:113 Boolean blocks only; wrappers/try uncovered |
| Other statements pass through unchanged outside/inside loops | 450,479 | Not a general semantic identity/association theorem |
| Reject outside-loop break/continue | 448-449 | Producer refusal |
| Break/continue become flag assignment | 452-453 | Fixed while/do/for break/continue families |
| Return-slot writes and return flag; absent slots rejected | 454-459 | AssignmentReturnFlag:69, WhileReturn:43; arbitrary values uncovered |
| In-loop block/wrappers/if and abrupt union | 460-471 | Fixed block/conditional families; generic composition missing |
| Reject try jumps in loop; lower jump-free clauses outside | 472-478 | Producer refusal / generic try uncovered |
| Extract for/do/while/internal-loop components | 485-489 | Matching fixed loop families |
| Effectful while condition moves to synthetic head | 493-496 | AssignmentWhileBreak:74 and Continue:86; output bridge missing |
| Reset loop flags, share nested return flag | 497-501 | Generic nesting invariant missing |
| Do-first flag/disjunction | 507-512 | AssignmentDoWhileBreak:74, Continue:76, Return:94 |
| Continue reset and lowered body | 513-514 | AssignmentWhileContinue:86, AssignmentWhileReset:205 |
| Append update, guarding against break/return | 515-517 | AssignmentForBreak:64, Continue:186, Return:56 |
| Guard condition against break/return | 518 | Fixed loop families |
| Flag declarations, restore outer flags, invariant tautologies | 519-532 | Generic freshness/specification/context transport missing |
| Emit loop, prelude block and outer return test | 533-539 | Fixed return families; generic endpoint missing |
| Initialize empty loop flags and project raw result | 543-544 | No producer-success theorem |

Other fixed ingredients: ReturnPair:90, ConditionalStatement:94,
ConditionalReturn:63. Arithmetic/unchecked rewriting is a separate obligation.

## Critical bridge

`RawExpr.hasIncDec` includes assignment (Elab/Context.lean:369-375).
Consequently `while (i = a) { break; }` with empty specifications takes the
synthetic-head rewrite at Lower.lean:493-496. Its actual output includes a
break-flag declaration, a flag-guarded loop, a condition-assignment test and a
guarded suffix. Intrinsic elaboration retains the loop (Arms.lean:1927-1950).
G19 AssignmentWhileBreak.code:12-15 is a scoped assignment/capture prefix,
without a loop. Equality to that code is not a viable association proof.

A generic target normalization/simulation and context transport are needed
before reusing the G19 leaf. Raw blocks flatten during elaboration
(Arms.lean:1951, Stmt.lean:826-831); hidden binders can remain in `Blk`'s
existential output context (Context.lean:1420,1473-1478). Hence `Output` retains
that context and the exact intrinsic program rather than requiring equal
input/output contexts. `IntrinsicProbe.actual_context` confirms one retained
Boolean flag for the concrete sample, and `actual_has_loop` confirms the loop.
`WhileBreak.prototype_sound` now connects the concrete actual target's two
caller-local observations to Source execution through G19.correct, for both
Boolean RHS paths and arbitrary Source state/pipeline. It does not prove
checker-wide soundness, complete state agreement or association for other names.

## Acceptance and refusals

No semantic constructor or combination is currently accepted by a general
triple checker: `Checker` remains a function type. `RawProbe.checkRaw` is an
implemented total raw-only matcher, and `WhileBreak.prototype_sound` is a
semantic theorem for its one concrete materialized sample, not a theorem for
all raw outputs the matcher accepts. Its raw family is: a single empty-spec while with
name-assignment condition and immediate break, with no user suffix. The
raw matcher checks no types or resolved indices; only the concrete sample
is independently elaborated as Boolean. It does not validate surrounding
live bindings, full returned counter/memo, or arbitrary raw/intrinsic
association.
Beyond the concrete sample, this family still needs raw/resolved association,
full fresh allocation and memo/context checks, intrinsic-output validation,
and a generic target bridge. This distinction is not whole-family coverage
credit. The actual-producer sample passes raw acceptance, fresh-counter,
intrinsic-context and two semantic-path checks. Corrupted declaration,
counter, source RHS and unsupported continue are raw negative controls. Sequence, conditionals, blocks, nested loops,
continue, return, for, do, specifications, try, arithmetic and checkedness
remain separate coverage gaps until a total check and generic proof exist.

Certificates below contain data only. They must not gain fields asserting
preservation, equivalence, successful elaboration or the desired conclusion.
A recursive implementation must consume a finite certificate/input tree,
refuse unsupported constructors, and never invoke opaque partial lowering in
kernel reduction. The producer remains outside the trust boundary.

## Measurable success gate

Run actual `lowerLoops` and intrinsic elaboration at elaboration time; quote
both exact outputs with their complete states into closed terms. Prove
`check input output cert = true` in the kernel by `decide`/`rfl` on those terms;
reject a corrupted output. Prove the generic soundness statement, execute that
very intrinsic output in its conclusion, and reuse G19.correct through a
proved generic bridge, not a supplied equivalence premise. Test state, flag,
source-index, pipeline and context corruption separately. An external
producer run or `#guard` alone does not pass this gate. Preserve a denominator
of producer failures and checker refusals, not only accepted samples.

## Recommendation before E1

Continue P1: the concrete raw and intrinsic outputs are reachable and have a
kernel-checked semantic observation using existing G19.correct plus a generic
replay bridge. Neither unavoidable duplication of lowering nor an unreachable
endpoint has been demonstrated, so LOW-2 does not justify choosing P2.
Budget 120-240 hours for the bounded control/sequence/block checker and generic
soundness, with a review point after 24-48 hours on actual-output context
transport and unbounded-loop simulation. This remains an engineering estimate,
not measured completion evidence or permission to freeze E1. The full accepted
association/state contract and generic soundness theorem remain open.

This candidate specifies the terminating normal Boolean observation only.
The horizon offset is the existing G19 leaf's offset, not a fuel/gas equation,
termination theorem or whole-language Horizon interface. Source journal and
model globals remain distinct; no physical storage/hash/gas claim is made.
`G` carries the pipeline. Return/error/timeout observations need the later
compositional interface; this contract does not silently identify them.
-/
namespace Solidity.Correctness.Lowering.Checker

open Solidity.Lowering.V07

/-- Full mutable ElabM carrier. Scope is carried separately because it is read
rather than mutated. In particular, memo is not reset using `runFrom`. -/
structure Snapshot where
  locals : ECtx × Nat
  memo : CallMemo

/-- Raw/resolved association is a check obligation, not a proof field. -/
structure Input (E : Source.Env) (returns : List Source.STy) (modifier : Bool)
    (control : Source.SCtx) (srcΓ : Source.RCtx) where
  raw : List RawStmt
  resolved : Source.RStmt E returns modifier control srcΓ srcΓ
  returnSlots : Option (List String)
  scope : ElabScope
  before : Snapshot

/-- Exact supplied output, including the existential intrinsic output context.
`elaborated` is the intermediate elaboration result before placement by `chain`.
No equality or semantic proof is supplied as evidence. -/
structure Output (C : Contract) (Γ : Ctx) where
  raw : List RawStmt
  afterLower : Snapshot
  elabScope : ElabScope
  beforeElab : Snapshot
  afterElab : Snapshot
  elaborated : SProg C
  names : List Var
  program : Blk C Γ

/-- Finite first-leaf evidence. Names, counters and positions are proposals
for a checker to validate, never assumed freshness or association facts. -/
structure Certificate where
  destination : String
  rhs : String
  breakFlag : String
  counter : Nat
  destinationPosition : Nat
  rhsPosition : Nat
  deriving Repr, DecidableEq

/-- Required total checker signature. A future definition must recurse on
finite syntax/certificate data, checking the supplied output rather than
reimplementing the producer. This is a type, not an implemented checker. -/
abbrev Checker (E : Source.Env) (returns : List Source.STy) (modifier : Bool)
    (control : Source.SCtx) (srcΓ : Source.RCtx) (C : Contract) (Γ : Ctx) :=
  ContextMap srcΓ Γ → Input E returns modifier control srcΓ → Output C Γ → Certificate → Bool

/-- Producer provenance equation, recorded separately from semantic validity.
It is not a certificate field or a premise of `SemanticSoundnessStatement`.
Partial recursion must not be unfolded to prove concrete acceptance. -/
def ProducerReceipt [FreshNames]
    {E : Source.Env} {returns : List Source.STy} {modifier : Bool}
    {control : Source.SCtx} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (input : Input E returns modifier control srcΓ) (output : Output C Γ) : Prop :=
  (((lowerLoops input.returnSlots input.raw).run input.scope).run input.before.locals).run
    input.before.memo = .ok ((output.raw, output.afterLower.locals), output.afterLower.memo)

/-- Intrinsic-output provenance, retaining both state layers and actual
context placement. This is also a specification, not accepted proof evidence. -/
def ElaborationReceipt [FreshNames] {C : Contract} {Γ : Ctx}
    (output : Output C Γ) : Prop :=
  (((elabStmtsP C output.raw).run output.elabScope).run output.beforeElab.locals).run
    output.beforeElab.memo =
      .ok ((output.elaborated, output.afterElab.locals), output.afterElab.memo) ∧
  SProg.chain output.names Γ output.elaborated = .ok output.program

/-- Candidate soundness obligation for the first normal Boolean leaf.

The conclusion runs `output.program.2`, not independently selected G19 code.
An implementation must check source association against the supplied map
and compute/check context transport. The post-observation is the input map
weakened along `embedding`; a certificate cannot choose an unrelated map. An eventual checker
should compute that embedding; the candidate signature will need this finite
context evidence added after actual-output experiments.

This is only the semantic component. Accepted raw/resolved and intrinsic
association, snapshot consistency and phase threading remain obligations;
semantic validity alone does not constrain unused provenance fields.
No inhabitant is supplied here; this is a statement, not an admitted theorem.
It does not assume desired execution or target equivalence. G19's initial
value alignment and Boolean reflection remain initial semantic facts. The
map typing/slot facts needed by G19 must be derived by the association checker,
not supplied as desired preservation premises. -/
def SemanticSoundnessStatement {E : Source.Env} {returns : List Source.STy} {modifier : Bool}
    {control : Source.SCtx} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (check : Checker E returns modifier control srcΓ C Γ) : Prop :=
  ∀ (m : ContextMap srcΓ Γ)
    (input : Input E returns modifier control srcΓ) (output : Output C Γ)
    (cert : Certificate), check m input output cert = true →
  ∃ embedding : Thin Γ output.program.1,
  ∀ (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (R : (H : HTy) → (τ : Source.STy) → (u : LTy) →
      Source.Val E.layout τ → u.TDenote C H → Prop),
    m.Related (R target.H) source.1 target.env →
    (∀ (H : HTy) (v : Source.Val E.layout .bool) (b : Bool),
      R H .bool (.val .bool) v b → v = .bool b) →
    ∃ (ls : Source.Locals E.layout srcΓ) (out : Out C target.H output.program.1),
      (Source.execS G F (fuel + 3) nps ph input.resolved source.1).run (.nil, source.2) =
        (.ok (Source.Out.normal ls), (.nil, source.2)) ∧
      output.program.2.run target = .ok out ∧
      (m.wk embedding).Related (R out.st.H) ls out.st.env ∧
      out.st.glob = target.glob

/-- Necessary phase-threading checks for the first no-call leaf. These do
not prove that the opaque producer or elaborator ran. Actual executions are
materialized at elaboration time and checked as supplied data; their receipt
equations above remain provenance specifications, not assumed soundness.
Raw/resolved and raw/intrinsic association still need structural definitions. -/
def StateThreading {E : Source.Env} {returns : List Source.STy} {modifier : Bool}
    {control : Source.SCtx} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (input : Input E returns modifier control srcΓ) (output : Output C Γ) : Prop :=
  output.beforeElab.locals = output.afterLower.locals ∧
  output.beforeElab.memo = output.afterLower.memo ∧
  output.elabScope = input.scope ∧
  output.names = (ECtx.toNCtx output.beforeElab.locals.1).names ∧
  Γ = (ECtx.toNCtx output.beforeElab.locals.1).ctx ∧
  output.afterLower.locals.1 = input.before.locals.1 ∧
  output.afterLower.memo = input.before.memo ∧
  input.before.locals.2 ≤ output.afterLower.locals.2

/-- State consistency is a conclusion of accepted checking, never a supplied
proof field. This necessary component does not yet specify exact fresh-name
allocation or raw/intrinsic association; it is not a complete P1 contract. -/
def StateSoundnessStatement {E : Source.Env} {returns : List Source.STy} {modifier : Bool}
    {control : Source.SCtx} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (check : Checker E returns modifier control srcΓ C Γ) : Prop :=
  ∀ (m : ContextMap srcΓ Γ) (input : Input E returns modifier control srcΓ)
    (output : Output C Γ) (cert : Certificate),
    check m input output cert = true → StateThreading input output

/-- Combined unfrozen semantic/state candidate. This statement elaborates,
but no checker or proof inhabiting it is supplied. Exact raw/resolved and
raw/intrinsic association and full allocation validation are additional
obligations before this can serve as the complete P1 contract. -/
def SoundnessStatement {E : Source.Env} {returns : List Source.STy} {modifier : Bool}
    {control : Source.SCtx} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (check : Checker E returns modifier control srcΓ C Γ) : Prop :=
  SemanticSoundnessStatement check ∧ StateSoundnessStatement check

end Solidity.Correctness.Lowering.Checker
