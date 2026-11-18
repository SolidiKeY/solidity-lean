import Solidity.Correctness.Lowering.Sim.Match
import Solidity.Goals.ElabTotal

/-!
# The lowering diagram: the open-recursion case interface

`Diagram.Simulates` quantifies over the outputs of the actual elaborator
(`ElaborationReceipt`: `elabStmtsP`, then `SProg.chain`), whose knot is
`partial`. Its arms are total definitions over a callback record
(`Syntax/Elab/Arms.lean`), so the cases of the simulation are stated here over
those arms at an arbitrary record, and the knot is closed afterwards by the
induction `Solidity.Goals.ElabKernelInduction` (a clause of
`Solidity.Goals.elabKernelTotal`).

* `RunSim b u m`: the per-run obligations of `Diagram.Simulates` for
  `Sim.diagram`: `LowerFresh`, total initial matching, and for one context
  extension the forward final matching at the transported fuel
  (`Diagram.Final`), stability of completed Source runs under larger horizons
  and the backward clause. `simulates_of_runs` checks that it is that part.
* `SiteSim C raw sc st P st'`: `RunSim` for every body and every emitted
  program whose elaboration is the run `raw, sc, st ↦ P, st'` placed by
  `SProg.chain`, lowered and threaded at the body's site (`Lowered`,
  `Threaded`), in the fragment (`Accepted`) and associated (`diagram.Assoc`).
* `RecSim C rc`: every successful run of `rc.hoist`, `rc.hoistStmt`,
  `rc.elabStmtP`, `rc.elabStmt1` and `rc.elabStmtsP` meets `SiteSim` at its
  site (`hoistQ`, `hoistStmtQ`, `stmtQ`, `blockQ`): the five predicates of
  `ElabKernelInduction`, instantiated (`recSim_of_step`).
* `ExprCases`, `StmtCases`, `StateCases`: for every record with `RecSim`, the
  successful outputs of the arms meet the same obligations, one conjunct per
  family (`StmtFamily`, `ExprFamily`: the statement constructors of
  `PublicCompilerTotal.StmtOk`, read on the raw input). Each takes
  `elabKernelTotal` as a hypothesis, for the defining equations of the
  `partial` helpers its arms call.

Loops are not a case: nothing here mentions `lowerLoops`. The three
propositions and a loop hypothesis (`StmtArm C r .loop` for every record with
`RecSim`; ls3a-sim-induction owns it) give the per-run part of
`diagram.Simulates` by `ElabKernelInduction` at `elabRec C ()`
(`runs_of_cases`). `Lowered` (the flag-based lowering) is a premise of
`SiteSim`, `LowerFresh` a conclusion of `RunSim`, and the forward clause is at
`diagram.fuel`.

## Limitations

* `ElabKernelInduction` constrains five fields of the record. An arm that
  calls another field (`elabBranch`, `elabCall`, `hoistTop`, …) at an arbitrary
  record has no hypothesis on that call's output, so its case needs the field's
  equation over the record, which `elabKernelTotal` does not state.
* `ElabKernelHelpers` states the equations of `RawExpr.mapM`, `lowerReturns`
  and `renameStmts` only.
* `SiteSim` is the whole-body obligation: a callback's run is read as the
  elaboration of a whole lowered body. It is not an invariant of a statement
  inside a body (a declaration changes the context, and `Body` has one).
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan ElabSat ElabKernelInduction ElabKernelNames elabStmtsStep
  elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Checker (Output ElaborationReceipt)

variable [FreshNames]

/-! ## The per-run obligations -/

/-- **The per-run obligations** of `Diagram.Simulates`, for `Sim.diagram`. -/
def RunSim (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) : Prop :=
  LowerFresh b u ∧
  (∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
    m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env ∧ diagram.globRel src.2 tgt) ∧
  ∃ emb : Thin u.Γ u.output.program.1,
  ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
    (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ),
    m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env → diagram.globRel src.2 tgt →
    (∀ n, (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
      diagram.Final m emb (sourceRun b G F n nps ph src)
        (u.output.program.2.runF (diagram.fuel n) tgt)) ∧
    (∀ n n', n ≤ n' → (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
      sourceRun b G F n' nps ph src = sourceRun b G F n nps ph src) ∧
    (∀ n, u.output.program.2.runF n tgt ≠ .error .diverge →
      ∃ j, diagram.Final m emb (sourceRun b G F j nps ph src) (u.output.program.2.runF n tgt))

/-- `RunSim` at every associated production run of the fragment is
`diagram.Simulates`. -/
theorem simulates_of_runs
    (runs : ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
      Production b u → Accepted u → diagram.Assoc b u m → RunSim b u m) :
    diagram.Simulates :=
  ⟨diagram_relations.1, diagram_relations.2.1, diagram_relations.2.2, runs⟩

variable (C : Contract)

/-- The elaboration recorded in `o` is the run `raw, sc, st ↦ P, st'`, placed
by `SProg.chain` under the output's names. -/
def Elaborated {Γ : Ctx} (o : Output C Γ) (raw : List RawStmt) (sc : ElabScope)
    (st : ECtx × Nat) (P : SProg C) (st' : ECtx × Nat) : Prop :=
  o.raw = raw ∧ o.elabScope = sc ∧ o.beforeElab.locals = st ∧ o.elaborated = P ∧
  o.afterElab.locals = st' ∧ SProg.chain o.names Γ P = .ok o.program

/-- **The obligations at a site**: every body and emitted program whose
elaboration is this run, lowered and threaded at the body's site, in the
fragment and associated by the diagram, meets `RunSim`. -/
def SiteSim (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C)
    (st' : ECtx × Nat) : Prop :=
  ∀ (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ),
    Elaborated C o raw sc st P st' → Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ →
    Accepted ⟨C, Γ, o⟩ → diagram.Assoc b ⟨C, Γ, o⟩ m → RunSim b ⟨C, Γ, o⟩ m

/-! ## The record -/

/-- The captures of an expression, at any lowered body they are the parts of. -/
def hoistQ (_ : RawExpr) (sc : ElabScope) (st : ECtx × Nat) (out : SProg C × RawExpr)
    (st' : ECtx × Nat) : Prop :=
  ∀ raw, SiteSim C raw sc st out.1 st'

/-- The captures of a statement, at any lowered body they are the parts of. -/
def hoistStmtQ (_ : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (out : SProg C × RawStmt)
    (st' : ECtx × Nat) : Prop :=
  ∀ raw, SiteSim C raw sc st out.1 st'

/-- The parts of one statement, at the lowered body that is this statement. -/
def stmtQ (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (st' : ECtx × Nat) :
    Prop :=
  SiteSim C [s] sc st P st'

/-- The parts of a block, at the lowered body that is this block. -/
def blockQ (ss : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C)
    (st' : ECtx × Nat) : Prop :=
  SiteSim C ss sc st P st'

/-- **The record simulates**: every successful output of the callbacks that
`ElabKernelInduction` ranges over meets the obligations at its site. -/
def RecSim (rc : ElabRec C) : Prop :=
  ElabSat (hoistQ C) rc.hoist ∧ ElabSat (hoistStmtQ C) rc.hoistStmt ∧
  ElabSat (stmtQ C) rc.elabStmtP ∧ ElabSat (stmtQ C) rc.elabStmt1 ∧
  ElabSat (blockQ C) rc.elabStmtsP

/-- `RecSim` is an instance of the predicates of `ElabKernelInduction`: the
arms preserve it, so the knot has it. -/
theorem recSim_of_step (rc : ElabRec C) (induction : ElabKernelInduction C rc)
    (step : ∀ r : ElabRec C, RecSim C r →
      ElabSat (hoistQ C) (hoistWith C r) ∧ ElabSat (hoistStmtQ C) (hoistStmtWith C r) ∧
      ElabSat (stmtQ C) (elabStmtPWith C r) ∧ ElabSat (stmtQ C) (elabStmt1With C r) ∧
      ElabSat (blockQ C) (elabStmtsStep C r)) :
    RecSim C rc :=
  induction (hoistQ C) (hoistStmtQ C) (stmtQ C) (stmtQ C) (blockQ C)
    fun r h s p o l => step r ⟨h, s, p, o, l⟩

/-! ## Families -/

/-- The statement families: the constructors of `PublicCompilerTotal.StmtOk`
read on the raw statement, `arith` for the arithmetic scopes, `state` for what
has no constructor there (memory, ABI, data-carrying errors, sends, `try`,
pushes, tuples), `jump` for what the lowering removes before elaboration
(`return`, `break`, `continue`, `_`), `loop` for the loops. -/
inductive StmtFamily where
  | assign | declLocal | opAssign | incDec | require | assert | revert | ite | block | jump
  | arith | declStorage | call | state | loop
  deriving DecidableEq, Repr

/-- The family of a raw statement. -/
def stmtFamily : RawStmt → StmtFamily
  | .assign _ (.call ..) | .decl _ _ (some (.call ..)) | .declStorage _ _ (some (.call ..))
  | .call .. => .call
  | .assign _ (.newArr ..) => .state
  | .assign .. => .assign
  | .decl .. => .declLocal
  | .opAssign .. => .opAssign
  | .incDec .. => .incDec
  | .require _ => .require
  | .assert _ => .assert
  | .revert => .revert
  | .ite .. => .ite
  | .block _ => .block
  | .ret _ | .brk | .cont | .hole => .jump
  | .unchecked _ | .checked .. => .arith
  | .declStorage .. => .declStorage
  | .whileLoop .. | .forLoop .. | .doWhile .. | .loop .. => .loop
  | _ => .state

/-- The expression families: operands, arithmetic and updates, and what
reaches the state or a call. -/
inductive ExprFamily where
  | operand | arith | state
  deriving DecidableEq, Repr

/-- The family of a raw expression. -/
def exprFamily : RawExpr → ExprFamily
  | .num _ | .name _ | .bool _ | .env _ | .ternary .. => .operand
  | .binop .. | .unop .. | .modular .. | .incDec .. | .assign .. | .opAssign .. => .arith
  | _ => .state

/-- A statement arm meets the obligations on a family: every successful
output of it on a statement of the family. -/
def ArmSat (arm : RawStmt → ElabM (SProg C)) (family : StmtFamily) : Prop :=
  ∀ s, stmtFamily s = family →
    ∀ sc st P st', ElabRan (arm s) sc st P st' → stmtQ C s sc st P st'

/-- The statement arms of a family meet the obligations: `elabStmtPWith`
(captures, then the statement) and `elabStmt1With` (the statement), one leaf
conjunct each. -/
def StmtArm (rc : ElabRec C) (family : StmtFamily) : Prop :=
  ArmSat C (elabStmtPWith C rc) family ∧ ArmSat C (elabStmt1With C rc) family

/-- The capture arm of a family meets the obligations: every successful
output of `hoistWith` on an expression of it. -/
def ExprArm (rc : ElabRec C) (family : ExprFamily) : Prop :=
  ∀ e, exprFamily e = family →
    ∀ sc st out st', ElabRan (hoistWith C rc e) sc st out st' → hoistQ C e sc st out st'

/-! ## The cases -/

/-- **Expression cases**: the captures of operands and of arithmetic
(`hoistWith`), the captures of statements (`hoistStmtWith`), and the checked
and unchecked arithmetic scopes. -/
def ExprCases : Prop :=
  elabKernelTotal → ∀ (C : Contract) (rc : ElabRec C), RecSim C rc →
    ExprArm C rc .operand ∧ ExprArm C rc .arith ∧
    ElabSat (hoistStmtQ C) (hoistStmtWith C rc) ∧ StmtArm C rc .arith

/-- **Statement cases**: the statements and control flow of `elabStmtPWith`
and `elabStmt1With` except loops, and the sequence of a block. -/
def StmtCases : Prop :=
  elabKernelTotal → ∀ (C : Contract) (rc : ElabRec C), RecSim C rc →
    StmtArm C rc .assign ∧ StmtArm C rc .declLocal ∧ StmtArm C rc .opAssign ∧
    StmtArm C rc .incDec ∧ StmtArm C rc .require ∧ StmtArm C rc .assert ∧
    StmtArm C rc .revert ∧ StmtArm C rc .ite ∧ StmtArm C rc .block ∧ StmtArm C rc .jump ∧
    ElabSat (blockQ C) (elabStmtsStep C rc)

/-- **State cases**: storage, memory, ABI, errors and calls: the storage
declarations, the call arms with `elabCallRetWith`, the remaining statements
and the captures that reach the state. -/
def StateCases : Prop :=
  elabKernelTotal → ∀ (C : Contract) (rc : ElabRec C), RecSim C rc →
    StmtArm C rc .declStorage ∧ StmtArm C rc .call ∧ StmtArm C rc .state ∧
    ExprArm C rc .state ∧
    ∀ f args res resW targets ctor resNew selfFrame sc st out st',
      ElabRan (elabCallRetWith C rc f args res resW targets ctor resNew selfFrame) sc st out st' →
      ∀ raw, SiteSim C raw sc st out.1 st'

/-! ## Sufficiency -/

/-- The cases and a loop hypothesis give the step of `ElabKernelInduction`. -/
theorem step_of_cases (kernel : elabKernelTotal) (exprs : ExprCases) (stmts : StmtCases)
    (states : StateCases) (loops : ∀ r : ElabRec C, RecSim C r → StmtArm C r .loop)
    (r : ElabRec C) (sim : RecSim C r) :
    ElabSat (hoistQ C) (hoistWith C r) ∧ ElabSat (hoistStmtQ C) (hoistStmtWith C r) ∧
    ElabSat (stmtQ C) (elabStmtPWith C r) ∧ ElabSat (stmtQ C) (elabStmt1With C r) ∧
    ElabSat (blockQ C) (elabStmtsStep C r) := by
  obtain ⟨operand, arith, captured, scopes⟩ := exprs kernel C r sim
  obtain ⟨assign, declLocal, opAssign, incDec, require, assert, revert, ite, block, jump,
    sequence⟩ :=
    stmts kernel C r sim
  obtain ⟨declStorage, call, state, reach, _⟩ := states kernel C r sim
  have arm (s : RawStmt) : StmtArm C r (stmtFamily s) := by
    cases family : stmtFamily s
    all_goals first
      | exact assign | exact declLocal | exact opAssign | exact incDec | exact require
      | exact assert | exact revert | exact ite | exact block | exact jump | exact scopes
      | exact declStorage | exact call | exact state | exact loops r sim
  have capture (e : RawExpr) : ExprArm C r (exprFamily e) := by
    cases family : exprFamily e
    all_goals first | exact operand | exact arith | exact reach
  exact ⟨fun e sc st out st' ran => capture e e rfl sc st out st' ran, captured,
    fun s sc st P st' ran => (arm s).1 s rfl sc st P st' ran,
    fun s sc st P st' ran => (arm s).2 s rfl sc st P st' ran, sequence⟩

/-- **The cases suffice**: with a loop hypothesis they give the per-run part
of `diagram.Simulates`, by `ElabKernelInduction` at `elabRec C ()`. -/
theorem runs_of_cases (kernel : elabKernelTotal) (exprs : ExprCases) (stmts : StmtCases)
    (states : StateCases)
    (loops : ∀ (C : Contract) (r : ElabRec C), RecSim C r → StmtArm C r .loop)
    (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) (production : Production b u)
    (accepted : Accepted u) (assoc : diagram.Assoc b u m) : RunSim b u m := by
  obtain ⟨C, Γ, o⟩ := u
  obtain ⟨_, names, induction⟩ := kernel.1 C
  have sim : RecSim C (elabRec C ()) :=
    recSim_of_step C _ induction (step_of_cases C kernel exprs stmts states (loops C))
  have block : (elabRec C ()).elabStmtsP = elabStmtsP C :=
    names.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨lowered, ⟨ran, placed⟩, threaded⟩ := production
  exact sim.2.2.2.2 o.raw o.elabScope o.beforeElab.locals o.elaborated o.afterElab.locals
    ⟨_, _, block ▸ ran⟩ b Γ o m ⟨rfl, rfl, rfl, rfl, rfl, placed⟩ lowered threaded accepted assoc

end Solidity.Correctness.Lowering.Sim
