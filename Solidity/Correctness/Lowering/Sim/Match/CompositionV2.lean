import Solidity.Correctness.Lowering.Sim.Match.StatementV2

/-!
# Statement capture, sequencing and callback closure, v2 (contract)

An additive prerequisite for `Solidity.Goals.loweringBySimulation`
(ls3v-p1-statement-v2). The statement-level relation of `StatementV2.lean`
(`SegSim`) read on the elaborator's runs: `ElabRan`/`ElabSat`, `SProg` and its
placement, context maps, the callback record and the conclusions of
`CasesV2.lean`.

**Contract only: unreviewed.** Predicates and laws are stated; the laws
(`CaptureLaw`, `BlockLaw`, `ClosureLaw`, `SingletonLaw`, `SiteLaw`,
`KnotStep`) are propositions, not theorems. Proved here: definitional facts of
the assembled record and bridges that only apply a law.

* `Reading`, `Interp`: the Source reading of raw input at a host context (a
  Source computation and a context map) is a parameter. No resolver from raw
  syntax to Source exists at the base; whoever associates bodies supplies it
  (`Interp.Covers`).
* `Seg`, `stmtQ`, `blockQ`: a part, wherever `SProg.chain` places it,
  simulates every reading of its input and extends the reading's map.
* `Captures`, `captureQ`: captures `P` with a residual. The reading of the
  input refines a Source prefix that `P` simulates, then a reading of the
  residual at the context `P` leaves; for every statement context the
  interpretation admits (`Interp.ctx`), so an expression's captures are judged
  in the statement that holds it.
* `assembled`: the record of the knot from its three generators (`hoist`,
  `elabStmtP`, `elabCallRet`). Every field is a function of them, so no
  callback is free: `Sim.passRec` is not of this shape. `RecSeg` gives the
  capture, statement and block callbacks their predicates.
* `AssembledInduction`: induction over the knot's runs with a step asked at
  assembled records only.

## Limitations

* **`AssembledInduction` is not `ElabKernelInduction`**
  (`Goals/ElabTotal.lean`), whose step ranges over every record and so cannot
  be discharged where an arm calls a field outside its five (`hoistTop`,
  `elabBranch`, …). It is a hypothesis here; a proof belongs to the owner of
  the knot's totalization (`Correctness/Elab/Total.lean`, outside this scope).
* `RecSeg` has no predicate for the call, ABI, dispatch, tuple and loop
  callbacks (`elabCall`, `abiEncode`, `fnDispatch`, `elabTuple`, `loopExpr`,
  …): they are fixed by the generators through `assembled`, and their
  conclusions are the state and loop cases'.
* The capture conclusions of `CasesV2.ExprCases` (`CasesV2.captureQ`, a whole
  body for every raw input) do not follow from `captureQ` and are not
  targeted: `Sim/Expr/Strength.lean` shows them as strong as the diagram.
-/
namespace Solidity.Correctness.Lowering.Sim.CompositionV2

open Solidity.Goals (ElabRan ElabSat elabStmtsStep)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Checker (Output ElaborationReceipt)
open StatementV2

/-! ## Readings -/

/-- **A Source reading** at the target context `Γ`: a Source computation and
the map of its input locals into `Γ`. -/
structure Reading (Γ : Ctx) where
  E : Source.Env
  Γs : Source.RCtx
  Δs : Source.RCtx
  run : SrcRun E Γs Δs
  map : ContextMap Γs Γ

/-- **An interpretation**: which readings a raw statement, a raw block and a
call with its result have, elaborated under a scope from a state and placed
in a context with the given names; the statement contexts captures are judged
in; the fuel transport. -/
structure Interp where
  fuel : Nat → Nat
  stmt : RawStmt → ElabScope → ECtx × Nat → List Var → {Γ : Ctx} → Reading Γ → Prop
  block : List RawStmt → ElabScope → ECtx × Nat → List Var → {Γ : Ctx} → Reading Γ → Prop
  call : String → List RawExpr → Option (Var × PrimTy) → ElabScope → ECtx × Nat → List Var →
    {Γ : Ctx} → Reading Γ → Prop
  ctx : {α : Type} → (α → RawStmt) → Prop

variable [FreshNames] (C : Contract) (I : Interp)

/-! ## Parts -/

/-- **A part simulates its readings**: wherever `P` is placed, for every
reading `rd` admits there, the placed program and the reading's computation
are in the statement-level relation, to a map that extends the reading's. -/
def Seg (rd : List Var → {Γ : Ctx} → Reading Γ → Prop) (P : SProg C) : Prop :=
  ∀ (ns : List Var) (Γ Γ' : Ctx) (p : Prog C Γ Γ'), SProg.chain ns Γ P = .ok ⟨Γ', p⟩ →
    ∀ r : Reading Γ, rd ns r →
      ∃ (emb : Thin Γ Γ') (m' : ContextMap r.Δs Γ'),
        MapExt r.map emb m' ∧ SegSim I.fuel r.run p r.map m'

/-- The parts of one statement. -/
def stmtQ (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (_ : ECtx × Nat) : Prop :=
  Seg C I (I.stmt s sc st) P

/-- The parts of a block. -/
def blockQ (ss : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C)
    (_ : ECtx × Nat) : Prop :=
  Seg C I (I.block ss sc st) P

/-- **Statement capture**: `P` captures part of `s`, leaving `s'`. Every
reading of `s` refines a Source prefix, which the placed `P` simulates to an
intermediate map, followed by a reading of `s'` from the state and at the
context and names `P` leaves. -/
def Captures (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (s' : RawStmt)
    (st' : ECtx × Nat) : Prop :=
  ∀ (ns : List Var) (Γ Γ' : Ctx) (p : Prog C Γ Γ'), SProg.chain ns Γ P = .ok ⟨Γ', p⟩ →
    ∀ r : Reading Γ, I.stmt s sc st ns r →
      ∃ (Γ₁ : Source.RCtx) (κ₀ : SrcRun r.E r.Γs Γ₁) (κ' : SrcRun r.E Γ₁ r.Δs) (emb : Thin Γ Γ')
        (m₁ : ContextMap Γ₁ Γ'),
        MapExt r.map emb m₁ ∧ SegSim I.fuel κ₀ p r.map m₁ ∧ r.run.Refines (κ₀.seq κ') ∧
        I.stmt s' sc st' (p.outNames ns) ⟨r.E, Γ₁, r.Δs, κ', m₁⟩

/-- The captures of a term (an expression, arguments, a statement) with its
residual, in every admitted statement context. -/
def captureQ {α : Type} (a : α) (sc : ElabScope) (st : ECtx × Nat) (out : SProg C × α)
    (st' : ECtx × Nat) : Prop :=
  ∀ K : α → RawStmt, I.ctx K → Captures C I (K a) sc st out.1 (K out.2) st'

/-! ## The record -/

/-- The output of `elabCallRet`. -/
abbrev CallOut := SProg C × Option (NCtx × RefTy × Var × Bool) × List (Var × LocalTy)

/-- The type of `elabCallRet`, the third generator of the knot (its defaults dropped). -/
abbrev CallRet := String → List RawExpr → Option (Var × PrimTy) → Nat → Bool → Bool → Bool →
    Bool → ElabM (CallOut C)

/-- The arm `elabCallRetWith` over a record, as a generator. -/
def callRetArm (rc : ElabRec C) : CallRet C :=
  fun f args res resW targets ctor resNew selfFrame =>
    elabCallRetWith C rc f args res resW targets ctor resNew selfFrame

/-- Every successful run of a call callback meets `Q`. -/
def CallSat (Q : String → List RawExpr → Option (Var × PrimTy) → ElabScope → ECtx × Nat →
    CallOut C → ECtx × Nat → Prop) (c : CallRet C) : Prop :=
  ∀ f args res resW targets ctor resNew selfFrame sc st out st',
    ElabRan (c f args res resW targets ctor resNew selfFrame) sc st out st' →
    Q f args res sc st out st'

/-- The parts of a call with its result. -/
def callQ (f : String) (args : List RawExpr) (res : Option (Var × PrimTy)) (sc : ElabScope)
    (st : ECtx × Nat) (out : CallOut C) (_ : ECtx × Nat) : Prop :=
  Seg C I (I.call f args res sc st) out.1

/-- **The generators simulate**: the three callbacks the knot is tied on. -/
def GenSeg (h : RawExpr → ElabM (SProg C × RawExpr)) (p : RawStmt → ElabM (SProg C))
    (c : CallRet C) : Prop :=
  ElabSat (captureQ C I) h ∧ ElabSat (stmtQ C I) p ∧ CallSat C (callQ C I) c

/-- **The assembled record**: the knot's record from its three generators
(`elabRecWithCallbacks`, `elabRecWithProducers`). -/
def assembled (h : RawExpr → ElabM (SProg C × RawExpr)) (p : RawStmt → ElabM (SProg C))
    (c : CallRet C) : ElabRec C :=
  elabRecWithProducers C (elabRecWithCallbacks C h p c) (panicProducerWithCallbacks C p c)

/-- The knot's record is assembled from the knot's generators. -/
theorem elabRec_assembled :
    elabRec C () = assembled C (hoist C) (elabStmtP C) (@elabCallRet C _) := rfl

/-- **No callback is free**: the capture, statement and block fields of an
assembled record are the generators and their derived forms. -/
theorem assembled_fields (h : RawExpr → ElabM (SProg C × RawExpr))
    (p : RawStmt → ElabM (SProg C)) (c : CallRet C) :
    (assembled C h p c).hoist = h ∧ (assembled C h p c).elabStmtP = p ∧
    (assembled C h p c).hoistTop = hoistTopWith C h ∧
    (assembled C h p c).hoistBinop = hoistBinopWith C h ∧
    (assembled C h p c).hoistAssign = hoistAssignWith C h ∧
    (assembled C h p c).hoistArgs = hoistArgsWith C h ∧
    (assembled C h p c).hoistCallArgs = hoistCallArgsWith C h p ∧
    (assembled C h p c).elabStmtsP = elabStmtsPWith C p ∧
    (assembled C h p c).elabBranch = elabBranchWith C p ∧
    (assembled C h p c).elabScope = elabScopeWith C (elabBranchWith C p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The record simulates, v2**: every capture, statement and block callback
meets its predicate (v1 `RecSim` constrains five). -/
structure RecSeg (rc : ElabRec C) : Prop where
  hoist : ElabSat (captureQ C I) rc.hoist
  hoistTop : ElabSat (captureQ C I) rc.hoistTop
  hoistBinop : ∀ op a b sc st out st', ElabRan (rc.hoistBinop op a b) sc st out st' →
    captureQ C I (RawExpr.binop op a b) sc st out st'
  hoistAssign : ∀ l r sc st out st', ElabRan (rc.hoistAssign l r) sc st out st' →
    captureQ C I (RawStmt.assign l r) sc st out st'
  hoistArgs : ElabSat (captureQ C I) rc.hoistArgs
  hoistCallArgs : ∀ f, ElabSat (captureQ C I) (rc.hoistCallArgs f)
  hoistStmt : ElabSat (captureQ C I) rc.hoistStmt
  elabStmtP : ElabSat (stmtQ C I) rc.elabStmtP
  elabStmt1 : ElabSat (stmtQ C I) rc.elabStmt1
  elabStmtsP : ElabSat (blockQ C I) rc.elabStmtsP
  elabBranch : ElabSat (blockQ C I) rc.elabBranch
  elabScope : ∀ (Γ : NCtx) ss sc st (b : Blk C Γ.ctx) st',
    ElabRan (rc.elabScope Γ ss) sc st b st' → ∀ r : Reading Γ.ctx, I.block ss sc st Γ.names r →
      ∃ (emb : Thin Γ.ctx b.1) (m' : ContextMap r.Δs b.1),
        MapExt r.map emb m' ∧ SegSim I.fuel r.run b.2 r.map m'

/-! ## What the interpretation owes -/

/-- **Block readings split** along the statement callback `stmt`: the empty
block reads as nothing; a reading of `s :: ss` refines a reading of `s`, then,
after any run of `stmt` on `s` whose placed output simulates that reading, a
reading of `ss` from the state, context, names and map it leaves. -/
structure Interp.Splits (stmt : RawStmt → ElabM (SProg C)) : Prop where
  nil : ∀ sc st ns (Γ : Ctx) (r : Reading Γ), I.block [] sc st ns r →
    ∃ m' : ContextMap r.Δs Γ, MapExt r.map .refl m' ∧
      SegSim I.fuel r.run (.nil : Prog C Γ Γ) r.map m'
  cons : ∀ s ss sc st ns (Γ : Ctx) (r : Reading Γ), I.block (s :: ss) sc st ns r →
    ∃ (Γ₁ : Source.RCtx) (κ₁ : SrcRun r.E r.Γs Γ₁) (κ₂ : SrcRun r.E Γ₁ r.Δs),
      I.stmt s sc st ns ⟨r.E, r.Γs, Γ₁, κ₁, r.map⟩ ∧ r.run.Refines (κ₁.seq κ₂) ∧
      ∀ (P : SProg C) (st₁ : ECtx × Nat) (Γ' : Ctx) (p : Prog C Γ Γ') (emb : Thin Γ Γ')
        (m₁ : ContextMap Γ₁ Γ'), ElabRan (stmt s) sc st P st₁ →
        SProg.chain ns Γ P = .ok ⟨Γ', p⟩ → MapExt r.map emb m₁ → SegSim I.fuel κ₁ p r.map m₁ →
        I.block ss sc st₁ (p.outNames ns) ⟨r.E, Γ₁, r.Δs, κ₂, m₁⟩

/-- **The interpretation covers the production bodies**: at every associated
production run of the fragment, the producer's fresh state is sound and the
lowered raw input, at the placement of the run, has a reading under the
association's map that the body's settled Source run refines. -/
def Interp.Covers : Prop :=
  ∀ (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ),
    ElaborationReceipt o → Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ → Accepted ⟨C, Γ, o⟩ →
    diagram.Assoc b ⟨C, Γ, o⟩ m →
    LowerFresh b ⟨C, Γ, o⟩ ∧ ∃ κ : SrcRun b.E b.ctx b.ctx,
      I.block o.raw o.elabScope o.beforeElab.locals o.names ⟨b.E, b.ctx, b.ctx, κ, m⟩ ∧
      (SrcRun.ofStmt b.input.resolved).settled.Refines κ

/-! ## Laws (statements; proved after review) -/

/-- **Capture then statement**: captures of `s` leaving `s'`, then the parts
of `s'`, are the parts of `s` (`elabStmtPWith`). -/
def CaptureLaw : Prop :=
  ∀ s sc st (P : SProg C) s' st₁ (Q : SProg C) st₂, Captures C I s sc st P s' st₁ →
    stmtQ C I s' sc st₁ Q st₂ → stmtQ C I s sc st (P ++ Q) st₂

/-- **Block sequencing**: where block readings split along a statement
callback that simulates, its blocks simulate (`elabStmtsPWith`). -/
def BlockLaw : Prop :=
  ∀ stmt : RawStmt → ElabM (SProg C), I.Splits C stmt → ElabSat (stmtQ C I) stmt →
    ElabSat (blockQ C I) (elabStmtsPWith C stmt)

/-- **Callback closure**: at generators that simulate, with block readings
that split, the assembled record simulates once its two statement arms do. -/
def ClosureLaw : Prop :=
  ∀ h p c, GenSeg C I h p c → I.Splits C p →
    ElabSat (captureQ C I) (assembled C h p c).hoistStmt →
    ElabSat (stmtQ C I) (assembled C h p c).elabStmt1 → RecSeg C I (assembled C h p c)

/-- A statement's parts are the parts of the block of that statement. -/
def SingletonLaw : Prop :=
  ∀ s sc st (P : SProg C) st', stmtQ C I s sc st P st' → blockQ C I [s] sc st P st'

/-- A block's parts meet the v2 site obligation. -/
def Sites : Prop :=
  ∀ raw sc st (P : SProg C) st', blockQ C I raw sc st P st' → SiteSim₂ C raw sc st P st'

/-- **Whole bodies**: at the diagram's fuel, under a covering interpretation,
a block's parts meet the v2 site obligation. -/
def SiteLaw : Prop :=
  I.fuel = diagram.fuel → I.Covers C → Sites C I

/-! ## The knot -/

/-- **Induction over the knot's runs at assembled records** (a hypothesis;
see "Limitations"): predicates on the runs of the three generators that the
arms keep over every assembled record hold of the knot. -/
def AssembledInduction : Prop :=
  ∀ (QH : RawExpr → ElabScope → ECtx × Nat → SProg C × RawExpr → ECtx × Nat → Prop)
    (QP : RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop)
    (QC : String → List RawExpr → Option (Var × PrimTy) → ElabScope → ECtx × Nat → CallOut C →
      ECtx × Nat → Prop),
    (∀ h p c, ElabSat QH h → ElabSat QP p → CallSat C QC c →
      ElabSat QH (hoistWith C (assembled C h p c)) ∧
        ElabSat QP (elabStmtPWith C (assembled C h p c)) ∧
        CallSat C QC (callRetArm C (assembled C h p c))) →
    ElabSat QH (hoist C) ∧ ElabSat QP (elabStmtP C) ∧ CallSat C QC (@elabCallRet C _)

/-- **The step** (the cases' obligation, v2): the arms keep `GenSeg` over
assembled records. -/
def KnotStep : Prop :=
  ∀ h p c, GenSeg C I h p c →
    GenSeg C I (hoistWith C (assembled C h p c)) (elabStmtPWith C (assembled C h p c))
      (callRetArm C (assembled C h p c))

/-- **Bridge**: the step and the induction give the knot's generators. -/
theorem knot_genSeg (induction : AssembledInduction C) (step : KnotStep C I) :
    GenSeg C I (hoist C) (elabStmtP C) (@elabCallRet C _) :=
  induction (captureQ C I) (stmtQ C I) (callQ C I) fun h p c sh sp sc => step h p c ⟨sh, sp, sc⟩

/-- **Bridge**: the knot's blocks simulate, by the block law. -/
theorem knot_blocks (block : BlockLaw C I) (splits : I.Splits C (elabStmtP C))
    (gen : GenSeg C I (hoist C) (elabStmtP C) (@elabCallRet C _)) :
    ElabSat (blockQ C I) (elabStmtsP C) :=
  block (elabStmtP C) splits gen.2.1

/-! ## The conclusions of `CasesV2` -/

/-- **Bridge**: a statement arm that simulates meets `Stmt.V2.ArmSat` on
every family. -/
theorem armSat_of_stmt (sites : Sites C I) (single : SingletonLaw C I)
    (arm : RawStmt → ElabM (SProg C)) (h : ElabSat (stmtQ C I) arm) (family : StmtFamily) :
    Stmt.V2.ArmSat C arm family :=
  fun s _ sc st P st' ran => sites _ _ _ _ _ (single _ _ _ _ _ (h s sc st P st' ran))

/-- **Bridge**: the statement conclusions of `CasesV2`, loops included, from
arms and a block step that simulate. -/
theorem stmtCases_of_segments (sites : Sites C I) (single : SingletonLaw C I) (rc : ElabRec C)
    (armP : ElabSat (stmtQ C I) (elabStmtPWith C rc))
    (arm1 : ElabSat (stmtQ C I) (elabStmt1With C rc))
    (block : ElabSat (blockQ C I) (elabStmtsStep C rc)) :
    CasesV2.StmtCases C rc ∧ Stmt.V2.StmtArm C rc .loop := by
  have arm (family : StmtFamily) : Stmt.V2.StmtArm C rc family :=
    ⟨armSat_of_stmt C I sites single _ armP family, armSat_of_stmt C I sites single _ arm1 family⟩
  exact ⟨⟨arm _, arm _, arm _, arm _, arm _, arm _, arm _, arm _, arm _, arm _,
    fun ss sc st P st' ran => sites _ _ _ _ _ (block ss sc st P st' ran)⟩, arm _⟩

/-- **Bridge**: the per-run v2 obligation at every associated production run
of the fragment, from the knot's blocks. -/
theorem runs₂_of_segments (sites : Sites C I) (block : ElabSat (blockQ C I) (elabStmtsP C))
    (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ)
    (production : Production b ⟨C, Γ, o⟩) (accepted : Accepted ⟨C, Γ, o⟩)
    (assoc : diagram.Assoc b ⟨C, Γ, o⟩ m) : RunSim₂ b ⟨C, Γ, o⟩ m := by
  obtain ⟨lowered, ⟨ran, placed⟩, threaded⟩ := production
  exact sites o.raw o.elabScope o.beforeElab.locals o.elaborated o.afterElab.locals
    (block o.raw o.elabScope o.beforeElab.locals o.elaborated o.afterElab.locals ⟨_, _, ran⟩)
    b Γ o m ⟨rfl, rfl, rfl, rfl, rfl, ran, placed⟩ lowered threaded accepted assoc

end Solidity.Correctness.Lowering.Sim.CompositionV2
