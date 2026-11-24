import Solidity.Correctness.Lowering.Sim.Match.StatementV2

/-!
# Statement capture, sequencing and callback closure, v2 (contract)

An additive prerequisite for `Solidity.Goals.loweringBySimulation`
(ls3v-p1-statement-v2): the relation of `StatementV2.lean` (`SegSim`) read on
the elaborator's runs (`ElabRan`/`ElabSat`, `SProg` and its placement, context
maps, the callback record) and connected to the conclusions of `CasesV2.lean`.

**Contract only: unreviewed.** `CaptureLaw`, `BlockLaw`, `ClosureLaw`,
`SiteLaw` and `KnotStep` are propositions, not theorems. Proved: definitional
facts of the assembled record and bridges that only apply a hypothesis.

The Source reading of raw input (`Reading`, `Interp`) is a parameter: no
resolver from raw syntax exists. `assembled` is the knot's record from its
three generators; no field is free, so `Sim.passRec` is not of this shape.

## Limitations

* **`AssembledInduction` is a new hypothesis**, not `ElabKernelInduction`
  (`Goals/ElabTotal.lean`), whose step ranges over every record. The
  generators are `partial`; a proof belongs with the knot's totalization
  (`Correctness/Elab/Total.lean`, outside this scope).
* **`ClosureLaw` is a candidate.** It needs laws of the interpretation not
  fixed here: `Interp.ctx` closed under sub-term contexts, readings invariant
  under `foldConst` and a branch's scope, base cases for `captureExpr`, and
  `Captures` closed under sequence (the prefix stable at every state).
* `RecSeg` has no predicate for the call, ABI, dispatch, tuple, scope and loop
  fields; the capture conclusions of `CasesV2.ExprCases` are not targeted.
* No interpretation with `Covers` and `Splits` is exhibited.
-/
namespace Solidity.Correctness.Lowering.Sim.CompositionV2

open Solidity.Goals (ElabRan ElabSat elabStmtsStep)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Checker (Output ElaborationReceipt)
open StatementV2

/-- **A Source reading** at the target context `Γ`: a Source computation from
`pre` to `post`, both over `base`, and the map of its input locals into `Γ`. -/
structure Reading (Γ : Ctx) where
  E : Source.Env
  base : Source.RCtx
  pre : Source.RCtx
  post : Source.RCtx
  run : SrcRun E (pre ++ base) (post ++ base)
  map : ContextMap (pre ++ base) Γ

/-- **An interpretation**: the readings of a raw statement, a raw block and a
call with its result, under a scope, from a state, placed under the given
names; the statement contexts captures are judged in; the fuel transport. -/
structure Interp where
  fuel : Nat → Nat
  stmt : RawStmt → ElabScope → ECtx × Nat → List Var → {Γ : Ctx} → Reading Γ → Prop
  block : List RawStmt → ElabScope → ECtx × Nat → List Var → {Γ : Ctx} → Reading Γ → Prop
  call : String → List RawExpr → Option (Var × PrimTy) → ElabScope → ECtx × Nat → List Var →
    {Γ : Ctx} → Reading Γ → Prop
  ctx : {α : Type} → (α → RawStmt) → Prop

variable [FreshNames] (C : Contract) (I : Interp)

/-- **A part simulates its readings**: wherever `P` is placed, the placed
program and every reading `rd` admits there are in the statement-level
relation, to a map that extends the reading's. -/
def Seg (rd : List Var → {Γ : Ctx} → Reading Γ → Prop) (P : SProg C) : Prop :=
  ∀ (ns : List Var) (Γ Γ' : Ctx) (p : Prog C Γ Γ'), SProg.chain ns Γ P = .ok ⟨Γ', p⟩ →
    ∀ r : Reading Γ, rd ns r →
      ∃ (emb : Thin Γ Γ') (m' : ContextMap (r.post ++ r.base) Γ'),
        MapExt r.map emb m' ∧ SegSim I.fuel r.run p r.map m'

/-- The parts of one statement. -/
def stmtQ (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (_ : ECtx × Nat) : Prop :=
  Seg C I (I.stmt s sc st) P

/-- The parts of a block. -/
def blockQ (ss : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C)
    (_ : ECtx × Nat) : Prop :=
  Seg C I (I.block ss sc st) P

/-- **Statement capture**: `P` captures part of `s`, leaving `s'`. Every
reading of `s` refines a Source prefix, which the placed `P` simulates, then a
reading of `s'` from the state and at the context and names `P` leaves. -/
def Captures (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (s' : RawStmt)
    (st' : ECtx × Nat) : Prop :=
  ∀ (ns : List Var) (Γ Γ' : Ctx) (p : Prog C Γ Γ'), SProg.chain ns Γ P = .ok ⟨Γ', p⟩ →
    ∀ r : Reading Γ, I.stmt s sc st ns r →
      ∃ (mid : Source.RCtx) (κ₀ : SrcRun r.E (r.pre ++ r.base) (mid ++ r.base))
        (κ' : SrcRun r.E (mid ++ r.base) (r.post ++ r.base)) (emb : Thin Γ Γ')
        (m₁ : ContextMap (mid ++ r.base) Γ'),
        MapExt r.map emb m₁ ∧ SegSim I.fuel κ₀ p r.map m₁ ∧ r.run.Refines (κ₀.seq κ') ∧
        I.stmt s' sc st' (p.outNames ns) ⟨r.E, r.base, mid, r.post, κ', m₁⟩

/-- The captures of a term with its residual, in every admitted context. -/
def captureQ {α : Type} (a : α) (sc : ElabScope) (st : ECtx × Nat) (out : SProg C × α)
    (st' : ECtx × Nat) : Prop :=
  ∀ K : α → RawStmt, I.ctx K → Captures C I (K a) sc st out.1 (K out.2) st'

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

/-- **The assembled record**: the knot's record from its three generators. -/
def assembled (h : RawExpr → ElabM (SProg C × RawExpr)) (p : RawStmt → ElabM (SProg C))
    (c : CallRet C) : ElabRec C :=
  elabRecWithProducers C (elabRecWithCallbacks C h p c) (panicProducerWithCallbacks C p c)

/-- **No callback is free**: fields of an assembled record, from the generators. -/
theorem assembled_fields (h : RawExpr → ElabM (SProg C × RawExpr))
    (p : RawStmt → ElabM (SProg C)) (c : CallRet C) :
    (assembled C h p c).hoist = h ∧ (assembled C h p c).elabStmtP = p ∧
    (assembled C h p c).hoistTop = hoistTopWith C h ∧
    (assembled C h p c).hoistBinop = hoistBinopWith C h ∧
    (assembled C h p c).hoistAssign = hoistAssignWith C h ∧
    (assembled C h p c).hoistArgs = hoistArgsWith C h ∧
    (assembled C h p c).hoistCallArgs = hoistCallArgsWith C h p ∧
    (assembled C h p c).elabStmtsP = elabStmtsPWith C p ∧
    (assembled C h p c).elabBranch = elabBranchWith C p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The record simulates, v2**: the capture, statement and block fields. -/
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
/-- **Block readings split** along the statement callback `stmt`: the empty
block reads as nothing; the block of one statement reads as the statement; a
reading of `s :: ss` refines a reading of `s`, then, after any run of `stmt`
on `s` whose placed output simulates that reading, a reading of `ss` from the
state, context, names and map it leaves. -/
structure Interp.Splits (stmt : RawStmt → ElabM (SProg C)) : Prop where
  nil : ∀ sc st ns (Γ : Ctx) (r : Reading Γ), I.block [] sc st ns r →
    ∃ m' : ContextMap (r.post ++ r.base) Γ, MapExt r.map .refl m' ∧
      SegSim I.fuel r.run (.nil : Prog C Γ Γ) r.map m'
  single : ∀ s sc st ns (Γ : Ctx) (r : Reading Γ), I.block [s] sc st ns r → I.stmt s sc st ns r
  cons : ∀ s ss sc st ns (Γ : Ctx) (r : Reading Γ), I.block (s :: ss) sc st ns r →
    ∃ (mid : Source.RCtx) (κ₁ : SrcRun r.E (r.pre ++ r.base) (mid ++ r.base))
      (κ₂ : SrcRun r.E (mid ++ r.base) (r.post ++ r.base)),
      I.stmt s sc st ns ⟨r.E, r.base, r.pre, mid, κ₁, r.map⟩ ∧ r.run.Refines (κ₁.seq κ₂) ∧
      ∀ (P : SProg C) (st₁ : ECtx × Nat) (Γ' : Ctx) (p : Prog C Γ Γ') (emb : Thin Γ Γ')
        (m₁ : ContextMap (mid ++ r.base) Γ'), ElabRan (stmt s) sc st P st₁ →
        SProg.chain ns Γ P = .ok ⟨Γ', p⟩ → MapExt r.map emb m₁ → SegSim I.fuel κ₁ p r.map m₁ →
        I.block ss sc st₁ (p.outNames ns) ⟨r.E, r.base, mid, r.post, κ₂, m₁⟩

/-- **The interpretation covers the production bodies**: at every associated
production run of the fragment, the producer's fresh state is sound and the
lowered raw input, at the placement of the run, has a reading over the body's
context under the association's map that the body's settled Source run refines. -/
def Interp.Covers : Prop :=
  ∀ (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ),
    ElaborationReceipt o → Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ → Accepted ⟨C, Γ, o⟩ →
    diagram.Assoc b ⟨C, Γ, o⟩ m →
    LowerFresh b ⟨C, Γ, o⟩ ∧ ∃ κ : SrcRun b.E b.ctx b.ctx,
      I.block o.raw o.elabScope o.beforeElab.locals o.names ⟨b.E, b.ctx, [], [], κ, m⟩ ∧
      (SrcRun.ofStmt b.input.resolved).settled.Refines κ

/-- **Capture then statement** are the statement's parts (`elabStmtPWith`). -/
def CaptureLaw : Prop :=
  ∀ s sc st (P : SProg C) s' st₁ (Q : SProg C) st₂, Captures C I s sc st P s' st₁ →
    stmtQ C I s' sc st₁ Q st₂ → stmtQ C I s sc st (P ++ Q) st₂

/-- **Block sequencing**: blocks of a simulating statement callback simulate. -/
def BlockLaw : Prop :=
  ∀ stmt : RawStmt → ElabM (SProg C), I.Splits C stmt → ElabSat (stmtQ C I) stmt →
    ElabSat (blockQ C I) (elabStmtsPWith C stmt)

/-- **Callback closure** (candidate; see "Limitations"): at simulating
generators, the assembled record simulates once its two statement arms do. -/
def ClosureLaw : Prop :=
  ∀ h p c, GenSeg C I h p c → I.Splits C p →
    ElabSat (captureQ C I) (assembled C h p c).hoistStmt →
    ElabSat (stmtQ C I) (assembled C h p c).elabStmt1 → RecSeg C I (assembled C h p c)

/-- A block's parts meet the v2 site obligation. -/
def Sites : Prop :=
  ∀ raw sc st (P : SProg C) st', blockQ C I raw sc st P st' → SiteSim₂ C raw sc st P st'

/-- **Whole bodies**: at the diagram's fuel, under a covering interpretation. -/
def SiteLaw : Prop :=
  I.fuel = diagram.fuel → I.Covers C → Sites C I

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

/-- **The step** (the cases' obligation, v2) over assembled records. -/
def KnotStep : Prop :=
  ∀ h p c, GenSeg C I h p c →
    GenSeg C I (hoistWith C (assembled C h p c)) (elabStmtPWith C (assembled C h p c))
      (callRetArm C (assembled C h p c))

/-- **Bridge**: the step and the induction give the knot's generators. -/
theorem knot_genSeg (induction : AssembledInduction C) (step : KnotStep C I) :
    GenSeg C I (hoist C) (elabStmtP C) (@elabCallRet C _) :=
  induction (captureQ C I) (stmtQ C I) (callQ C I) fun h p c sh sp sc => step h p c ⟨sh, sp, sc⟩

/-- **Bridge**: a simulating arm meets `Stmt.V2.ArmSat` (`CasesV2`), every family. -/
theorem armSat_of_stmt (sites : Sites C I)
    (single : ∀ s sc st ns (Γ : Ctx) (r : Reading Γ), I.block [s] sc st ns r → I.stmt s sc st ns r)
    (arm : RawStmt → ElabM (SProg C)) (h : ElabSat (stmtQ C I) arm) (family : StmtFamily) :
    Stmt.V2.ArmSat C arm family :=
  fun s _ sc st P st' ran => sites _ _ _ _ _ fun ns Γ Γ' p placed r read =>
    h s sc st P st' ran ns Γ Γ' p placed r (single s sc st ns Γ r read)

/-- **Bridge**: the per-run v2 obligation at production, from the knot's blocks. -/
theorem runs₂_of_segments (sites : Sites C I) (block : ElabSat (blockQ C I) (elabStmtsP C))
    (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ)
    (production : Production b ⟨C, Γ, o⟩) (accepted : Accepted ⟨C, Γ, o⟩)
    (assoc : diagram.Assoc b ⟨C, Γ, o⟩ m) : RunSim₂ b ⟨C, Γ, o⟩ m := by
  obtain ⟨lowered, ⟨ran, placed⟩, threaded⟩ := production
  exact sites o.raw o.elabScope o.beforeElab.locals o.elaborated o.afterElab.locals
    (block o.raw o.elabScope o.beforeElab.locals o.elaborated o.afterElab.locals ⟨_, _, ran⟩)
    b Γ o m ⟨rfl, rfl, rfl, rfl, rfl, ran, placed⟩ lowered threaded accepted assoc

end Solidity.Correctness.Lowering.Sim.CompositionV2
