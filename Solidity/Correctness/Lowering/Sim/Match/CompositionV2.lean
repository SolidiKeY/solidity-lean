import Solidity.Correctness.Lowering.Sim.Match.StatementV2

/-!
# Statement capture, sequencing and callback closure, v2 (contract)

An additive prerequisite for `Solidity.Goals.loweringBySimulation`: `SegSim`
(`StatementV2.lean`) read on the elaborator's runs, `SProg` placement, context
maps and the callback record, and connected to `CasesV2.lean`.
**Contract only.** `CaptureLaw`, `BlockLaw`, `SiteLaw` and `KnotStep` are
propositions; proved are facts of the assembled record and bridges that only
apply a hypothesis. The Source reading of raw input (`Reading`: resolved
Source items, H1422 option B, with a fuel transport) is a parameter
(`Interp`): no resolver from raw syntax exists. `assembled` is the knot's
record from its three generators; no field is free (unlike `Sim.passRec`).

## Limitations

* **`AssembledInduction` is a new hypothesis** (additive, H1423), not
  `ElabKernelInduction`, whose step ranges over every record. The generators
  are `partial`; a proof belongs with the knot's totalization.
* Callback closure is stated as shape only (`assembled_fields`): predicates
  for the derived capture, branch, call, ABI, dispatch, tuple and loop fields
  wait for the interpretation's base cases (this step, H1417) and its
  invariance under `foldConst` and a branch's scope (P2-P5). The capture
  conclusions of `CasesV2.ExprCases` are not targeted.
* No interpretation with `Covers` and `Splits` is exhibited.
-/
namespace Solidity.Correctness.Lowering.Sim.CompositionV2

open Solidity.Goals (ElabRan ElabSat elabStmtsStep)
open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Checker (Output ElaborationReceipt)
open StatementV2

/-- **A Source reading** at the target context `Γ`: resolved Source items
from `pre` to `post`, both over `base`, the map of their input locals into
`Γ`, and the fuel transport they are simulated at. -/
structure Reading (Γ : Ctx) where
  E : Source.Env
  R : List Source.STy
  M : Bool
  k : Source.SCtx
  base : Source.RCtx
  pre : Source.RCtx
  post : Source.RCtx
  items : Source.RItems E R M k (pre ++ base) (post ++ base)
  map : ContextMap (pre ++ base) Γ
  fuel : Nat → Nat

/-- **An interpretation**: the readings of a raw statement, a raw block and a
call with its result, under a scope, from a state, placed under the given
names; the statement contexts captures are judged in. -/
structure Interp where
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
        MapExt r.map emb m' ∧ SegSim r.fuel r.items p r.map m'

/-- The parts of one statement. -/
def stmtQ (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (_ : ECtx × Nat) : Prop :=
  Seg C (I.stmt s sc st) P

/-- The parts of a block. -/
def blockQ (ss : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C)
    (_ : ECtx × Nat) : Prop :=
  Seg C (I.block ss sc st) P

/-- **Statement capture**: `P` captures part of `s`, leaving `s'`. Every
reading of `s` refines, within `c` horizon steps, Source items that the placed
`P` simulates, then a reading of `s'` from the state and at the context and
names `P` leaves, both at a monotone fuel that fits the reading's. -/
def Captures (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (s' : RawStmt)
    (st' : ECtx × Nat) : Prop :=
  ∀ (ns : List Var) (Γ Γ' : Ctx) (p : Prog C Γ Γ'), SProg.chain ns Γ P = .ok ⟨Γ', p⟩ →
    ∀ r : Reading Γ, I.stmt s sc st ns r →
      ∃ (mid : Source.RCtx) (a₀ : Source.RItems r.E r.R r.M r.k (r.pre ++ r.base) (mid ++ r.base))
        (a' : Source.RItems r.E r.R r.M r.k (mid ++ r.base) (r.post ++ r.base)) (emb : Thin Γ Γ')
        (m₁ : ContextMap (mid ++ r.base) Γ') (c : Nat) (g : Nat → Nat),
        MapExt r.map emb m₁ ∧ SegSim g a₀ p r.map m₁ ∧
        (SrcRun.ofItems r.items).Refines (SrcRun.ofItems (append a₀ a')) c ∧
        (∀ n n', n ≤ n' → g n ≤ g n') ∧ (∀ n, g (n + c) ≤ r.fuel n) ∧
        I.stmt s' sc st' (p.outNames ns) ⟨r.E, r.R, r.M, r.k, r.base, mid, r.post, a', m₁, g⟩

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
  Seg C (I.call f args res sc st) out.1

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

/-- **Block readings split** along the statement callback `stmt`: the empty
block reads as nothing; the block of one statement as the statement; `s :: ss`
refines a reading of `s`, then, after any run of `stmt` on `s` whose placed
output simulates it, a reading of `ss` where it leaves; at a fuel that fits. -/
structure Interp.Splits (stmt : RawStmt → ElabM (SProg C)) : Prop where
  nil : ∀ sc st ns (Γ : Ctx) (r : Reading Γ), I.block [] sc st ns r →
    ∃ m' : ContextMap (r.post ++ r.base) Γ, MapExt r.map .refl m' ∧
      SegSim r.fuel r.items (.nil : Prog C Γ Γ) r.map m'
  single : ∀ s sc st ns (Γ : Ctx) (r : Reading Γ), I.block [s] sc st ns r → I.stmt s sc st ns r
  cons : ∀ s ss sc st ns (Γ : Ctx) (r : Reading Γ), I.block (s :: ss) sc st ns r →
    ∃ (mid : Source.RCtx) (a₁ : Source.RItems r.E r.R r.M r.k (r.pre ++ r.base) (mid ++ r.base))
      (a₂ : Source.RItems r.E r.R r.M r.k (mid ++ r.base) (r.post ++ r.base)) (c : Nat)
      (g : Nat → Nat),
      I.stmt s sc st ns ⟨r.E, r.R, r.M, r.k, r.base, r.pre, mid, a₁, r.map, g⟩ ∧
      (SrcRun.ofItems r.items).Refines (SrcRun.ofItems (append a₁ a₂)) c ∧
      (∀ n n', n ≤ n' → g n ≤ g n') ∧ (∀ n, g (n + c) ≤ r.fuel n) ∧
      ∀ (P : SProg C) (st₁ : ECtx × Nat) (Γ' : Ctx) (p : Prog C Γ Γ') (emb : Thin Γ Γ')
        (m₁ : ContextMap (mid ++ r.base) Γ'), ElabRan (stmt s) sc st P st₁ →
        SProg.chain ns Γ P = .ok ⟨Γ', p⟩ → MapExt r.map emb m₁ → SegSim g a₁ p r.map m₁ →
        I.block ss sc st₁ (p.outNames ns) ⟨r.E, r.R, r.M, r.k, r.base, mid, r.post, a₂, m₁, g⟩

/-- **The interpretation covers the production bodies**: at every associated
production run the producer's fresh state is sound and the lowered raw input
reads, under the association's map, as Source items that the body's settled
Source run refines at a fuel that fits the diagram's. -/
def Interp.Covers : Prop :=
  ∀ (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ),
    ElaborationReceipt o → Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ → Accepted ⟨C, Γ, o⟩ →
    diagram.Assoc b ⟨C, Γ, o⟩ m →
    LowerFresh b ⟨C, Γ, o⟩ ∧ ∃ (R : List Source.STy) (M : Bool) (k : Source.SCtx)
      (a : Source.RItems b.E R M k b.ctx b.ctx) (c : Nat) (g : Nat → Nat),
      I.block o.raw o.elabScope o.beforeElab.locals o.names ⟨b.E, R, M, k, b.ctx, [], [], a, m, g⟩ ∧
      SrcRun.Refines (SrcRun.settled (SrcRun.ofStmt b.input.resolved)) (SrcRun.ofItems a) c ∧
      ∀ n, g (n + c) ≤ diagram.fuel n

/-- **Capture then statement** are the statement's parts (`elabStmtPWith`). -/
def CaptureLaw : Prop :=
  ∀ s sc st (P : SProg C) s' st₁ (Q : SProg C) st₂, Captures C I s sc st P s' st₁ →
    stmtQ C I s' sc st₁ Q st₂ → stmtQ C I s sc st (P ++ Q) st₂

/-- **Block sequencing**: blocks of a simulating statement callback simulate. -/
def BlockLaw : Prop :=
  ∀ stmt : RawStmt → ElabM (SProg C), I.Splits C stmt → ElabSat (stmtQ C I) stmt →
    ElabSat (blockQ C I) (elabStmtsPWith C stmt)

/-- A block's parts meet the v2 site obligation. -/
def Sites : Prop :=
  ∀ raw sc st (P : SProg C) st', blockQ C I raw sc st P st' → SiteSim₂ C raw sc st P st'

/-- **Whole bodies**, under a covering interpretation. -/
def SiteLaw : Prop :=
  I.Covers C → Sites C I

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
