import Solidity.Backend.InternalFlow.RuntimeFrameContext
import Solidity.Backend.InternalFlow.RuntimeFrameTransport

/-! Frozen P1 runtime-frame interface, version 1. The definitions state
relations and unproved producer obligations over existing intrinsic syntax and
execution. There is no axiom, proof stub, new evaluator or producer instance,
and nothing asserts that the `Pending*` structures are inhabited. A signature
change goes to a new version. The recursive-return obligations do not assert
G37.02 finite-prefix/divergence closure and do not remove source `recDepth`.
See `docs/feature-work/runtime-frame-p1.md`.
-/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1
open Evm Evm.Memory

/-- Static emitter metadata. Runtime arena words and source heap allocation
cost are DISTINCT budgets. No soundness is hidden in this data record. -/
structure Emission (C : Contract) (Γ Δ : Ctx) where
 code : List Instr
 frag : Frag Δ
 need : Nat
 localLimit : Nat
 pointerCell : Nat
 arenaWords : State C Γ → Nat
 heapCost : State C Γ → Nat

/-- Actual initial representation and frame/arena/capacity requirements.
The runtime cursor is read from the SAME supplied machine. -/
structure Entry {C : Contract} {Γ Δ : Ctx} (plan : Emission C Γ Δ)
 (L b frame : Nat) (F : Frag Γ) (caller : State C Γ)
 (base : Nat → Fin W) (machine : Machine) (start : Nat) : Prop where
 represented : StateRepr L b frame F caller base machine
 callerBound : b + Γ.length ≤ plan.localLimit
 resultBound : b + Δ.length ≤ plan.localLimit
 workspace : b + plan.need ≤ plan.localLimit
 pointerAbove : plan.localLimit ≤ plan.pointerCell
 pointerBelow : plan.pointerCell < frame
 payloadAbove : plan.localLimit ≤ start
 reserve : start + plan.arenaWords caller ≤ frame
 controlSpace : Γ.length + 1 ≤ plan.arenaWords caller
 separate : plan.pointerCell < start ∨ start + plan.arenaWords caller ≤ plan.pointerCell
 noWrap : start + plan.arenaWords caller < W
 cursor : machine.mem plan.pointerCell = .val (wmod start)
 capacity : AllocationInput b frame (plan.heapCost caller) caller base machine

/-- At least one represented entry. This does not make `ReturnClaim`
non-vacuous: the plan's state-indexed budgets may admit only callers whose
source run fails, and `PendingRecursiveReturns` may realize only index 0, where
`recBase` exhausts. It does not establish profile coverage or budgets.
`InterfaceV2.SuccessfulEntry` ties the entry to a successful source run. -/
def RealizableEntry {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
 (plan : Emission C Γ Δ) : Prop :=
 ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
   (machine : Machine) (start : Nat), Entry plan L b frame F caller base machine start

/-- Successful target return, including protected OLDER runtime-frame words.
This relation describes a requirement; no inhabitant is supplied here. -/
def Returned {C : Contract} {Γ Δ : Ctx} (plan : Emission C Γ Δ)
 (L b frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
 (machine : Machine) (start : Nat) (out : Solidity.Out C caller.H Δ) : Prop :=
 ∃ target addresses,
 Evm.run plan.code machine = .ok target 0 ∧
 StateRepr L b frame plan.frag out.st addresses target ∧
 target.stack = machine.stack ∧
 BaseExtends caller.H base addresses ∧
 GrowsAllocator b frame (plan.heapCost caller) caller base machine out.st addresses target ∧
 target.mem plan.pointerCell = .val (wmod start) ∧
 Footprint.Words plan.localLimit start machine target

/-- General successful statement transport, as an explicit pending premise. -/
def ReturnClaim {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (s : Stmt C Γ Δ)
 (plan : Emission C Γ Δ) : Prop :=
 ∀ (L frame : Nat) (caller : State C Γ)
   (base : Nat → Fin W) (machine : Machine) (start : Nat),
 Entry plan L b frame F caller base machine start →
 ∀ out : Solidity.Out C caller.H Δ, s.run caller = .ok out →
 Returned plan L b frame caller base machine start out

/-- ONLY bare revert. Payload/panic/exhaustion/divergence are not identified
with this class and require their own genuine producer evidence. -/
def BareRevertClaim {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (s : Stmt C Γ Δ)
 (plan : Emission C Γ Δ) : Prop :=
 ∀ (L frame : Nat) (caller : State C Γ)
   (base : Nat → Fin W) (machine : Machine) (start : Nat),
 Entry plan L b frame F caller base machine start →
 s.run caller = .error .revert → Evm.run plan.code machine = .revert

/-- UNPROVED requirements for a specified ordinary intrinsic call.
Unsupported cases are not admitted merely by declaring this type. -/
structure PendingCallProducer {C : Contract} {Γ Δ ps rs Γf : Ctx}
 (b : Nat) (F : Frag Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Prog C (rs ++ ps) Γf) where
 plan : Emission C Γ Δ
 required_entry : RealizableEntry b F plan
 required_return : ReturnClaim b F (.call f args ret body) plan
 required_bare_revert : BareRevertClaim b F (.call f args ret body) plan

/-- A fixed thunk and its quotation index, exactly as existing callRec.
This is NOT the unbounded recursive-family obligation below. -/
structure PendingFixedCallRecProducer {C : Contract} {Γ Δ ps rs : Ctx}
 (b : Nat) (F : Frag Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) where
 plan : Emission C Γ Δ
 required_entry : RealizableEntry b F plan
 required_return : ∀ d, ReturnClaim b F (.callRec f d args ret body) plan
 required_bare_revert : ∀ d, BareRevertClaim b F (.callRec f d args ret body) plan

/-- One target code image for a whole actual recUnroll family. The natural
index changes only the requested finite observation's capacity/fragment
metadata, not the code. It is not a public admission cutoff. -/
structure RecursiveEmission (C : Contract) (Γ Δ : Ctx) where
 code : List Instr
 frag : Nat → Frag Δ
 need : Nat → Nat
 localLimit : Nat
 pointerCell : Nat
 arenaWords : Nat → State C Γ → Nat
 heapCost : Nat → State C Γ → Nat

def RecursiveEmission.at {C : Contract} {Γ Δ : Ctx}
 (plan : RecursiveEmission C Γ Δ) (n : Nat) : Emission C Γ Δ :=
 ⟨plan.code,plan.frag n,plan.need n,plan.localLimit,plan.pointerCell,
   plan.arenaWords n,plan.heapCost n⟩

/-- Actual existing intrinsic family: no replacement recursion evaluator.
recBase exhaustion and the frontend's existing recDepth remain unchanged. -/
def recursiveSource {C : Contract} {Γ Δ ps rs : Ctx}
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps))
 (n : Nat) : Stmt C Γ Δ :=
 .callRec f n args ret (fun _ => recUnroll (Prog.recBase (C := C) (Γ := rs ++ ps)) step n)

/-- Coherence is a required SOURCE fact, not an assertion about arbitrary
index-dependent builders. It must be proved for the actual family. -/
def RecursiveReturnCoherence {C : Contract} {Γ Δ ps rs : Ctx}
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)) : Prop :=
 ∀ (caller : State C Γ) (n k : Nat) (left right : Solidity.Out C caller.H Δ),
 (recursiveSource f args ret step n).run caller = .ok left →
 (recursiveSource f args ret step k).run caller = .ok right → left = right

/-- UNPROVED all-finite-unroll RETURN requirements with one code image.
This neither treats exhausted as success nor asserts termination/divergence
or a finite-prefix execution theorem. Those remain separate obligations. -/
structure PendingRecursiveReturns {C : Contract} {Γ Δ ps rs : Ctx}
 (b : Nat) (F : Frag Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)) where
 plan : RecursiveEmission C Γ Δ
 required_entry : ∃ n, RealizableEntry b F (plan.at n)
 required_source_coherence : RecursiveReturnCoherence f args ret step
 required_return : ∀ n, ReturnClaim b F (recursiveSource f args ret step n) (plan.at n)
 required_bare_revert : ∀ n, BareRevertClaim b F (recursiveSource f args ret step n) (plan.at n)

/-- A static fragment-side condition, NOT a new admitted-source exclusion.
A real caller/callee producer must establish it for restoration. -/
def NoAliasPromotion {Γ Δ : Ctx} (F : Frag Γ) (G : Frag Δ) (scope : Ext Γ Δ) : Prop :=
 ∀ {R : RefTy} (i : Idx Γ (.alias R)), G.get (i.ext scope) ≠ .dead → F.get i ≠ .dead

/-- UNPROVED full restored-representation statement, with actual source
caller transport, current liveness/flags and post-body machine fields.
No heap-content preservation or rollback is requested from the old state. -/
def RestoredRepresentationClaim : Prop :=
 ∀ {C : Contract} {Γ Δ : Ctx} {L b frame lo pointer start : Nat}
   {F : Frag Γ} {G : Frag Δ} {caller : State C Γ} {afterSource : State C Δ}
   {base addresses : Nat → Fin W} {before after last : Machine}
   (scope : Ext Γ Δ) (growth : caller.H <+: afterSource.H),
 StateRepr L b frame F caller base before →
 StateRepr L b frame G afterSource addresses after →
 TEnv.drop scope afterSource.env = TEnv.wk growth Γ caller.env →
 BaseExtends caller.H base addresses → NoAliasPromotion F G scope →
 b + Δ.length ≤ lo → lo ≤ pointer → pointer < frame → lo ≤ frame →
 Context.Recovered before after last (Restore.contextCells b Γ) lo pointer start →
 StateRepr L b frame G afterSource addresses last

/-- An EXPLICIT premise slot, not an available theorem or producer instance. -/
structure PendingRestoration : Prop where
 required : RestoredRepresentationClaim

end Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1
