import Solidity.Source.FailureResources

/-!
# Typed failure-execution cursor (H16 interface checkpoint)

The semantic resource is the existing `FailureResources.Bound`. Request and
frame ordinals are distinct Fin-indexed namespaces, bounded by counts of
entries already issued/started. Frame budgets count the observable subtrace
while active, including nested events; request budgets count body events,
not the terminal receipt. Pending request failure has priority over frames;
otherwise the oldest active failing frame owns the unwind.

These are executable cursor operations only. Machine/Eval/Session hooks are
not installed by this interface module, and no failure-aware language or P8a
Producer inhabitant is claimed here. Logical rollback must retain the cursor;
leaving a frame pops its live budget rather than restoring a stale snapshot.
-/
namespace Solidity.Source.FailureExecution
open Solidity.Roadmap.Evm

abbrev Resource := FailureResources.Bound

/-- Immutable evaluator input: existing calls default to None; a failure-aware
session supplies Some resource.points throughout its actual recursive calls.
This is a configuration type, not an interpreter or a SourceSpec instance. -/
abbrev RuntimePlan := Option FailurePoints

def RuntimePlan.ofResource (resource : Resource) : RuntimePlan := some resource.points

structure RequestBudget (issued : Nat) where
  ordinal : Fin issued
  senderBalance : Nat
  cut : Option Nat
  emitted : Nat := 0
  deriving Repr

structure FrameBudget (started : Nat) where
  ordinal : Fin started
  cut : Option Nat
  emitted : Nat := 0
  deriving Repr

/-- The kind is retained even when request/frame ordinals have equal values. -/
inductive Stop (requests frames : Nat) where
  | request (ordinal : Fin requests)
  | frame (ordinal : Fin frames)
  deriving Repr

def FrameBudget.grow {n : Nat} (b : FrameBudget n) : FrameBudget (n+1) :=
  ⟨b.ordinal.castSucc,b.cut,b.emitted⟩

def Stop.growFrame {r f : Nat} : Stop r f → Stop r (f+1)
  | .request i => .request i
  | .frame i => .frame i.castSucc

def Stop.growRequest {r f : Nat} : Stop r f → Stop (r+1) f
  | .request i => .request i.castSucc
  | .frame i => .frame i

def Stop.isRequest {r f : Nat} (s : Stop r f) (i : Nat) : Bool :=
  match s with | .request j => j.val == i | .frame _ => false

def Stop.isFrame {r f : Nat} (s : Stop r f) (i : Nat) : Bool :=
  match s with | .request _ => false | .frame j => j.val == i


structure Cursor where
  nextRequest : Nat
  nextFrame : Nat
  request : Option (RequestBudget nextRequest)
  /-- Innermost frame first. -/
  frames : List (FrameBudget nextFrame)
  pending : Option (Stop nextRequest nextFrame)
  deriving Repr

def Cursor.empty : Cursor := ⟨0,0,none,[],none⟩

def Cursor.quiescent (c : Cursor) : Bool :=
  c.request.isNone && c.frames.isEmpty && c.pending.isNone

def cutReached (cut : Option Nat) (emitted : Nat) : Bool :=
  match cut with
  | none => false
  | some k => decide (k ≤ emitted)

/-- Consume a request ordinal even when the request is dropped. Session entry
must be quiescent; this operation does not finalize a transaction or run code. -/
def Cursor.enterRequest (plan : FailurePoints) (c : Cursor)
    (_ : c.quiescent = true) : TxFate × Cursor :=
  let fate := plan.tx c.nextRequest
  let budget := match fate with
    | .dropped => none
    | .runs balance cut => some (RequestBudget.mk (Fin.last c.nextRequest) balance cut 0)
  (fate,⟨c.nextRequest+1,c.nextFrame,budget,c.frames,c.pending.map Stop.growRequest⟩)

/-- Called at actual compiled-system frame entry, after pre-entry refusal
checks. Internal function calls and environment code do not consume this ID. -/
def Cursor.enterFrame (plan : FailurePoints) (c : Cursor) : Cursor :=
  ⟨c.nextRequest,c.nextFrame+1,c.request,
    ⟨Fin.last c.nextFrame,plan.frame c.nextFrame,0⟩ :: c.frames.map FrameBudget.grow,
    c.pending.map Stop.growFrame⟩

/-- Leave only the current frame. A stop for an outer owner or the request
must survive; equal numeric request/frame IDs do not authorize consumption. -/
def Cursor.leaveFrame (c : Cursor) : Cursor :=
  let pending := match c.frames, c.pending with
    | frame :: _, some stop => if stop.isFrame frame.ordinal.val then none else c.pending
    | _, _ => c.pending
  { c with frames := c.frames.tail, pending := pending }

def Cursor.leaveRequest (c : Cursor) : Cursor :=
  let pending := match c.request, c.pending with
    | some request, some stop => if stop.isRequest request.ordinal.val then none else c.pending
    | _, _ => c.pending
  { c with request := none, pending := pending }

/-- Check zero cuts on entry as well as cuts reached after an emitted event.
A pending stop cannot be overwritten by a nested handler or a later event. -/
def Cursor.stop? (c : Cursor) : Option (Stop c.nextRequest c.nextFrame) :=
  c.pending.orElse fun _ =>
    match c.request with
    | some b => if cutReached b.cut b.emitted then some (.request b.ordinal)
      else (c.frames.reverse.find? fun f => cutReached f.cut f.emitted).map fun f => .frame f.ordinal
    | none => (c.frames.reverse.find? fun f => cutReached f.cut f.emitted).map fun f => .frame f.ordinal

/-- Advance only active budgets. Call before terminal receipt emission only
while a request/frame is active; no Source event is manufactured here. -/
def Cursor.advanceEvent (c : Cursor) : Cursor :=
  match c.stop? with
  | some stop => { c with pending := some stop }
  | none =>
    let advanced : Cursor := { c with
      request := c.request.map (fun (b : RequestBudget c.nextRequest) => { b with emitted := b.emitted+1 })
      frames := c.frames.map (fun (b : FrameBudget c.nextFrame) => { b with emitted := b.emitted+1 }) }
    { advanced with pending := advanced.stop? }


end Solidity.Source.FailureExecution
