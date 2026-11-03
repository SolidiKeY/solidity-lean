import Solidity.Yul.World.PhysicalCallOutput

/-! Explicit equality transport of an existing heap view into a completed
full-carrier call. The equality is structural, never a view-adequacy axiom. -/
namespace Solidity.Yul.World.HeapOutputTransport
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Backend.Environment (writeBytes)

def placement {D} {h k : Source.Heap D} (eq : h=k) (p : Placement h) : Placement k := eq ▸ p

def found {D} {h k : Source.Heap D} (eq : h=k) (e : HeapByteEntry h) :
    k.get e.id=some ⟨heapByteType e.string,heapByteData D e.string e.bytes⟩ := by
  cases eq
  exact e.found

/-- Executes the existing real copyOutput after explicit view transport. -/
def copy {E Γ} (c : Result E Γ) (shared : c.2.effects.execution=c.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset capacity : Word) :=
  copyOutput c shared (placement eq p) e.id e.string e.bytes (found eq e) m offset capacity

/-- Complete expected result: original completion, exact raw write, full source
heap update, both journals and complete ordered observer. -/
def image {E Γ} (c : Result E Γ) (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap)
    (p : Placement h) (e : HeapByteEntry h) (m : ByteView) (offset : Word) (bytes : Bytes) :=
  (c,some ((writeBytes m (p.address e.id+32+offset.val) bytes,
    withSourceHeap c.1.1.1 (c.1.1.1.2.heap.write e.id
      (heapByteData E.layout e.string (HeapWindow.splice e.bytes offset.val bytes))
      (heap_ty_of_get _ e.id _ _ (found eq e)))),(c.1.1.2,c.1.2),c.2))

theorem exact_copy {E Γ} (c : Result E Γ) (shared : c.2.effects.execution=c.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset capacity : Word)
    (inside : offset.val+min capacity.val c.2.effects.returndata.length≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    copy c shared h eq p e m offset capacity=
      image c h eq p e m offset (callOutput c.2.effects.returndata capacity.val) := by
  cases eq
  exact copyOutput_exact c shared p e.id e.string e.bytes e.found m offset capacity inside header reads

abbrev CopyResult (E : Env) (Γ : RCtx) := Result E Γ ×
  Option ((ByteView × EMState E Γ) × (ResidualJournal complementCarrierOwnership × BoolEncodingJournal) ×
    ObservedEffects E.layout E.lay E.lay)

/-- Runtime bind of an actual call result. The selected caller supplies its
proved completed call equation. Outcome-indexing prevents a pending Halt
from being fed into output copying; concrete adapters assume no callee outcome. -/
def sequence {E Γ} (called : Option (Except Halt Roadmap.Outcome × Result E Γ))
    (known : Roadmap.Outcome × Result E Γ) (ran : called=some (.ok known.1,known.2))
    (shared : known.2.2.effects.execution=known.2.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=known.2.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset capacity : Word) : Option (Except Halt Roadmap.Outcome × CopyResult E Γ) :=
  called.pbind fun actual entered=>by
    have same : actual=(Except.ok known.1,known.2) := Option.some.inj (entered.symm.trans ran)
    subst actual
    exact some (Except.ok known.1,copy known.2 shared h eq p e m offset capacity)

theorem sequence_exact {E Γ} (called : Option (Except Halt Roadmap.Outcome × Result E Γ))
    (known : Roadmap.Outcome × Result E Γ) (ran : called=some (.ok known.1,known.2))
    (shared : known.2.2.effects.execution=known.2.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=known.2.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset capacity : Word) :
    sequence called known ran shared h eq p e m offset capacity=
      some (Except.ok known.1,copy known.2 shared h eq p e m offset capacity) := by
  cases ran
  rfl

/-- The same explicit transport for strict RETURNDATACOPY. -/
def window {E Γ} (c : Result E Γ) (shared : c.2.effects.execution=c.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset source size : Word) :=
  copyAfter c shared (placement eq p) e.id e.string e.bytes (found eq e) m offset source size

theorem window_exact {E Γ} (c : Result E Γ) (shared : c.2.effects.execution=c.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset source size : Word) (bytes : Bytes)
    (sourceWindow : returnWindow c.2.effects.returndata source.val size.val=some bytes)
    (inside : offset.val+bytes.length≤e.bytes.length)
    (header : (mload m (p.address e.id)).val=e.bytes.length)
    (reads : readBytes m (p.address e.id+32) e.bytes.length=e.bytes) :
    window c shared h eq p e m offset source size=image c h eq p e m offset bytes := by
  cases eq
  exact congrArg (fun x=>(c,x)) (HeapWindow.copyCoupledWindow_exact c.2 c.1.1.1 p e.id e.string e.bytes bytes e.found
    c.1.1.2 c.1.2 shared m offset source size sourceWindow inside header reads)

theorem window_bad_source {E Γ} (c : Result E Γ) (shared : c.2.effects.execution=c.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset source size : Word) (bad : c.2.effects.returndata.length<source.val+size.val) :
    window c shared h eq p e m offset source size=(c,none) := by
  cases eq
  exact copyAfter_bad_source c shared p e.id e.string e.bytes e.found m offset source size bad

def sequenceWindow {E Γ} (called : Option (Except Halt Roadmap.Outcome × Result E Γ))
    (known : Roadmap.Outcome × Result E Γ) (ran : called=some (.ok known.1,known.2))
    (shared : known.2.2.effects.execution=known.2.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=known.2.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset source size : Word) : Option (Except Halt Roadmap.Outcome × CopyResult E Γ) :=
  called.pbind fun actual entered=>by
    have same : actual=(Except.ok known.1,known.2) := Option.some.inj (entered.symm.trans ran)
    subst actual
    exact some (Except.ok known.1,window known.2 shared h eq p e m offset source size)

theorem sequenceWindow_exact {E Γ} (called : Option (Except Halt Roadmap.Outcome × Result E Γ))
    (known : Roadmap.Outcome × Result E Γ) (ran : called=some (.ok known.1,known.2))
    (shared : known.2.2.effects.execution=known.2.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=known.2.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset source size : Word) :
    sequenceWindow called known ran shared h eq p e m offset source size=
      some (Except.ok known.1,window known.2 shared h eq p e m offset source size) := by
  cases ran
  rfl

theorem destination_refused {E Γ} (c : Result E Γ) (shared : c.2.effects.execution=c.1.1.1.2.ex)
    (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap) (p : Placement h) (e : HeapByteEntry h)
    (m : ByteView) (offset capacity : Word)
    (outside : ¬offset.val+min capacity.val c.2.effects.returndata.length≤e.bytes.length) :
    copy c shared h eq p e m offset capacity=(c,none) := by
  cases eq
  exact copyOutput_refusal c shared p e.id e.string e.bytes e.found m offset capacity outside

/-- Full preservation of every non-heap Source field and both physical banks;
this is in addition to exact whole-result equality, not its replacement. -/
theorem image_frame {E Γ} (c : Result E Γ) (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap)
    (p : Placement h) (e : HeapByteEntry h) (m : ByteView) (offset : Word) (bytes : Bytes) :
    ∃ m' s', image c h eq p e m offset bytes=(c,some ((m',s'),(c.1.1.2,c.1.2),c.2)) ∧
      s'.1=c.1.1.1.1 ∧ s'.2.ex=c.1.1.1.2.ex ∧ s'.2.events=c.1.1.1.2.events ∧
      s'.2.logs=c.1.1.1.2.logs ∧ s'.2.fnLocals=c.1.1.1.2.fnLocals ∧
      s'.2.heap.ty=c.1.1.1.2.heap.ty ∧ s'.2.heap.next=c.1.1.1.2.heap.next := by
  refine ⟨_,_,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl⟩
  funext b
  exact Source.Heap.write_ty c.1.1.1.2.heap e.id b
    (heapByteData E.layout e.string (HeapWindow.splice e.bytes offset.val bytes))
    (heap_ty_of_get _ e.id _ _ (found eq e))

theorem image_memOK {E Γ} (c : Result E Γ) (h : Source.Heap E.layout) (eq : h=c.1.1.1.2.heap)
    (p : Placement h) (e : HeapByteEntry h) (m : ByteView) (offset : Word) (bytes : Bytes)
    (H : Source.HeapTy) (ok : Source.MemOK E H c.1.1.1) :
    ∃ m' s', image c h eq p e m offset bytes=(c,some ((m',s'),(c.1.1.2,c.1.2),c.2)) ∧ Source.MemOK E H s' := by
  exact ⟨_,_,rfl,heapByte_write_MemOK E H c.1.1.1 e.id e.string
    (HeapWindow.splice e.bytes offset.val bytes) (heap_ty_of_get _ e.id _ _ (found eq e)) ok⟩
end Solidity.Yul.World.HeapOutputTransport
