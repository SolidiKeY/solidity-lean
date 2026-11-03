import Solidity.Yul.World.GeneralReturningStatic

namespace Solidity.Yul.World.GeneralReturning
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (env output)
open Solidity.Backend.Environment (writeBytes)

/-- Output header/payload premises are derived from the ACTUAL VY2 encoder,
not an input-view assumption unrelated to the caller's heap. -/
theorem output_encoded {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (es : List (HeapByteEntry s.2.heap)) (distinct : (es.map HeapByteEntry.id).Nodup)
    (e : HeapByteEntry s.2.heap) (member : e ∈ es) (background : ByteView)
    (offset capacity : Word) (inside : offset.val+min capacity.val output.length≤e.bytes.length) :
    copyOutput (successResult s next r b o) rfl p e.id e.string e.bytes e.found (encodeByteHeap p es background) offset capacity=
      (successResult s next r b o,some
        ((writeBytes (encodeByteHeap p es background) (p.address e.id+32+offset.val) (callOutput output capacity.val),
          withSourceHeap (after s next) (s.2.heap.write e.id
            (heapByteData env.layout e.string (HeapWindow.splice e.bytes offset.val (callOutput output capacity.val)))
            (heap_ty_of_get _ e.id _ _ e.found))),(r,b),(successResult s next r b o).2)) :=
  copy_output s next r b o p e.id e.string e.bytes e.found _ offset capacity inside
    (encodeByteHeap_reads p es distinct background e member).1 (encodeByteHeap_reads p es distinct background e member).2

/-- Concrete mini-composition: the actual source call and bounded output
write use the SAME caller heap encoding and SAME complete returned carrier.
This avoids treating an arbitrary configured result as source reachability. -/
theorem call_then_output_encoded (G : Glob env) {Γ} (s : EMState env Γ)
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (shared : o.effects.execution=s.2.ex)
    (p : Placement s.2.heap) (es : List (HeapByteEntry s.2.heap)) (distinct : (es.map HeapByteEntry.id).Nodup)
    (incoming outgoing : HeapByteEntry s.2.heap) (inputMember : incoming ∈ es) (outputMember : outgoing ∈ es)
    (inputBytes : incoming.bytes=ReturningCall.input G) (background : ByteView) (gas offset capacity : Word)
    (inside : offset.val+min capacity.val output.length≤outgoing.bytes.length) :
    call (CallerFrame.liftInvoke (ReturningCall.invoke G)) s r b o shared (encodeByteHeap p es background)
      (ReturningCall.parent s) .call CallerFrameChecks.receiver gas 7
      (PhysicalHeapPort.payloadOffset s.2.heap p incoming.id incoming.string incoming.bytes incoming.found)
      ⟨incoming.bytes.length,heapByte_length_bound s.2.heap p incoming.id incoming.string incoming.bytes incoming.found⟩=
      some (.ok (.success output),successResult s next r b o) ∧
    copyOutput (successResult s next r b o) rfl p outgoing.id outgoing.string outgoing.bytes outgoing.found
      (encodeByteHeap p es background) offset capacity=
      (successResult s next r b o,some
        ((writeBytes (encodeByteHeap p es background) (p.address outgoing.id+32+offset.val) (callOutput output capacity.val),
          withSourceHeap (after s next) (s.2.heap.write outgoing.id
            (heapByteData env.layout outgoing.string (HeapWindow.splice outgoing.bytes offset.val (callOutput output capacity.val)))
            (heap_ty_of_get _ outgoing.id _ _ outgoing.found))),(r,b),(successResult s next r b o).2)) :=
  ⟨call_encoded G s next code transfer r b o shared p es distinct incoming inputMember inputBytes background gas,
    output_encoded s next r b o p es distinct outgoing outputMember background offset capacity inside⟩

/-- Full typed neighboring images are framed by the actual partial write. -/
theorem output_other_image {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (a other : Nat) (string : Bool) (old : Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData env.layout string old⟩)
    (m : ByteView) (offset capacity : Word) (inside : offset.val+min capacity.val output.length≤old.length)
    (header : (mload m (p.address a)).val=old.length) (payload : readBytes m (p.address a+32) old.length=old)
    {τ : STy} {d : Data env.layout τ} (image : MemoryImage p d)
    (otherFound : s.2.heap.get other=some ⟨τ,d⟩) (different : other≠a)
    (reads : image.Reads m (p.address other)) :
    image.Reads (writeBytes m (p.address a+32+offset.val) (callOutput output capacity.val)) (p.address other) := by
  have extent : offset.val+(callOutput output capacity.val).length≤old.length := by
    simpa only [callOutput_length] using inside
  have window := output_window (successResult s next r b o) capacity
  have copied := HeapWindow.copyHeapWindow_exact (successResult s next r b o).2.effects s.2.heap p a string old
    (callOutput output capacity.val) found m offset 0 (outputCount (successResult s next r b o) capacity) window extent header payload
  exact HeapWindow.window_other_image (successResult s next r b o).2.effects s.2.heap p a other string old
    (callOutput output capacity.val) found m offset 0 (outputCount (successResult s next r b o) capacity)
    window extent header payload _ _ copied image otherFound different reads

/-- Strict RETURNDATACOPY still rejects an invalid zero-length source window
AFTER the actual full-buffer completion. It never silently truncates the source. -/
theorem invalid_zero {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes) (found) (m : ByteView) (offset : Word) :
    copyAfter (successResult s next r b o) rfl p a string old found m offset 33 0=
      (successResult s next r b o,none) :=
  copyAfter_bad_source _ rfl _ a string old found _ offset 33 0 (by change output.length<33+0; rw [ReturningCall.output_length]; decide)

/-- Exact end of the NEW full return buffer is a valid zero copy, including
at the selected destination's end. Invalid source33/size0 remains refused. -/
theorem end_zero {Γ} (s : EMState env Γ) (next : ExecState env.layout env.lay env.lay)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes) (found) (m : ByteView) (offset : Word)
    (inside : offset.val≤old.length)
    (header : (mload m (p.address a)).val=old.length) (payload : readBytes m (p.address a+32) old.length=old) :
    copyAfter (successResult s next r b o) rfl p a string old found m offset 32 0=
      (successResult s next r b o,some ((m,after s next),(r,b),(successResult s next r b o).2)) := by
  have zero := HeapWindow.copyHeapWindow_zero (successResult s next r b o).2.effects s.2.heap p a string old found m offset 32
    (by change 32≤output.length; rw [ReturningCall.output_length]; exact Nat.le_refl _) inside header payload
  unfold copyAfter HeapWindow.copyCoupledWindow
  rw [HeapWindow.copyStateWindow_heap]
  simp only [successResult,after] at zero ⊢
  rw [zero]
  simp only [Option.map_some,withSourceHeap_unchanged] <;> rfl

/-- A refused call has an empty NEW return buffer. Its bounded caller output
write is an actual no-op, with completion and all full carriers retained. -/
theorem refused_output {Γ} (s : EMState env Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects env.layout env.lay env.lay) (p : Placement s.2.heap)
    (a : Nat) (string : Bool) (old : Bytes) (found) (m : ByteView) (offset capacity : Word)
    (inside : offset.val≤old.length)
    (header : (mload m (p.address a)).val=old.length) (payload : readBytes m (p.address a+32) old.length=old) :
    copyOutput (refusedResult s r b o) rfl p a string old found m offset capacity=
      (refusedResult s r b o,some ((m,s),(r,b),(refusedResult s r b o).2)) := by
  have zero := HeapWindow.copyHeapWindow_zero (refusedResult s r b o).2.effects s.2.heap p a string old found m offset 0
    (by exact Nat.zero_le _) inside header payload
  have count : outputCount (refusedResult s r b o) capacity=0 := by
    apply Fin.ext
    simp only [outputCount,refusedResult,List.length_nil,Nat.min_zero]
    rfl
  unfold copyOutput HeapWindow.copyCoupledWindow
  rw [count,HeapWindow.copyStateWindow_heap]
  simp only [refusedResult] at zero ⊢
  rw [zero]
  simp only [Option.map_some,withSourceHeap_unchanged]

end Solidity.Yul.World.GeneralReturning
