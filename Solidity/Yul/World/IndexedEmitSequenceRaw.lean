import Solidity.Yul.World.IndexedEmitSequence

namespace Solidity.Yul.World.IndexedEmitSequenceRaw
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Roadmap (Word)
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.IndexedEmitPort
open Solidity.Yul.World.ScalarEmitPort (env)

def raw {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (m : ByteView) (offset size nextOffset nextSize : Word) := do
  let first←logAdapter PhysicalHeapPort.port o m false (encoding G l i).emitter
    (encoding G l i).count (encoding G l i).topics offset size
  pure (first,logAdapter PhysicalHeapPort.port first m false (encoding G l j).emitter
    (encoding G l j).count (encoding G l j).topics nextOffset nextSize)

/-- Complete ordered observation agreement for actual matching raw windows.
The byte/range premises are real physical input relations, not arbitrary-heap
adequacy; the Source side selects the actual caller's intrinsic local indices. -/
theorem agreement {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (m : ByteView) (offset size nextOffset nextSize : Word)
    (range : offset.val+size.val≤2^256) (nextRange : nextOffset.val+nextSize.val≤2^256)
    (bytes : readBytes m offset.val size.val=(encoding G s.1 i).data)
    (nextBytes : readBytes m nextOffset.val nextSize.val=(encoding G s.1 j).data) :
    raw G s.1 i j o m offset size nextOffset nextSize=
      some (emitObserved o (encoding G s.1 i),some (IndexedEmitSequence.twice G s i j r b o shared).2) := by
  unfold raw
  rw [IndexedEmitMemory.raw_matched G s.1 i o m offset size range bytes]
  simp only [bind,Option.bind_some]
  rw [IndexedEmitMemory.raw_matched G s.1 j _ m nextOffset nextSize nextRange nextBytes,
    IndexedEmitSequence.twice_exact]
  rfl

/-- A failed physical input window refuses the adapter; this Option result is
not identified with an EVM exceptional halt or a completed Source revert. -/
theorem refused {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (m : ByteView) (offset size nextOffset nextSize : Word)
    (missing : PhysicalHeapPort.port.load m offset size=none) :
    raw G l i j o m offset size nextOffset nextSize=none := by
  simp only [raw,logAdapter,Bool.false_eq_true,if_false,missing,bind,Option.bind_none]

/-- First completed observation survives refusal of the second input window. -/
theorem second_refused {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (m : ByteView) (offset size nextOffset nextSize : Word)
    (range : offset.val+size.val≤2^256)
    (bytes : readBytes m offset.val size.val=(encoding G l i).data)
    (missing : PhysicalHeapPort.port.load m nextOffset nextSize=none) :
    raw G l i j o m offset size nextOffset nextSize=some (emitObserved o (encoding G l i),none) := by
  unfold raw
  rw [IndexedEmitMemory.raw_matched G l i o m offset size range bytes]
  simp only [bind,Option.bind_some,logAdapter,Bool.false_eq_true,if_false,missing,Option.bind_none,pure]

/-- Inhabited actual matching view used twice; arbitrary distinct-value windows
remain governed by agreement's explicit actual-byte relations. -/
theorem repeated_view {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (s : EMState (env indexed anonymous) Γ) (i : Source.Idx Γ ReturningCall.uint)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    raw G s.1 i i o (IndexedEmitMemory.memory G s.1 i) 160 (IndexedEmitMemory.size G s.1 i)
      160 (IndexedEmitMemory.size G s.1 i)=some (emitObserved o (encoding G s.1 i),
        some (IndexedEmitSequence.twice G s i i r b o shared).2) := by
  have bound:=IndexedEmitMemory.data_bound G s.1 i
  have range : (160 : Word).val+(IndexedEmitMemory.size G s.1 i).val≤2^256 := by
    change 160+(encoding G s.1 i).data.length≤2^256
    omega
  have loaded:=IndexedEmitMemory.loaded G s.1 i
  rw [PhysicalHeapPort.load_view _ _ _ range] at loaded
  have bytes:=Option.some.inj loaded
  exact agreement G s i i r b o shared _ _ _ _ _ range range bytes bytes

def badOffset : Word := ⟨2^256-1,by decide⟩

theorem bad_load (m : ByteView) : PhysicalHeapPort.port.load m badOffset 2=none := by
  change (if badOffset.val+(2 : Word).val≤2^256 then some (Solidity.Backend.Environment.readMemory m badOffset.val (2 : Word).val) else none)=none
  exact if_neg (by decide)

theorem witnessed_second_refusal {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i j : Source.Idx Γ ReturningCall.uint)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay) :
    raw G l i j o (IndexedEmitMemory.memory G l i) 160 (IndexedEmitMemory.size G l i) badOffset 2=
      some (emitObserved o (encoding G l i),none) := by
  have bound:=IndexedEmitMemory.data_bound G l i
  have range : (160 : Word).val+(IndexedEmitMemory.size G l i).val≤2^256 := by
    change 160+(encoding G l i).data.length≤2^256
    omega
  have loaded:=IndexedEmitMemory.loaded G l i
  rw [PhysicalHeapPort.load_view _ _ _ range] at loaded
  exact second_refused G l i j o _ _ _ _ _ range (Option.some.inj loaded) (bad_load _)
end Solidity.Yul.World.IndexedEmitSequenceRaw
