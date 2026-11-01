import Solidity.Backend.AbiWorld.MixedPacket
import tests.«v13-abi-world».CallerPacketControls
import tests.«v13-abi-world».MixedCodecControls
namespace Solidity.Backend.AbiWorld.MixedPacketControls
open Evm Evm.Memory InternalFlow
open InternalFlow.MemoryDispatchChecks
open InternalFlow.MemoryDispatchChecks.ProtectedTail

def markerIndex : Idx View (.val .uint) :=
  .there (.there (.there (.there (.there (.there .here)))))

theorem entry_marker : TEnv.get (markerIndex.wk projection) mid.st.env = indexValue (wmod 42) := by
  apply Subtype.ext
  decide +kernel

theorem reached_marker : TEnv.get (markerIndex.wk projection) chosen.st.env = indexValue (wmod 42) := by
  have keep := congrArg (TEnv.get markerIndex) complete_caller_frame
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin] at keep
  change TEnv.get (markerIndex.wk projection) chosen.st.env =
    TEnv.get (markerIndex.wk projection) mid.st.env at keep
  exact keep.trans entry_marker

theorem encoded_current : AbiEntry.encodeArgs (MixedPacket.values
    (chosen.st.heap.get (old.wk chosen.ext)).1 (TEnv.get (markerIndex.wk projection) mid.st.env)) =
      packet := by
  rw [MixedPacket.encoded_values,CallerPacketControls.current_words,entry_marker]
  decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.entry_marker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_marker
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.reached_marker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_marker
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.encoded_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_current
end Solidity.Backend.AbiWorld.MixedPacketControls
