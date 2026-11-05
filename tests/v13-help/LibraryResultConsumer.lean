import Solidity.Backend.AbiWorld.LibraryResultPacket
import Solidity.Examples.Tactics.LibraryTrySource
import Solidity.Backend.AbiWorld.ErrorReadWindowControls

/-! Lane-local application above the frontend: never imported into the core. -/
namespace Solidity.Tests.AbiWorld.LibraryResultConsumer
open Solidity Semantics
open Backend.AbiWorld.LibraryResultPacket
open Examples.Tactics.LibraryTrySource

def packet (n : Fin AbiEntry.W) (message : List UInt8) : List UInt8 :=
  AbiEntry.encodeArgs (values n message)
def failure : List UInt8 := [102,97,105,108,117,114,101]

theorem expected_transport (n : Fin AbiEntry.W) (bs : List UInt8) :
    expected n.val bs = (packet n bs).map UInt8.toNat := by
  simp only [expected,packet,encoded_values]

theorem ordered_typed : ordered.toOption = some
    ((packet ⟨8,by decide⟩ []).map UInt8.toNat,
     (packet ⟨18,by decide⟩ failure).map UInt8.toNat,
     (packet ⟨9,by decide⟩ []).map UInt8.toNat,
     (packet ⟨19,by decide⟩ failure).map UInt8.toNat) := by
  have h := original_outputs
  change ordered.toOption = some (expected 8 [],expected 18 failure,expected 9 [],expected 19 failure) at h
  rw [expected_transport ⟨8,by decide⟩ [],expected_transport ⟨18,by decide⟩ failure,
    expected_transport ⟨9,by decide⟩ [],expected_transport ⟨19,by decide⟩ failure] at h
  exact h

theorem ordinary_typed : orderedOrdinary.toOption = some
    ((packet ⟨8,by decide⟩ []).map UInt8.toNat,
     (packet ⟨18,by decide⟩ failure).map UInt8.toNat,
     (packet ⟨9,by decide⟩ []).map UInt8.toNat,
     (packet ⟨19,by decide⟩ failure).map UInt8.toNat) := by
  rw [ordinary_execution]
  exact ordered_typed

/-- The producer's separately observed same ordered storage program, unchanged. -/
theorem prefix_storage : storageEffects.toOption = some (0,0,9,9) := actual_prefix_storage

def packets : List (List UInt8) :=
  [packet ⟨8,by decide⟩ [],packet ⟨18,by decide⟩ failure,
   packet ⟨9,by decide⟩ [],packet ⟨19,by decide⟩ failure]
def boundaries : List (List UInt8) :=
  [packet ⟨300,by decide⟩ [0,255,128],packet ⟨2^256-1,by decide⟩ [],
   packet ⟨0,by decide⟩ (List.replicate 31 0),
   packet ⟨0,by decide⟩ (List.replicate 32 255),
   packet ⟨0,by decide⟩ (List.replicate 33 128)]

theorem offsets : (packets++boundaries).all (fun bs => decide (bytesNat ((bs.drop 32).take 32) = 64)) = true := by decide

theorem wrong_offset : ((packet ⟨18,by decide⟩ failure).drop 32).take 32 ≠ wordBytes 32 := by decide

theorem wrong_marker : (packet ⟨300,by decide⟩ [0,255,128]).take 32 ≠ wordBytes 44 := by decide

theorem wrong_payload : ((packet ⟨18,by decide⟩ failure).drop 96).take failure.length ≠ failure.reverse := by decide

theorem wrong_order : packet ⟨18,by decide⟩ failure ≠
    wordBytes 64 ++ wordBytes 18 ++ wordBytes failure.length ++ pad32 failure := by decide

theorem truncated_differs : (packet ⟨18,by decide⟩ failure).take 102 ≠ packet ⟨18,by decide⟩ failure := by decide
end Solidity.Tests.AbiWorld.LibraryResultConsumer
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.expected_transport
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.ordered_typed
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.ordinary_typed
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.prefix_storage
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.offsets
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.wrong_offset
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.wrong_marker
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.wrong_payload
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.wrong_order
#print axioms Solidity.Tests.AbiWorld.LibraryResultConsumer.truncated_differs
#check Solidity.Tests.AbiWorld.LibraryResultConsumer.ordered_typed
#eval IO.println ("LIBRARY_TYPED_PACKETS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets Solidity.Tests.AbiWorld.LibraryResultConsumer.packets)
#eval IO.println ("LIBRARY_BOUNDARY_PACKETS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets Solidity.Tests.AbiWorld.LibraryResultConsumer.boundaries)
#eval IO.println ("LIBRARY_PUBLISHED_EXPECTED=" ++ "[" ++ String.intercalate "," ([Solidity.Examples.Tactics.LibraryTrySource.expected 8 [],Solidity.Examples.Tactics.LibraryTrySource.expected 18 Solidity.Tests.AbiWorld.LibraryResultConsumer.failure,Solidity.Examples.Tactics.LibraryTrySource.expected 9 [],Solidity.Examples.Tactics.LibraryTrySource.expected 19 Solidity.Tests.AbiWorld.LibraryResultConsumer.failure].map (fun bs => "[" ++ String.intercalate "," (bs.map toString) ++ "]")) ++ "]")
