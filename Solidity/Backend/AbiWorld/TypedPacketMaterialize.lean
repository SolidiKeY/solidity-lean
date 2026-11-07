import Solidity.Backend.MemoryOps.PhysicalByteStackExact
import Solidity.Backend.AbiWorld.LibraryResultPacket

/-! Typed codec packets through the existing literal byte materializer. These
are supplied indexed Vals, not reads from unknown runtime memory. Nonempty
packets have the exact transient stack guard; disjoint numeric frames survive. -/
namespace Solidity.Backend.AbiWorld.TypedPacketMaterialize
open Solidity.Backend
open MemoryOps.Physical

theorem execute {shapes : List AbiEntry.Shape} (values : AbiEntry.Vals shapes)
 (nonempty : AbiEntry.encodeArgs values≠[]) (m : Evm.Machine) (memory : Environment.Memory)
 (live : Nat → Prop) (initial : WordFrame m memory live) (frame : Environment.Frame)
 (a n : Roadmap.Word) (tail : List Roadmap.Word) (envTail : List Environment.Word)
 (suffix : Program) (size : n.val=(AbiEntry.encodeArgs values).length)
 (fits : a.val+(AbiEntry.encodeArgs values).length≤2^256)
 (separate : ∀ c,live c → a.val+(AbiEntry.encodeArgs values).length≤32*c ∨ 32*c+32≤a.val) :
 let packet := AbiEntry.encodeArgs values
 Environment.runSlice frame (Environment.materialize a.val packet) ⟨envTail,memory⟩=
  some ⟨envTail,Environment.writeBytes memory a.val packet⟩ ∧
 Failure.Slice.checkedRun (Environment.materialize a.val packet++(.op .REVERT::suffix)) ⟨a::n::tail,memory⟩=
  (if tail.length+4≤1024 then some (⟨tail,Environment.writeBytes memory a.val packet⟩,some (.revert packet)) else none) ∧
 WordFrame m (Environment.writeBytes memory a.val packet) live ∧
 (∀ j,j<a.val ∨ a.val+packet.length≤j → Environment.writeBytes memory a.val packet j=memory j) := by
 first | (solve | rfl) | (solve | simp only []) | (solve | omega) | skip
 have actual := initial.materialize_revert frame a n (AbiEntry.encodeArgs values) tail envTail suffix size fits separate
 refine ⟨actual.1,?_,actual.2.2⟩
 generalize eq : AbiEntry.encodeArgs values=packet at *
 cases packet with
 | nil => exact (nonempty rfl).elim
 | cons b bs => exact materialize_checked_revert_exact b bs a n tail memory suffix size fits
end Solidity.Backend.AbiWorld.TypedPacketMaterialize
