import Solidity.Yul.World.Adapters
import Solidity.Backend.Environment.ByteConstants

/-! Concrete consumer instance for the existing target byte-memory functions.
This reuses their implementation, not a second memory semantics. A VY2 source
view adapter and layout/ownership/writeback agreement are still required.
-/
namespace Solidity.Yul.World.TargetMemory
open Solidity.Roadmap (Word Bytes)
open Solidity.Source
open Solidity.Backend.Environment (Memory readMemory writeBytes)

/-- Word-indexed, nonwrapping windows; no gas/resource adequacy is inferred. -/
def port : BytePort Memory where
  acceptOutput _ offset size := decide (offset.val + size.val ≤ 2^256)
  load memory offset size :=
    if offset.val + size.val ≤ 2^256 then some (readMemory memory offset.val size.val) else none
  store memory offset bytes :=
    if offset.val + bytes.length ≤ 2^256 then some (writeBytes memory offset.val bytes) else none

theorem load_exact (memory : Memory) (offset size : Word)
    (h : offset.val + size.val ≤ 2^256) :
    port.load memory offset size = some (readMemory memory offset.val size.val) := by
  simp only [port, h, ↓reduceIte]

theorem store_exact (memory : Memory) (offset : Word) (bytes : Bytes)
    (h : offset.val + bytes.length ≤ 2^256) :
    port.store memory offset bytes = some (writeBytes memory offset.val bytes) := by
  simp only [port, h, ↓reduceIte]

/-- Now an actual memory readback, using the existing implementation's theorem. -/
theorem copy_readback {D : Solidity.Source.Layout} {L T : Solidity.Roadmap.Address → Solidity.Source.SPath → Solidity.Source.STy}
    (entry : Effects D L T) (memory : Memory) (destination source size : Word) (bytes : Bytes)
    (hs : returnWindow entry.returndata source.val size.val = some bytes)
    (hd : destination.val + bytes.length ≤ 2^256) :
    (copyReturndata port entry memory destination source size).map
      (fun after => readMemory after destination.val bytes.length) = some bytes := by
  rw [copyReturndata_exact _ _ _ _ _ _ _ hs, store_exact _ _ _ hd]
  simp only [Option.map_some, Solidity.Backend.Environment.read_written]

/-- Outside the actually copied bytes, the existing memory really is unchanged. -/
theorem copy_frame {D : Solidity.Source.Layout} {L T : Solidity.Roadmap.Address → Solidity.Source.SPath → Solidity.Source.STy}
    (entry : Effects D L T) (memory : Memory) (destination source size : Word) (bytes : Bytes) (i : Nat)
    (hs : returnWindow entry.returndata source.val size.val = some bytes)
    (hd : destination.val + bytes.length ≤ 2^256)
    (outside : i < destination.val ∨ destination.val + bytes.length ≤ i) :
    (copyReturndata port entry memory destination source size).map (fun after => after i) = some (memory i) := by
  rw [copyReturndata_exact _ _ _ _ _ _ _ hs, store_exact _ _ _ hd]
  simp only [Option.map_some, Solidity.Backend.Environment.writeBytes_frame _ _ _ _ outside]

/-- A call output is bounded by the actual returned bytes, not its capacity. -/
theorem output_frame (memory : Memory) (destination : Word) (data : Bytes) (capacity i : Nat)
    (hd : destination.val + (callOutput data capacity).length ≤ 2^256)
    (outside : i < destination.val ∨ destination.val + min capacity data.length ≤ i) :
    (port.store memory destination (callOutput data capacity)).map (fun after => after i) = some (memory i) := by
  rw [store_exact _ _ _ hd]
  simp only [Option.map_some]
  apply congrArg some
  apply Solidity.Backend.Environment.writeBytes_frame
  simpa only [callOutput_length] using outside

/-- This concrete port discharges its output-write existence obligation from
acceptance of the entire requested window, even if only a shorter prefix is
returned. Generic BytePort instances do not get this law by assumption. -/
theorem accepted_output_store (memory : Memory) (destination capacity : Word) (data : Bytes)
    (h : port.acceptOutput memory destination capacity = true) :
    port.store memory destination (callOutput data capacity.val) =
      some (writeBytes memory destination.val (callOutput data capacity.val)) := by
  have hb : destination.val + capacity.val ≤ 2^256 := of_decide_eq_true h
  have hl : (callOutput data capacity.val).length ≤ capacity.val := by
    rw [callOutput_length]
    exact Nat.min_le_left _ _
  apply store_exact
  omega

end Solidity.Yul.World.TargetMemory
