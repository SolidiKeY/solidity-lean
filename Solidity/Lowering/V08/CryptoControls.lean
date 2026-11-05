import Solidity.Lowering.V08.CryptoObservations
import Solidity.Roadmap.Controls

/-! Kernel witnesses for the fixed Keccak boundary. Existing G07 toyFixed is
used only for its published real Keccak pin, not its ledger/precompile mocks. -/
namespace Solidity.Lowering.V08.CryptoControls
open Solidity
open CryptoObservations

def binary : List UInt8 := [0x00, 0xff, 0x80]

/-- An inhabited published pin applies to a nonempty binary input. -/
theorem fixed_transport : EnvironmentProjection.liftWord (Roadmap.Controls.toyFixed.hash binary) =
    keccakBytes [0, 255, 128] :=
  fixed_keccak_observation Roadmap.Controls.toyFixed Roadmap.Controls.toyFixed_keccak binary

/-- The actual intrinsic empty-byte hash equals the standard Keccak vector. -/
theorem empty_hash : (keccakBytes []).1 =
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  unfold keccakBytes
  decide +kernel

/-- A wrong input byte changes these concrete hashes; no injectivity is assumed. -/
theorem wrong_input : keccakBytes [0, 255, 128] ≠ keccakBytes [0, 255, 127] := by
  unfold keccakBytes
  decide +kernel

/-- Zero cannot substitute for the exact observed empty-input hash word. -/
theorem wrong_hash : (keccakBytes []).1 ≠ 0 := by
  rw [empty_hash]
  decide +kernel

#print axioms fixed_transport
#print axioms empty_hash
#print axioms wrong_input
#print axioms wrong_hash
end Solidity.Lowering.V08.CryptoControls
