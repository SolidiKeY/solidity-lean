import Solidity.Lowering.V08.CryptoControls

/-! Regression: arbitrary Nat lists do not satisfy byte-fold bounds merely
because they are called bytes. UInt8 inputs supply the original universal bound
for every member. The existing real Keccak pin and both word observations then
coexist for the same arbitrary input; no hash injectivity, Source execution,
ledger/precompile correctness or compiler/admission adequacy is asserted. -/
namespace H62.AuditV08Adapters.TypedKeccakJoint
open Solidity
open Solidity.Lowering.V08
open CryptoObservations

/-- The original bound follows from the input type, with no input-length bound. -/
theorem typed_bytes (bytes : List UInt8) :
    ∀ byte, byte ∈ bytes.map UInt8.toNat → byte < 256 := by
  intro byte member
  obtain ⟨value, _, equal⟩ := List.mem_map.mp member
  subst byte
  exact value.toNat_lt

/-- The complete published pin and byte-bound premise inhabit one input model. -/
theorem joint (bytes : List UInt8) : Roadmap.Controls.toyFixed.Keccak ∧
    ∀ byte, byte ∈ bytes.map UInt8.toNat → byte < 256 :=
  ⟨Roadmap.Controls.toyFixed_keccak, typed_bytes bytes⟩

/-- Arbitrary accumulators and inputs retain the original strict fold bound. -/
theorem actual_fold (bytes : List UInt8) (initial : Nat) :
    (bytes.map UInt8.toNat).foldl (fun accumulator byte => 256 * accumulator + byte) initial <
      (initial + 1) * 256 ^ bytes.length := by
  simpa only [List.length_map] using fold_byte_bound (bytes.map UInt8.toNat)
    (joint bytes).2 initial

/-- Both original observations share the same pin and arbitrary input bytes. -/
theorem actual_observations (bytes : List UInt8) :
    EnvironmentProjection.liftWord (Roadmap.Controls.toyFixed.hash bytes) =
      keccakBytes (bytes.map (fun byte => (byte.toNat : Int))) ∧
    Source.wordBytes (Roadmap.Controls.toyFixed.hash bytes) =
      Semantics.wordBytes (keccakBytes (bytes.map (fun byte => (byte.toNat : Int)))).1.toNat :=
  ⟨fixed_keccak_observation _ (joint bytes).1 bytes,
    fixed_keccak_bytes _ (joint bytes).1 bytes⟩

/-- A genuinely out-of-range Nat element violates the original premise. -/
theorem invalid_nat_refused :
    ¬ (∀ byte, byte ∈ ([256] : List Nat) → byte < 256) := by
  intro bounded
  have impossible := bounded 256 (List.mem_singleton_self _)
  omega

#print axioms typed_bytes
#print axioms joint
#print axioms actual_fold
#print axioms actual_observations
#print axioms invalid_nat_refused
end H62.AuditV08Adapters.TypedKeccakJoint
