import Solidity.Lowering.V08.AbiObservations

/-!
# Canonical signature selectors across the independent byte observations

Only the two published selector definitions are compared. No hash injectivity,
new hash implementation, payload emitter or source signature resolver is used.
The shared canonical signature string must still be justified by its owner.
-/
namespace Solidity.Lowering.V08.SelectorObservations
open Solidity

/-- Split a big-endian observation into its high and low byte regions. -/
theorem beBytes_split (high low number : Nat) :
    Source.beBytes (high + low) number =
      Source.beBytes high (number / 256 ^ low) ++ Source.beBytes low number := by
  induction low generalizing number with
  | zero => simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one, Source.beBytes, List.append_nil]
  | succ low ih =>
    change Source.beBytes ((high + low) + 1) number = _
    rw [Source.beBytes, ih]
    simp only [Source.beBytes, List.append_assoc, Nat.div_div_eq_div_mul, Nat.pow_succ']

/-- A prefix observation drops exactly the represented low bytes. -/
theorem beBytes_take (high low number : Nat) :
    (Source.beBytes (high + low) number).take high = Source.beBytes high (number / 256 ^ low) := by
  rw [beBytes_split]
  exact List.take_left' (Source.beBytes_length high _)

/-- The existing UInt32 selector's bytes agree with the source byte layout. -/
theorem selectorBytes_layout (selector : UInt32) :
    Semantics.selectorBytes selector = Source.beBytes 4 selector.toNat := by
  simp only [Semantics.selectorBytes, Source.beBytes, List.nil_append, List.cons_append,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply UInt8.toNat.inj
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.reduceToNat,
      UInt8.toNat_ofNat', Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      Nat.reducePow, Nat.reduceMul, Nat.mod_mod]

/-- Selector truncation agrees for arbitrary naturals, even above32 bits. -/
theorem selectorBytes_ofNat (number : Nat) :
    Semantics.selectorBytes (UInt32.ofNat number) = Source.beBytes 4 number := by
  rw [selectorBytes_layout, UInt32.toNat_ofNat']
  have power : (256 : Nat) ^ 4 = 2 ^ 32 := by decide +kernel
  rw [← power, beBytes_mod]

/-- Source selectors agree with the actual intrinsic customSelector byte
observation for every signature string. No bound on the raw hash is assumed. -/
theorem signature_selector (signature : String) :
    Source.selector signature = Semantics.selectorBytes (Semantics.customSelector signature) := by
  unfold Semantics.customSelector
  rw [selectorBytes_ofNat]
  unfold Source.selector Source.wordBytes Source.toWord Roadmap.Evm.keccakWord
  dsimp only
  rw [Nat.mod_mod]
  have power32 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide +kernel
  rw [← power32, beBytes_mod]
  rw [beBytes_take 4 28]
  have power28 : (256 : Nat) ^ 28 = 2 ^ 224 := by decide +kernel
  rw [power28]
  rfl

/-- Extend a supplied canonical signature observation with existing typed ABI
word observations, retaining exact argument order. This adds no payload emitter. -/
theorem signature_arguments (signature : String) (arguments : List Roadmap.Word) :
    Source.selector signature ++ arguments.flatMap Source.wordBytes =
      Semantics.selectorBytes (Semantics.customSelector signature) ++
        arguments.flatMap (fun word => Semantics.wordBytes word.val) := by
  rw [signature_selector, wordSequence_transport]

#print axioms signature_arguments
#print axioms beBytes_split
#print axioms beBytes_take
#print axioms selectorBytes_layout
#print axioms selectorBytes_ofNat
#print axioms signature_selector
end Solidity.Lowering.V08.SelectorObservations
