import Solidity.Semantics.Run
import Solidity.Evm.Machine

/-!
# Typed boundaries

External arguments keep their Solidity types, ledger keys are addresses,
path segments compose by type, and every EVM storage cell is a word.
The rejected terms pin the constraints, not just the constructors' shape.
-/

namespace Solidity.Examples.Tactics.Boundaries

open Semantics Evm

/-- `ping(uint(7), int(7), true)` retains all three argument types. -/
private def ping : ExtCall StandardExample [] :=
  ⟨.lit 9 rfl, "ping", [⟨.uint, .lit 7 rfl⟩, ⟨.int, .lit 7 rfl⟩, ⟨.bool, .bool true⟩]⟩

/-- The interpreter passes the typed values directly to the external-call key. -/
example : ping.keyT (State.init StandardExample) =
    ⟨⟨9, rfl⟩, "ping", [.uint ⟨7, rfl⟩, .int ⟨7, rfl⟩, .bool true]⟩ := by
  decide +kernel

/-- A raw integer is neither a typed address nor a typed call argument. -/
example : True := by
  fail_if_success have : ExtKey := ⟨(-1 : Int), "ping", []⟩
  fail_if_success have : CallValue := .uint (true : Bool)
  fail_if_success have : CallValue := .uint ⟨-1, by decide⟩
  fail_if_success have : Ledger := [((-1 : Int), 0)]
  trivial

/-- KeY's `net` remains unbounded and signed, even though its key is bounded. -/
example : lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote)
    ([(⟨9, rfl⟩, -(2 ^ 300))] : Ledger) = some (-(2 ^ 300)) := by
  decide +kernel

/-- An array segment can reach a uint; it cannot be composed with a bool tail. -/
example : True := by
  have : Segs (.ref (.array (.prim .uint))) (.prim .uint) := .cons (.at ⟨0, rfl⟩) .nil
  fail_if_success
    have : Segs (.ref (.array (.prim .uint))) (.prim .bool) := .cons (.at ⟨0, rfl⟩) .nil
  trivial

/-- A path's comparison observation comes from its typed segments. -/
example : (Path.at (E := .prim .uint) ⟨3, rfl⟩ .nil).segments.labels = [.at 3] := rfl

/-- An index is a `uint`: a negative one cannot be written. -/
example : True := by
  fail_if_success have : Path (.ref (.array (.prim .uint))) (.prim .uint) := .at ⟨-1, rfl⟩ .nil
  trivial

/-- SSTORE normalizes an oversized operand to a word and leaves another slot alone. -/
example : (WordStore.write WordStore.zero (.root 0) (W + 7)) (.root 0) = 7 := by
  rw [WordStore.write_same, Nat.add_mod_left, Nat.mod_eq_of_lt (by unfold W; decide)]

example : (WordStore.write WordStore.zero (.root 0) (W + 7)) (.root 1) = 0 := by
  rw [WordStore.write_other _ _ (by decide)]
  rfl

/-- Every machine storage read is a 256-bit word, including an untouched slot. -/
example (m : Machine) (s : Slot) : m.store s < W := WordStore.read_lt m.store s

end Solidity.Examples.Tactics.Boundaries
