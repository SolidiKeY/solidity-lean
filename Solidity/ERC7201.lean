import Solidity.RevertBytes
import Lean.Elab.Tactic.Omega

/-!
# ERC-7201 namespace integers

The namespace formula over bytes, without physical storage slots. Both the
elaborator's constant folding and its runtime lowering use Keccak-256 and
one big-endian ABI word. Subtraction wraps at 256 bits even in checked code.
No collision or namespace-disjointness assumption is made.
-/

namespace Solidity.ERC7201

/-- The first digest minus one, modulo the width of an ABI word. -/
def predecessor (h : Nat) : Fin (2 ^ 256) :=
  ⟨(h + 2 ^ 256 - 1) % 2 ^ 256, Nat.mod_lt _ (by decide)⟩

/-- Clear the least significant byte of a bounded word. -/
def align (h : Fin (2 ^ 256)) : Fin (2 ^ 256) :=
  ⟨h.val / 256 * 256, by have hh := h.isLt; omega⟩

/-- `keccak256(abi.encode(uint256(keccak256(id)) - 1)) & ~uint256(255)`. -/
def root (id : List UInt8) : Fin (2 ^ 256) :=
  let first := Keccak.keccak256Nat (id.map UInt8.toNat)
  let input := Semantics.wordBytes (predecessor first).val
  let second := Keccak.keccak256Nat (input.map UInt8.toNat)
  align ⟨second % 2 ^ 256, Nat.mod_lt _ (by decide)⟩

/-- Every namespace result has its low eight bits clear. -/
theorem root_aligned (id : List UInt8) : (root id).val % 256 = 0 := by
  simp only [root, align, Nat.mul_mod_left]

/-- The subtraction is wrapping, including the zero-digest boundary. -/
theorem predecessor_zero : (predecessor 0).val = 2 ^ 256 - 1 := by
  decide

end Solidity.ERC7201
