import Solidity.Yul.Builtins
import Solidity.Roadmap.Contracts

/-!
# Pure Yul word operations

The word reuses `Roadmap.Word`. Target-machine agreement is kept in the
separate `EvmSigned` adapter, so pure operations do not import the machine.
Division and remainder explicitly return zero on a zero divisor, including
signed operations. Large shifts are tested before constructing powers.
ADDMOD/MULMOD use unbounded intermediates, not wrapped ADD/MUL.
-/
namespace Solidity.Yul

abbrev Word := Solidity.Roadmap.Word

def word (n : Nat) : Word := ⟨n % (2 ^ 256), Nat.mod_lt _ (by decide)⟩
def iword (n : Int) : Word := word (n % (2 ^ 256)).toNat
def signed (x : Word) : Int :=
  if x.val < 2 ^ 255 then x.val else (x.val : Int) - 2 ^ 256

def truth (p : Bool) : Word := word (if p then 1 else 0)

/-- Structural square-and-multiply over the bit length. This is an arithmetic
algorithm, not an execution horizon or a recursion cutoff. -/
def powBits : Nat → Word → Nat → Word
  | 0, _, _ => word 1
  | k + 1, b, e =>
    if e = 0 then word 1 else
      let p := powBits k (word (b.val * b.val)) (e / 2)
      if e % 2 = 0 then p else word (b.val * p.val)

/-- The mathematical square-and-multiply identity. -/
theorem pow_halve (b e : Nat) : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
  conv => lhs; rw [← Nat.div_add_mod e 2]
  rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]

/-- All exponent bits are consumed under the real bit-width premise. -/
theorem powBits_correct (k : Nat) (b : Word) (e : Nat) (h : e < 2 ^ k) :
    (powBits k b e).val = b.val ^ e % (2 ^ 256) := by
  induction k generalizing b e with
  | zero =>
      have he : e = 0 := by simp only [Nat.pow_zero] at h; omega
      subst e
      rfl
  | succ k ih =>
      have he : e / 2 < 2 ^ k := by rw [Nat.pow_succ] at h; omega
      simp only [powBits]
      split
      · next hz => subst e; rfl
      · by_cases hp : e % 2 = 0
        · rw [if_pos hp, ih _ _ he]
          change ((b.val * b.val) % (2 ^ 256)) ^ (e / 2) % (2 ^ 256) = _
          rw [← Nat.pow_mod, pow_halve b.val e, hp, Nat.pow_zero, Nat.mul_one]
        · rw [if_neg hp]
          change (b.val * (powBits k (word (b.val * b.val)) (e / 2)).val) % (2 ^ 256) = _
          rw [ih _ _ he]
          have hp1 : e % 2 = 1 := by have := Nat.mod_lt e (by decide : 0 < 2); omega
          change (b.val * (((b.val * b.val) % (2 ^ 256)) ^ (e / 2) % (2 ^ 256))) % (2 ^ 256) = _
          rw [Nat.mul_mod_mod, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod,
            pow_halve b.val e, hp1, Nat.pow_one, Nat.mul_comm b.val]

/-- Every natural exponent is handled, with no arbitrary bound. -/
def powWord (b : Word) (e : Nat) : Word := powBits (e.log2 + 1) b e

/-- EXP's exact unbounded-integer meaning, reduced to an EVM word. -/
theorem powWord_correct (b : Word) (e : Nat) :
    (powWord b e).val = b.val ^ e % (2 ^ 256) :=
  powBits_correct _ b e (Nat.lt_log2_self)

/-- Sign extension of byte `i`; index 31 and all larger indices are identities. -/
def signextend (i x : Word) : Word :=
  if i.val ≥ 31 then x else
    let bits := 8 * (i.val + 1)
    let low := x.val % (2 ^ bits)
    if low < 2 ^ (bits - 1) then word low
    else word (low + 2 ^ 256 - 2 ^ bits)

/-- Count leading zero bits, with CLZ(0)=256 (Osaka / EIP-7939). -/
def clz (x : Word) : Word :=
  word (if x.val = 0 then 256 else 255 - x.val.log2)

/-- Numeric meaning for each pure operation; arguments are in Yul source order. -/
def Pure.eval {a : Nat} (p : Pure a) : (Fin a → Word) → Word :=
  Pure.casesOn (motive := fun a _ => (Fin a → Word) → Word) p
    («iszero» := fun xs => truth ((xs 0).val == 0))
    («not» := fun xs => word (2 ^ 256 - 1 - (xs 0).val))
    («clz» := fun xs => Solidity.Yul.clz (xs 0))
    («add» := fun xs => word ((xs 0).val + (xs 1).val))
    («sub» := fun xs => word ((xs 0).val + 2 ^ 256 - (xs 1).val))
    («mul» := fun xs => word ((xs 0).val * (xs 1).val))
    («div» := fun xs => word ((xs 0).val / (xs 1).val))
    («sdiv» := fun xs => if (xs 1).val = 0 then word 0 else iword ((signed (xs 0)).tdiv (signed (xs 1))))
    («mod» := fun xs => if (xs 1).val = 0 then word 0 else word ((xs 0).val % (xs 1).val))
    («smod» := fun xs => if (xs 1).val = 0 then word 0 else iword ((signed (xs 0)).tmod (signed (xs 1))))
    («exp» := fun xs => powWord (xs 0) (xs 1).val)
    («lt» := fun xs => truth ((xs 0).val < (xs 1).val))
    («gt» := fun xs => truth ((xs 1).val < (xs 0).val))
    («slt» := fun xs => truth (signed (xs 0) < signed (xs 1)))
    («sgt» := fun xs => truth (signed (xs 1) < signed (xs 0)))
    («eq» := fun xs => truth ((xs 0).val == (xs 1).val))
    («and» := fun xs => word ((xs 0).val &&& (xs 1).val))
    («or» := fun xs => word ((xs 0).val ||| (xs 1).val))
    («xor» := fun xs => word ((xs 0).val ^^^ (xs 1).val))
    («byte» := fun xs =>
    if (xs 0).val ≥ 32 then word 0 else word (((xs 1).val >>> (8 * (31 - (xs 0).val))) % 256))
    («shl» := fun xs => if (xs 0).val ≥ 256 then word 0 else word ((xs 1).val <<< (xs 0).val))
    («shr» := fun xs => if (xs 0).val ≥ 256 then word 0 else word ((xs 1).val >>> (xs 0).val))
    («sar» := fun xs =>
    if (xs 0).val ≥ 256 then (if signed (xs 1) < 0 then word (2 ^ 256 - 1) else word 0)
    else iword (signed (xs 1) >>> (xs 0).val))
    («signextend» := fun xs => Solidity.Yul.signextend (xs 0) (xs 1))
    («addmod» := fun xs =>
    if (xs 2).val = 0 then word 0 else word (((xs 0).val + (xs 1).val) % (xs 2).val))
    («mulmod» := fun xs =>
    if (xs 2).val = 0 then word 0 else word (((xs 0).val * (xs 1).val) % (xs 2).val))


/-- Every operation produces a word, even DIV/MOD by zero. -/
theorem Pure.eval_range {a : Nat} (p : Pure a) (xs : Fin a → Word) :
    (p.eval xs).val < 2 ^ 256 := (p.eval xs).isLt

/-- Yul `div(x, 0)` returns zero for every word. -/
theorem div_zero (x : Word) : Pure.eval .«div» (fun i => if i = 0 then x else word 0) = word 0 := by
  change word (x.val / 0) = word 0
  rw [Nat.div_zero]

/-- Yul `mod(x, 0)` returns zero, unlike Solidity's `%`. -/
theorem mod_zero (x : Word) : Pure.eval .«mod» (fun i => if i = 0 then x else word 0) = word 0 := by
  rfl

end Solidity.Yul
