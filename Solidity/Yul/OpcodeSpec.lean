import Solidity.Yul.Words

/-! # Universal opcode specifications

The arithmetic meaning of the 26 distinct opcodes of the finite Checks
families, stated over every input. Inputs are already words, so quantifying
over `Fin a → Word` covers the entire word domain. All result equalities expose
canonical natural residues modulo 2^256. `Solidity.Goals` states its plan goals
as definitionally equal wrappers of these propositions. -/
namespace Solidity.Yul.OpcodeSpec

/-- Word modulus, independent of evaluation. -/
def modulus : Nat := 2 ^ 256

/-- Canonical residue of a signed integer, including negative results. -/
def residue (z : Int) : Nat := (z % (2 ^ 256)).toNat

/-- CLZ shared by Arithmetic and Bytes: zero has 256 leading zeros; for
nonzero words log2 is the position of the highest set bit. -/
def clz : Prop := ∀ xs : Fin 1 → Word,
  (Pure.eval .«clz» xs).val =
    (if (xs 0).val = 0 then 256 else 255 - (xs 0).val.log2) % modulus

/-- Source operand 0 is the shift amount; operand 1 is the value.
SAR divides the signed two's-complement integer with floor rounding, including
negative odd values. Amounts at least 256 give zero or the complete sign fill. -/
def shifts : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«shl» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val * 2 ^ (xs 0).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«shr» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val / 2 ^ (xs 0).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sar» xs).val =
    residue (if (xs 0).val ≥ 256 then
      (if signed (xs 1) < 0 then -1 else 0)
      else signed (xs 1) / (2 ^ (xs 0).val : Int)))

/-- Source operands 0,1 are left,right; operand 2 is ADDMOD/MULMOD's
modulus. Natural intermediates are unbounded, with subtraction wrapping by
adding 2^256 first. Signed operands use `signed`'s two's-complement meaning;
`tdiv` truncates toward zero and `tmod` retains the dividend's sign. Residue
normalization includes minimum-signed / -1 overflow. Every zero divisor or
modulus gives zero. Comparisons return complete words 0 or 1, and bitwise
operations cover all 256 bits. No operand is excluded. -/
def arithmetic : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«add» xs).val =
    ((xs 0).val + (xs 1).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sub» xs).val =
    ((xs 0).val + modulus - (xs 1).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«mul» xs).val =
    ((xs 0).val * (xs 1).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«div» xs).val =
    (if (xs 1).val = 0 then 0 else (xs 0).val / (xs 1).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«mod» xs).val =
    (if (xs 1).val = 0 then 0 else (xs 0).val % (xs 1).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sdiv» xs).val =
    residue (if (xs 1).val = 0 then 0 else (signed (xs 0)).tdiv (signed (xs 1)))) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«smod» xs).val =
    residue (if (xs 1).val = 0 then 0 else (signed (xs 0)).tmod (signed (xs 1)))) ∧
  (∀ xs : Fin 3 → Word, (Pure.eval .«addmod» xs).val =
    (if (xs 2).val = 0 then 0 else ((xs 0).val + (xs 1).val) % (xs 2).val) % modulus) ∧
  (∀ xs : Fin 3 → Word, (Pure.eval .«mulmod» xs).val =
    (if (xs 2).val = 0 then 0 else ((xs 0).val * (xs 1).val) % (xs 2).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«lt» xs).val =
    (if (xs 0).val < (xs 1).val then 1 else 0) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«gt» xs).val =
    (if (xs 1).val < (xs 0).val then 1 else 0) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«slt» xs).val =
    (if signed (xs 0) < signed (xs 1) then 1 else 0) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sgt» xs).val =
    (if signed (xs 1) < signed (xs 0) then 1 else 0) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«eq» xs).val =
    (if (xs 0).val = (xs 1).val then 1 else 0) % modulus) ∧
  (∀ xs : Fin 1 → Word, (Pure.eval .«iszero» xs).val =
    (if (xs 0).val = 0 then 1 else 0) % modulus) ∧
  (∀ xs : Fin 1 → Word, (Pure.eval .«not» xs).val =
    (modulus - 1 - (xs 0).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«and» xs).val =
    ((xs 0).val &&& (xs 1).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«or» xs).val =
    ((xs 0).val ||| (xs 1).val) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«xor» xs).val =
    ((xs 0).val ^^^ (xs 1).val) % modulus) ∧
  clz

/-- BYTE uses operand 0 as a big-endian byte index (0 is most significant),
with zero at every index ≥32. SIGNEXTEND uses operand 0 as a byte index,
tests bit 8*i+7, and is identity at every index ≥31. EXP uses operand 0 as
base and operand 1 as exponent: mathematical power includes exponent zero
(and 0^0 = 1), independently of the square-and-multiply implementation. -/
def bytesPowers : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«byte» xs).val =
    (if (xs 0).val ≥ 32 then 0 else
      ((xs 1).val / 2 ^ (8 * (31 - (xs 0).val))) % 256) % modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«signextend» xs).val =
    (if (xs 0).val ≥ 31 then (xs 1).val else
      let bits := 8 * ((xs 0).val + 1)
      let low := (xs 1).val % (2 ^ bits)
      if low < 2 ^ (bits - 1) then low
      else low + modulus - 2 ^ bits) % modulus) ∧
  clz ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«exp» xs).val =
    (xs 0).val ^ (xs 1).val % modulus)

/-- Universal arithmetic agreement for the 26 distinct opcodes in the finite
Checks families. CLZ has two memberships with one identical specification.
The three family obligations are independently usable by Checks-only proofs. -/
def evalUniversal : Prop :=
  shifts ∧ arithmetic ∧ bytesPowers

end Solidity.Yul.OpcodeSpec
