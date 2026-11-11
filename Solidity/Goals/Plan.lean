import Solidity.Tools.Goal
import Solidity.Yul.Words

/-! Plan steps outside the finish line: each goal names the theorem expected to close
it; all await vocabulary. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Main.trusted_surface_closed "va1-trust-surface"]
def trustedSurfaceClosed : Prop := Unstated

@[goal Solidity.Validation.differential_agreement "va3-semantic-validation"]
def differentialAgreement : Prop := Unstated

@[goal Solidity.Bench.budgets_met "vu1-benchmarks"]
def benchmarkBudgetsMet : Prop := Unstated

@[goal Solidity.Automation.fast_mode_agrees "vu2-fast-mode"]
def fastModeAgrees : Prop := Unstated

@[goal Solidity.Automation.Certificate.check_sound "vu3-certificates"]
def certificateCheckSound : Prop := Unstated

@[goal Solidity.Automation.Summary.call_summary_sound "vu4-modular"]
def callSummarySound : Prop := Unstated

@[goal Solidity.Yul.Views.generic_views_preserve "t1-yul-views-generic"]
def genericYulViewsPreserve : Prop := Unstated

@[goal Solidity.Controls.off_critical_path "t2-controls-off-path"]
def controlsOffCriticalPath : Prop := Unstated

@[goal Solidity.Dedup.statements_preserved "t3-dedup-rollout"]
def dedupStatementsPreserved : Prop := Unstated

@[goal Solidity.Docs.lint_clean "g2-doc-lint"]
def docLintClean : Prop := Unstated

@[goal Solidity.Docs.history_purged "g3-history-purge-docs"]
def docHistoryPurged : Prop := Unstated

@[goal Solidity.Docs.comments_as_code "g4-comments-to-code"]
def commentsAsCode : Prop := Unstated

/-! Arithmetic vocabulary for the universal opcode contract. Inputs are already
words, so quantifying over `Fin a → Word` covers the entire word domain.
All result equalities expose canonical natural residues modulo 2^256. -/
namespace OpcodeSpec

open Solidity.Yul

/-- Word modulus, independent of evaluation. -/
def modulus : Nat := 2 ^ 256

/-- Canonical residue of a signed integer, including negative results. -/
def residue (z : Int) : Nat := (z % (2 ^ 256)).toNat

/-- CLZ shared by Arithmetic and Bytes: zero has 256 leading zeros; for
nonzero words log2 is the position of the highest set bit. -/
def clz : Prop := ∀ xs : Fin 1 → Word,
  (Pure.eval .«clz» xs).val =
    (if (xs 0).val = 0 then 256 else 255 - (xs 0).val.log2) % modulus

end OpcodeSpec

open Solidity.Yul

/-- Source operand 0 is the shift amount; operand 1 is the value.
SAR divides the signed two's-complement integer with floor rounding, including
negative odd values. Amounts at least 256 give zero or the complete sign fill. -/
def opcodeShifts : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«shl» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val * 2 ^ (xs 0).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«shr» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val / 2 ^ (xs 0).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sar» xs).val =
    OpcodeSpec.residue (if (xs 0).val ≥ 256 then
      (if signed (xs 1) < 0 then -1 else 0)
      else signed (xs 1) / (2 ^ (xs 0).val : Int)))

/-- Source operands 0,1 are left,right; operand 2 is ADDMOD/MULMOD's
modulus. Natural intermediates are unbounded, with subtraction wrapping by
adding 2^256 first. Signed operands use `signed`'s two's-complement meaning;
`tdiv` truncates toward zero and `tmod` retains the dividend's sign. Residue
normalization includes minimum-signed / -1 overflow. Every zero divisor or
modulus gives zero. Comparisons return complete words 0 or 1, and bitwise
operations cover all 256 bits. No operand is excluded. -/
def opcodeArithmetic : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«add» xs).val =
    ((xs 0).val + (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sub» xs).val =
    ((xs 0).val + OpcodeSpec.modulus - (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«mul» xs).val =
    ((xs 0).val * (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«div» xs).val =
    (if (xs 1).val = 0 then 0 else (xs 0).val / (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«mod» xs).val =
    (if (xs 1).val = 0 then 0 else (xs 0).val % (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sdiv» xs).val =
    OpcodeSpec.residue (if (xs 1).val = 0 then 0 else (signed (xs 0)).tdiv (signed (xs 1)))) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«smod» xs).val =
    OpcodeSpec.residue (if (xs 1).val = 0 then 0 else (signed (xs 0)).tmod (signed (xs 1)))) ∧
  (∀ xs : Fin 3 → Word, (Pure.eval .«addmod» xs).val =
    (if (xs 2).val = 0 then 0 else ((xs 0).val + (xs 1).val) % (xs 2).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 3 → Word, (Pure.eval .«mulmod» xs).val =
    (if (xs 2).val = 0 then 0 else ((xs 0).val * (xs 1).val) % (xs 2).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«lt» xs).val =
    (if (xs 0).val < (xs 1).val then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«gt» xs).val =
    (if (xs 1).val < (xs 0).val then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«slt» xs).val =
    (if signed (xs 0) < signed (xs 1) then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«sgt» xs).val =
    (if signed (xs 1) < signed (xs 0) then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«eq» xs).val =
    (if (xs 0).val = (xs 1).val then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 1 → Word, (Pure.eval .«iszero» xs).val =
    (if (xs 0).val = 0 then 1 else 0) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 1 → Word, (Pure.eval .«not» xs).val =
    (OpcodeSpec.modulus - 1 - (xs 0).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«and» xs).val =
    ((xs 0).val &&& (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«or» xs).val =
    ((xs 0).val ||| (xs 1).val) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«xor» xs).val =
    ((xs 0).val ^^^ (xs 1).val) % OpcodeSpec.modulus) ∧
  OpcodeSpec.clz

/-- BYTE uses operand 0 as a big-endian byte index (0 is most significant),
with zero at every index ≥32. SIGNEXTEND uses operand 0 as a byte index,
tests bit 8*i+7, and is identity at every index ≥31. EXP uses operand 0 as
base and operand 1 as exponent: mathematical power includes exponent zero
(and 0^0 = 1), independently of the square-and-multiply implementation. -/
def opcodeBytesPowers : Prop :=
  (∀ xs : Fin 2 → Word, (Pure.eval .«byte» xs).val =
    (if (xs 0).val ≥ 32 then 0 else
      ((xs 1).val / 2 ^ (8 * (31 - (xs 0).val))) % 256) % OpcodeSpec.modulus) ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«signextend» xs).val =
    (if (xs 0).val ≥ 31 then (xs 1).val else
      let bits := 8 * ((xs 0).val + 1)
      let low := (xs 1).val % (2 ^ bits)
      if low < 2 ^ (bits - 1) then low
      else low + OpcodeSpec.modulus - 2 ^ bits) % OpcodeSpec.modulus) ∧
  OpcodeSpec.clz ∧
  (∀ xs : Fin 2 → Word, (Pure.eval .«exp» xs).val =
    (xs 0).val ^ (xs 1).val % OpcodeSpec.modulus)

/-- Universal arithmetic agreement for the 26 distinct opcodes in the finite
Checks families. CLZ has two memberships with one identical specification.
The three family obligations are independently usable by Checks-only proofs. -/
@[goal Solidity.Yul.opcode_eval_universal "v1-yul-checks-universal"]
def opcodeEvalUniversal : Prop :=
  opcodeShifts ∧ opcodeArithmetic ∧ opcodeBytesPowers

end Solidity.Goals
