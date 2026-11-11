import Solidity.Tools.Goal
import Solidity.Yul.OpcodeSpec

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

/-! Arithmetic vocabulary for the universal opcode contract: wrappers of the
pure statements in `Solidity.Yul.OpcodeSpec`, which proofs in the core use
without importing goal tooling. -/
namespace OpcodeSpec

/-- Word modulus, independent of evaluation. -/
def modulus : Nat := Solidity.Yul.OpcodeSpec.modulus

/-- Canonical residue of a signed integer, including negative results. -/
def residue (z : Int) : Nat := Solidity.Yul.OpcodeSpec.residue z

/-- CLZ shared by Arithmetic and Bytes (`Solidity.Yul.OpcodeSpec.clz`). -/
def clz : Prop := Solidity.Yul.OpcodeSpec.clz

end OpcodeSpec

/-- SHL, SHR and SAR over every input (`Solidity.Yul.OpcodeSpec.shifts`). -/
def opcodeShifts : Prop := Solidity.Yul.OpcodeSpec.shifts

/-- The twenty arithmetic, comparison and bitwise opcodes over every input
(`Solidity.Yul.OpcodeSpec.arithmetic`). -/
def opcodeArithmetic : Prop := Solidity.Yul.OpcodeSpec.arithmetic

/-- BYTE, SIGNEXTEND, CLZ and EXP over every input
(`Solidity.Yul.OpcodeSpec.bytesPowers`). -/
def opcodeBytesPowers : Prop := Solidity.Yul.OpcodeSpec.bytesPowers

/-- Universal arithmetic agreement for the 26 distinct opcodes in the finite
Checks families. CLZ has two memberships with one identical specification.
The three family obligations are independently usable by Checks-only proofs. -/
@[goal Solidity.Yul.opcode_eval_universal "v1-yul-checks-universal"]
def opcodeEvalUniversal : Prop :=
  opcodeShifts ∧ opcodeArithmetic ∧ opcodeBytesPowers

end Solidity.Goals
