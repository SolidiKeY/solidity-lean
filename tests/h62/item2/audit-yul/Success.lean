import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Yul.Composition.CorrectnessPublicControls

/-! Additive audit of unchanged producer and generic composition contracts.
Literal assignment covers every 256-bit word, with arbitrary caller tail.
The scalar runner has no gas/fork model: these results assert no native gas,
Osaka execution, G24 embedding or admitted Solidity assembly adequacy.
-/
namespace H62.AuditYul
open Solidity Solidity.Yul Solidity.Yul.Compilation
open Solidity.Backend Solidity.Backend.Scalar
open Solidity.Yul.Closed ProducerExpressions

def control : Control := ⟨false, false⟩
def assignment (w : Solidity.Yul.Word) : Stmt [] [] control 1 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal w)
def assignmentCertificate (w : Solidity.Yul.Word) :
    ProducerStatements.Compiled 2 (assignment w) :=
  ProducerStatements.assign 0 (ProducerExpressions.literal 0 w)
def assignmentCode (w : Solidity.Yul.Word) : Program :=
  [pushWord (BitVec.ofFin w)] ++ writeSlot ⟨0, by decide⟩

/-- All data and all proof hypotheses of the unchanged `executes` statement
are supplied together. The assignment writes a real local, not an empty skip. -/
theorem statement_joint_witness :
    ∃ (compiled : ProducerStatements.Compiled 2 (assignment 7))
      (depth : Nat) (code : Program) (_locals : Vector Scalar.Word 1)
      (_newer : Vector Scalar.Word depth) (_caller : Stack),
      compiled.lowered.code depth = some code :=
  ⟨assignmentCertificate 7, 0, assignmentCode 7, #v[0], #v[], [], rfl⟩

/-- All expression endpoint hypotheses are likewise simultaneously feasible. -/
theorem expression_joint_witness :
    ∃ (compiled : ProducerExpressions.Compiled 1 (Expr.literal (n := 1) 7))
      (depth : Nat) (code : Program) (_locals : Vector Scalar.Word 1)
      (_newer : Vector Scalar.Word depth) (_caller : Stack),
      compiled.lowered.code depth = some code :=
  ⟨ProducerExpressions.literal 0 7, 0, [pushWord 7], #v[0], #v[], [], rfl⟩

/-- The successful visitor result is exactly the certificate whose emitted
code and source/target runs are checked below. -/
theorem assignment_compile_eq (w : Solidity.Yul.Word) :
    ProducerStatements.compile 2 (assignment w) = some (assignmentCertificate w) := rfl

/-- The actual executable visitor accepts every supported literal assignment
at this exact horizon; acceptance is derived, never assumed. -/
theorem assignment_total (w : Solidity.Yul.Word) :
    (ProducerStatements.compile 2 (assignment w)).isSome = true := rfl

/-- Actual source and emitted scalar code both complete. Every original word
and arbitrary caller stack survive except the selected assignment destination. -/
theorem assignment_success (w : Solidity.Yul.Word)
    (locals : Vector Scalar.Word 1) (caller : Stack) :
    evalStmt 2 .nil True.intro (assignment w) (assignmentCertificate w).profile
      (sourceLocals locals) =
        some ⟨sourceLocals ((assignmentCertificate w).update locals), .normal⟩ ∧
    Scalar.run (assignmentCode w) (locals.toList ++ caller) =
      some (((assignmentCertificate w).update locals).toList ++ caller) :=
  ProducerStatements.executes (assignmentCertificate w) 0 (assignmentCode w) rfl
    locals #v[] caller

/-- A reject-all replacement fails the concrete totality requirement. -/
theorem reject_all_fails :
    ¬ (∀ w : Solidity.Yul.Word,
      ((fun (fuel : Nat) (stmt : Stmt [] [] control 1) =>
        (none : Option (ProducerStatements.Compiled fuel stmt))) 2 (assignment w)).isSome = true) := by
  intro h
  have bad : false = true := h 7
  cases bad

/-- No valid normally completing statement certificate can emit a REVERT-only
stream at this boundary, irrespective of its selected update. -/
theorem any_revert_certificate_fails (w : Solidity.Yul.Word)
    (compiled : ProducerStatements.Compiled 2 (assignment w)) :
    compiled.lowered.code 0 ≠ some [.op .REVERT] := by
  intro emitted
  have bad := compiled.lowered.correct 0 [.op .REVERT] emitted #v[0] #v[] []
  change none = some _ at bad
  cases bad

/-- An always-reverting instruction stream cannot be emitted by a valid
certificate at this accessible assignment boundary. -/
theorem revert_code_fails (w : Solidity.Yul.Word) :
    (assignmentCertificate w).lowered.code 0 ≠ some [.op .REVERT] := by
  intro h
  have run_ok := (assignment_success w #v[0] []).2
  have code_eq : assignmentCode w = [.op .REVERT] := Option.some.inj h
  rw [code_eq] at run_ok
  change none = some _ at run_ok
  cases run_ok

/-- Exact one-step-before completion boundary; source fuel is not native gas. -/
theorem assignment_horizon_refusal (w : Solidity.Yul.Word) :
    ProducerStatements.compile 1 (assignment w) = none := rfl

/-- Concrete global composition premise record and its linking hypothesis,
inhabited jointly. This is G01's toy instance, not assembly admission. -/
theorem public_joint_witness :
    ∃ _B : Solidity.Yul.Composition.CorrectnessInstances.PublicBoundary
      Solidity.Yul.Composition.CorrectnessControls.stages
      Solidity.Yul.Composition.CorrectnessControls.table (fun _ _ => none),
      Solidity.Yul.Composition.CorrectnessControls.stages.TablesLinked
        Solidity.Yul.Composition.CorrectnessControls.table :=
  ⟨Solidity.Yul.Composition.CorrectnessControls.boundary,
    Solidity.Yul.Composition.CorrectnessControls.linked⟩

#print axioms statement_joint_witness
#print axioms expression_joint_witness
#print axioms assignment_compile_eq
#print axioms any_revert_certificate_fails
#print axioms assignment_total
#print axioms assignment_success
#print axioms reject_all_fails
#print axioms revert_code_fails
#print axioms assignment_horizon_refusal
#print axioms public_joint_witness
end H62.AuditYul
