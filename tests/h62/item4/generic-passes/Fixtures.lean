import Solidity.Backend.Passes.AssignmentAdditionControls
import Solidity.Backend.Passes.AssignmentSubtractionControls
import Solidity.Backend.Passes.AssignmentMultiplicationControls
/-! Typed fixtures retain the original public selected programs, dependent value
code, populated inputs, expected machines and ordered observations. All original
negative/refusal declarations remain in their original modules and are aliased
with their exact inferred types below. This table does not prove arithmetic. -/
namespace Solidity.Backend.Passes.H62Fixtures
open Evm Evm.Memory Evm.Compiler
structure Fixture where
  C : Contract
  Γ : Ctx
  Δ : Ctx
  b : Nat
  F : Frag Γ
  program : Prog C Γ Δ
  compiled : CompiledProg b F program
  expression : Val C Δ .uint
  operand : CompiledVal b compiled.frag expression
  initial : Machine
  final : Machine
  expected : Word
  cells : List Nat

inductive Operator where
  | addition | subtraction | multiplication
  deriving DecidableEq

private def addition (pipeline : Roadmap.Pipeline) : Fixture where
  C := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.C
  Γ := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.Γ
  Δ := .val .uint :: .val .uint :: Solidity.Backend.Passes.AssignmentAdditionPass.Controls.Γ
  b := 1
  F := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.F
  program := Solidity.Lowering.V07.assignReadPrefix pipeline Solidity.Backend.Passes.AssignmentAdditionPass.Controls.i Solidity.Backend.Passes.AssignmentAdditionPass.Controls.a
  compiled := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.compiled pipeline
  expression := Solidity.Backend.Passes.AssignmentAdditionPass.value pipeline 8
  operand := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.operand pipeline
  initial := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.machine
  final := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.after pipeline
  expected := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.resultWord pipeline
  cells := Solidity.Backend.Passes.AssignmentAdditionPass.Controls.cells

private def subtraction (pipeline : Roadmap.Pipeline) : Fixture where
  C := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.C
  Γ := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.Γ
  Δ := .val .uint :: .val .uint :: Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.Γ
  b := 1
  F := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.F
  program := Solidity.Lowering.V07.assignReadPrefix pipeline Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.i Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.a
  compiled := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.compiled pipeline
  expression := Solidity.Backend.Passes.AssignmentSubtractionPass.value pipeline .u8
  operand := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.operand pipeline
  initial := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.machine
  final := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.after pipeline
  expected := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.resultWord pipeline
  cells := Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.cells

private def multiplication (pipeline : Roadmap.Pipeline) : Fixture where
  C := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.C
  Γ := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.Γ
  Δ := .val .uint :: .val .uint :: Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.Γ
  b := 1
  F := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.F
  program := Solidity.Lowering.V07.assignReadPrefix pipeline Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.i Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.a
  compiled := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.compiled pipeline
  expression := Solidity.Backend.Passes.AssignmentMultiplicationPass.value pipeline 8
  operand := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.operand pipeline
  initial := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.machine
  final := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.after pipeline
  expected := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.resultWord pipeline
  cells := Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.cells

def fixture (operator : Operator) (pipeline : Roadmap.Pipeline) : Fixture :=
  match operator with
  | .addition => addition pipeline
  | .subtraction => subtraction pipeline
  | .multiplication => multiplication pipeline

def table : List Fixture :=
  [fixture .addition .legacy, fixture .addition .viaIR,
   fixture .subtraction .legacy, fixture .subtraction .viaIR,
   fixture .multiplication .legacy, fixture .multiplication .viaIR]

/-- Exact original emitted equations at every table row. The owner proofs,
including their Source transport, remain the semantic producers. -/
theorem correspondence (operator : Operator) (pipeline : Roadmap.Pipeline) (tail : List Word) :
    let row := fixture operator pipeline
    run (row.compiled.code ++ row.operand.code) {row.initial with stack := tail} =
      .ok ({row.final with stack := tail}.push row.expected) 0 := by
  cases operator with
  | addition => exact AssignmentAdditionPass.Controls.emitted pipeline tail
  | subtraction => exact AssignmentSubtractionPass.Controls.emitted pipeline tail
  | multiplication => exact AssignmentMultiplicationPass.Controls.emitted pipeline tail

end Solidity.Backend.Passes.H62Fixtures
