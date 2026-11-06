import Solidity.Backend.Passes.Stack
import Solidity.Evm.MemoryCompileExamples
import Solidity.Syntax.Join

/-!
# Inhabited staged compiler controls

The published populated aliasing fixture is reused, rather than replacing it
by an empty heap. A core-only assertion precedes actual memory writes/reads.
The original whole-program entry refuses the combination. Staging therefore
does not assert totality of that entry or discharge the G01 session contract.
-/
namespace Solidity.Backend.Passes.Controls

open Solidity.Evm
open Solidity.Evm.Compiler
open Solidity.Evm.Memory
namespace Fixture
export Solidity.Evm.Memory.CompileExamples (C Γ σ machine base fixture_repr
  writeAndRead compiled coreAssignment checkedCore)
end Fixture
open Fixture

def assertion (v : Bool) : Prog C Γ Γ := .cons (.assert (.simple (.bool v))) .nil

def assertionCompiled (v : Bool) : Compilation 0 (Frag.init Γ) (assertion v) :=
  .core (Frag.init Γ) (by cases v <;> rfl)

def memoryCompiled : Compilation 0 (Frag.init Γ) writeAndRead := .memory compiled

def mixed : Prog C Γ Γ := (assertion true).join writeAndRead

def stagedCode : List Instr := (assertionCompiled true).code ++ memoryCompiled.code

/-- R01 is a real rejection, even with both individually inhabited stages. -/
theorem whole_program_refused :
    (Compiler.compile 0 (Frag.init Γ) mixed).isNone = true := by
  decide +kernel

/-- The core assertion is the identity on the *entire* machine for every
saved tail, not merely on a scalar projection of it. -/
theorem assertion_run (m : Machine) :
    run (assertionCompiled true).code m = .ok m 0 := by
  rfl

/-- This concrete source prefix leaves every heap, environment and frame
component unchanged, providing the otherwise missing core-to-memory bridge. -/
theorem source_prefix_identity :
    mixed.run σ = writeAndRead.run σ := by
  change Prog.run σ (.cons (.assert (.simple (.bool true))) writeAndRead) = _
  rw [Prog.run_cons_ok (o := ⟨σ, List.prefix_refl _⟩) (by rfl)]
  cases writeAndRead.run σ <;> rfl

def sourceOutput : Solidity.Out C σ.H Γ :=
  match writeAndRead.run σ with
  | .ok o => o
  | .error _ => ⟨σ, List.prefix_refl _⟩

theorem source_success : writeAndRead.run σ = .ok sourceOutput := by
  have h : (writeAndRead.run σ).halt? = none := by decide +kernel
  unfold sourceOutput
  generalize he : writeAndRead.run σ = res at *
  cases res with
  | ok o => rfl
  | error err => cases h

theorem memory_input : memoryCompiled.Input 1 4 base σ machine :=
  ⟨fixture_repr, by decide +kernel, .inl (by decide +kernel)⟩

/-- The concrete cross-branch boundary keeps the populated heap, all aliases
and allocator facts. It works at every arbitrary saved operand tail. -/
theorem mixed_success_tail (tail : List Word) :
    ∃ m', mixed.run σ = .ok sourceOutput ∧
      run stagedCode {machine with stack := tail} = .ok m' 0 ∧
      m'.stack = tail ∧ memoryCompiled.Rep 1 4 base
        σ {machine with stack := tail} sourceOutput.st m' := by
  obtain ⟨m', ht, hstack, hr⟩ :=
    compilation_success_tail memoryCompiled memory_input rfl source_success tail
  refine ⟨m', source_prefix_identity.trans source_success, ?_, hstack, hr⟩
  rw [stagedCode, run_append_ok (assertion_run _)]
  exact ht

private def cellValue (a : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem a with | .val w => some w.val | _ => none
  | _ => none

private def stackLength : Evm.Out → Option Nat
  | .ok m _ => some m.stack.length
  | _ => none

/-- The staged result is a nonempty successful value observation. -/
theorem result_five : cellValue 3 (run stagedCode machine) = some 5 := by
  decide +kernel

/-- A success witness refutes an always-reverting implementation locally. -/
theorem staged_not_always_revert : run stagedCode machine ≠ .revert := by
  intro h
  have hv := result_five
  rw [h] at hv
  cases hv

/-- Correct order leaves 5; moving the scalar core assignment after the
memory read leaves 8. This uses the existing compiler for both stages. -/
theorem wrong_order :
    cellValue 3 (run (checkedCore.code ++ stagedCode) machine) = some 5 ∧
    cellValue 3 (run (stagedCode ++ checkedCore.code) machine) = some 8 := by
  constructor <;> decide +kernel

/-- Appending an unbalanced POP corrupts an inhabited two-word saved tail. -/
theorem stack_corruption :
    stackLength (run stagedCode {machine with stack := [w[41], w[19]]}) = some 2 ∧
    stackLength (run (stagedCode ++ [.pop])
      {machine with stack := [w[41], w[19]]}) = some 1 := by
  constructor <;> decide +kernel

/-- Cherry-picking the accepted memory fragment erases the failing assertion.
The staged code reverts; the selected suffix alone succeeds with value 5. -/
theorem fragment_cherry_picking :
    run ((assertionCompiled false).code ++ memoryCompiled.code) machine = .revert ∧
    cellValue 3 (run memoryCompiled.code machine) = some 5 := by
  constructor
  · exact run_append_revert rfl
  · decide +kernel

/-- These adapters really accept a represented nonempty program. -/
theorem nonempty_acceptance :
    0 < (assertionCompiled true).code.length ∧ 0 < memoryCompiled.code.length := by
  constructor <;> decide +kernel

/-- Three staged pieces associate without changing pending-jump semantics. -/
theorem sequencing_associative (m : Machine) :
    run (((assertionCompiled true).code ++ checkedCore.code) ++ memoryCompiled.code) m =
      run ((assertionCompiled true).code ++ (checkedCore.code ++ memoryCompiled.code)) m := by
  rw [List.append_assoc]

/-- Actual recognizer acceptance of both nonempty stages, separately from
manual certificate construction or instruction-length observations. -/
theorem accepted_stages :
    (Compiler.compile 0 (Frag.init Γ) (assertion true)).isSome = true ∧
    (Compiler.compile 0 (Frag.init Γ) writeAndRead).isSome = true := by
  constructor <;> decide +kernel

/-- The actual compiler entry is not an empty-acceptance implementation. -/
theorem compiler_not_empty :
    ¬ (∀ {Δ : Ctx} (P : Prog C Γ Δ), (Compiler.compile 0 (Frag.init Γ) P).isNone = true) := by
  intro h
  have hbad : (Compiler.compile 0 (Frag.init Γ) writeAndRead).isNone = true := h writeAndRead
  have hyes : (Compiler.compile 0 (Frag.init Γ) writeAndRead).isNone = false := by decide +kernel
  rw [hyes] at hbad
  cases hbad

end Solidity.Backend.Passes.Controls
