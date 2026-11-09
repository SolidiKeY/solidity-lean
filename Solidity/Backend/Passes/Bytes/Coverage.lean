import Solidity.Backend.Passes.Bytes.Stage
import Solidity.Backend.Passes.CompilerWholeScope
import Solidity.Backend.Passes.CompilerScopedFailure
import Solidity.Backend.Passes.FreshBooleanCompilation
import Solidity.Backend.Passes.RelatedStorageCaptureControls
import Solidity.Backend.Passes.LoopCallControls
import Solidity.Backend.Passes.DeferredConditionFailureControls
import Solidity.Backend.Passes.MemoryCallReuse

/-! Measured coverage of the bytes stage on the compiled fixtures reachable
from `Backend/Passes`: each compiler result is accepted, or its first
instruction refused by the proved scalar selector is named by index and
family. Every count below is checked by the kernel (`decide +kernel`). -/
namespace Solidity.Backend.Passes.Bytes
open Solidity.Backend Selection Evm Evm.Memory Evm.Compiler

/-- Instruction families of checked-entry code, for the gap report. -/
inductive Family where
  | push | stack | arithmetic | comparison | bitwise | signed
  | hashing | storage | fixedMemory | stackMemory | skipJump | call | revert
  | environment | loop
  deriving DecidableEq, Repr

def family : Evm.Instr → Family
  | .push _ => .push
  | .pop | .dup _ | .swap _ => .stack
  | .add | .sub | .mul | .div | .mod | .exp => .arithmetic
  | .lt | .gt | .eq | .iszero => .comparison
  | .or | .and | .xor | .not | .shl | .shr | .sar => .bitwise
  | .slt | .sgt | .sdiv | .smod => .signed
  | .keccakMap | .keccakArr => .hashing
  | .sload | .sstore => .storage
  | .mload _ | .mstore _ => .fixedMemory
  | .mloadAt | .mstoreAt => .stackMemory
  | .jump _ | .jumpi _ => .skipJump
  | .call => .call
  | .revert => .revert
  | .caller | .callvalue | .timestamp | .selfbalance | .address => .environment
  | .loop _ _ => .loop

/-- Whether the proved scalar selector accepts one instruction. -/
def selected (i : Evm.Instr) : Bool := (selectScalar i).isSome

/-- Coverage of one instruction list. -/
structure Measure where
  /-- Number of instructions. -/
  length : Nat
  /-- Number the selector refuses. -/
  refused : Nat
  /-- First refused instruction: index and family. -/
  first : Option (Nat × Family)
  /-- Families refused, in order of first occurrence. -/
  families : List Family
  /-- Whether the whole stage accepts the code at input height 0. -/
  accepted : Bool
  deriving DecidableEq, Repr

def firstRefused : Nat → List Evm.Instr → Option (Nat × Family)
  | _, [] => none
  | k, i :: rest => if selected i then firstRefused (k + 1) rest else some (k, family i)

def refusedFamilies (ir : List Evm.Instr) : List Family :=
  (ir.filter (! selected ·)).foldl
    (fun seen i => if family i ∈ seen then seen else seen ++ [family i]) []

def measure (ir : List Evm.Instr) : Measure where
  length := ir.length
  refused := (ir.filter (! selected ·)).length
  first := firstRefused 0 ir
  families := refusedFamilies ir
  accepted := match stage ir 0 with | .ok _ => true | .error _ => false

/-- A measurement agrees with the stage: acceptance means some accepted record. -/
theorem measure_accepted (ir : List Evm.Instr) (h : (measure ir).accepted = true) :
    ∃ accepted, stage ir 0 = .ok accepted := by
  simp only [measure] at h
  split at h
  · next accepted staged => exact ⟨accepted, staged⟩
  · cases h

/-! ## Fixtures -/

def wholeScope := (Compiler.compile 1 (Frag.init []) CompilerWholeScope.program).map (measure ·.code)
def callScope := (Compiler.compile 1 MemoryCallControls.allocation.frag
  MemoryCallScopeBoundary.Controls.scopeProgram).map (measure ·.code)
def memoryCall := (Compiler.compile 1 MemoryCallControls.allocation.frag
  MemoryCallControls.call).map (measure ·.code)
def scopedArgument := (Compiler.compile 1 (Frag.init [])
  CompilerScopedFailure.argumentProgram).map (measure ·.code)
def scopedBody := (Compiler.compile 1 (Frag.init [])
  CompilerScopedFailure.bodyProgram).map (measure ·.code)
def fixedBoolean := (Compiler.compile 1 FixedBooleanSequence.BF
  FixedBooleanSequence.fixedProgram).map (measure ·.code)
def freshBoolean (b : Bool) := (Compiler.compile 1 (Frag.init [])
  (FreshBooleanFailure.wholeProgram b)).map (measure ·.code)
def relatedStorage := (Compiler.compile 0 RelatedStorageCapture.Controls.F
  RelatedStorageCapture.Controls.program).map (measure ·.code)
def loopScope := (Compiler.compile 1 LoopScopeControls.preparation.frag
  LoopScopeControls.wrapped).map (measure ·.code)
def loopCall := (Compiler.compile 1 LoopScopeControls.enclosed.frag
  LoopCallControls.call).map (measure ·.code)
def deferredPanic := (Compiler.compile 0 ReferenceControls.fb
  (DeferredConditionFailure.Controls.immediate true).code).map (measure ·.code)
def reuseScalar := (Compiler.compile 1 MemoryCallReuse.leading.frag
  MemoryCallReuse.scalarCall).map (measure ·.code)
def reuseAlias := (Compiler.compile 1 MemoryCallReuse.leading.frag
  MemoryCallReuse.aliasCall).map (measure ·.code)
def reuseVoid := (Compiler.compile 1 MemoryCallReuse.leading.frag
  MemoryCallReuse.voidCall).map (measure ·.code)
def reuseWrong := (Compiler.compile 1 MemoryCallReuse.leading.frag
  MemoryCallReuse.wrongCall).map (measure ·.code)
def empty := (Compiler.compile 0 (Frag.init []) (.nil : Prog MemoryCallControls.C [] [])).map
  (measure ·.code)

/-! ## Compiled value fragments

No whole compiled program except the empty one is accepted: every statement
ends in a fixed-cell write, storage, or an `assertTop` skip-jump. The
compiler's expression stage (`Evm.compileVal`) on locals-free unchecked
arithmetic is accepted; checked `+` is refused at its overflow `JUMPI`. -/

abbrev C := MemoryCallControls.C

def two : Val C [] .uint := .simple (.lit 2 (by decide))
def three : Val C [] .uint := .simple (.lit 3 (by decide))
def nine : Val C [] .uint := .simple (.lit 9 (by decide))
/-- `unchecked { 2 + 3 } < 9`. -/
def comparison : Val C [] .bool := .binop .lt rfl rfl (.binop .addW rfl rfl two three) nine
/-- Checked `2 + 3`. -/
def checkedSum : Val C [] .uint := .binop .add rfl rfl two three

def comparisonCode : List Evm.Instr := compileVal 0 comparison
def checkedCode : List Evm.Instr := compileVal 0 checkedSum

def comparisonBytes : Option (List UInt8) :=
  match stage comparisonCode 0 with | .ok accepted => some accepted.bytes | .error _ => none

/-! ## Kernel-checked measurements -/

open Family in
theorem whole_scope_measure : wholeScope = some ⟨145, 57, some (1, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem call_scope_measure : callScope = some ⟨83, 35, some (0, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem memory_call_measure : memoryCall = some ⟨83, 35, some (0, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem scoped_argument_measure : scopedArgument = some ⟨78, 31, some (1, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem scoped_body_measure : scopedBody = some ⟨70, 28, some (1, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem fixed_boolean_measure : fixedBoolean = some ⟨84, 38, some (0, fixedMemory),
    [fixedMemory, skipJump, stackMemory, revert], false⟩ := by decide +kernel
open Family in
theorem fresh_boolean_measure (b : Bool) : freshBoolean b = some ⟨157, 69, some (1, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by cases b <;> decide +kernel
open Family in
theorem related_storage_measure : relatedStorage = some ⟨2, 2, some (0, fixedMemory),
    [fixedMemory], false⟩ := by decide +kernel
open Family in
theorem loop_scope_measure : loopScope = some ⟨1, 1, some (0, loop), [loop], false⟩ := by
  decide +kernel
open Family in
theorem loop_call_measure : loopCall = some ⟨116, 45, some (0, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem deferred_panic_measure : deferredPanic = some ⟨3, 2, some (1, skipJump),
    [skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem reuse_scalar_measure : reuseScalar = some ⟨54, 23, some (0, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem reuse_alias_measure : reuseAlias = some ⟨18, 10, some (0, fixedMemory),
    [fixedMemory, stackMemory], false⟩ := by decide +kernel
open Family in
theorem reuse_void_measure : reuseVoid = some ⟨62, 23, some (0, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
open Family in
theorem reuse_wrong_measure : reuseWrong = some ⟨54, 23, some (0, fixedMemory),
    [fixedMemory, stackMemory, skipJump, revert], false⟩ := by decide +kernel
theorem empty_measure : empty = some ⟨0, 0, none, [], true⟩ := by decide +kernel

theorem comparison_measure : measure comparisonCode = ⟨5, 0, none, [], true⟩ := by decide +kernel
open Family in
theorem checked_measure : measure checkedCode =
    ⟨12, 2, some (8, skipJump), [skipJump, revert], false⟩ := by decide +kernel

/-! ## The accepted fragment is inhabited and its bytes run -/

def comparisonProgram : Program :=
  [Scalar.pushWord 2, Scalar.pushWord 3, .op .ADD, Scalar.pushWord 9, .op .GT]

theorem comparison_selected : compileScalar comparisonCode = some comparisonProgram := by
  decide +kernel

/-- The executed bytes are exactly the encoding of the selected program. -/
theorem comparison_bytes : comparisonBytes = some (encode comparisonProgram) ∧
    (encode comparisonProgram).length = 101 := by decide +kernel

/-- `Evm.run` of the compiled fragment pushes `1` (`5 < 9`). -/
theorem comparison_run (m : Evm.Machine) (stack : m.stack = []) :
    Evm.run comparisonCode m = .ok { m with stack := irStack [1] } 0 := by
  rw [compileScalar_equation comparisonCode comparisonProgram comparison_selected [] m stack]
  have actual : Scalar.run comparisonProgram [] = some [1] := by decide +kernel
  rw [actual]

/-- Hence the stage's accepted bytes have a stack-safe byte trace ending at
their end PC with `1`, from every machine with an empty stack. -/
theorem comparison_executes (m : Evm.Machine) (stack : m.stack = []) :
    ∃ accepted, stage comparisonCode 0 = .ok accepted ∧
      ∃ count, ExecutionTrace.Safe accepted.bytes count ⟨0, []⟩ ⟨accepted.finish, [1]⟩ := by
  obtain ⟨accepted, staged⟩ := measure_accepted comparisonCode
    (by rw [comparison_measure])
  exact ⟨accepted, staged,
    (accepted.success_iff [] [1] rfl m stack).mp (comparison_run m stack)⟩

#print axioms measure_accepted
#print axioms whole_scope_measure
#print axioms empty_measure
#print axioms comparison_measure
#print axioms checked_measure
#print axioms comparison_selected
#print axioms comparison_bytes
#print axioms comparison_run
#print axioms comparison_executes

end Solidity.Backend.Passes.Bytes
