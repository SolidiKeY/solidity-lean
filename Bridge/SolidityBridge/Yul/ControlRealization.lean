import SolidityBridge.Yul.LiteralSelection
import SolidityBridge.Yul.StructuredSource
import Solidity.Yul.Compilation.MachineControl
/-! Checked numeric model selection for existing Backend.Block. The package is
indexed by that existing block, with no replacement syntax or evaluator.
Exact scalar-leaf certificates and forward structured realization are proved
here; ControlCompleteness supplies the whole selected-block iff separately.
Native byte execution, capacity and Source/G24 remain separate obligations. -/
namespace SolidityBridge.Yul.ControlRealization
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

/-- An actual list of instruction certificates, checked against the SAME scalar
program. Exact equality refuses erased PUSH widths that would change bytes. -/
structure Slice (code : Backend.Program) where
  ir : List Evm.Instr
  certificates : SelectionSequence.Certificates ir
  origin : SelectionSequence.emit ir certificates = code

/-- Refuses both unproved instruction selections and unequal re-encodings. -/
def selectSliceUsing (choose : Backend.Program → Option (List Evm.Instr))
    (table : (i : Evm.Instr) → Option (InstructionCertificate i))
    (code : Backend.Program) : Option (Slice code) := do
  let ir ← choose code
  if available : ir.all (fun i => (table i).isSome) = true then
    let pick : SelectionSequence.Certificates ir := fun i member =>
      (table i).get (List.all_eq_true.mp available i member)
    if origin : SelectionSequence.emit ir pick = code then
      some ⟨ir,pick,origin⟩
    else none
  else none

/-- The original numeric candidate generator and table contract are retained. -/
def selectSliceWith (table : (i : Evm.Instr) → Option (InstructionCertificate i))
    (code : Backend.Program) : Option (Slice code) :=
  selectSliceUsing NumericMachine.selectCode table code

/-- Legacy entry point retains its original concrete table and verdicts. -/
def selectSlice (code : Backend.Program) : Option (Slice code) :=
  selectSliceWith LiteralSelection.select code

/-- Successful realization of an existing block. This forward-only package
must not be substituted for Selection.LoweringCertificate (which asks iff). -/
structure Realization (block : Backend.Block) where
  ir : List Evm.Instr
  execute : ∀ (input output : Scalar.Stack) (m : Evm.Machine),
    m.stack = irStack input → StructuredExec block input output →
    Evm.run ir m = .ok {m with stack := irStack output} 0

theorem branch_true (condition : Fin Evm.W) (yes no : List Evm.Instr)
    (m out : Evm.Machine) (nonzero : condition.val ≠ 0)
    (body : Evm.run yes m = .ok out 0) :
    Evm.run (MachineControl.branchTail yes no) {m with stack := .val condition :: m.stack} = .ok out 0 := by
  simp only [MachineControl.branchTail,Evm.run,Evm.exec_cons_zero,Evm.Instr.step,
    nonzero,ite_false,Evm.Out.ok_bind]
  rw [Evm.exec_skip_append]
  exact body

theorem branch_false (condition : Fin Evm.W) (yes no : List Evm.Instr)
    (m out : Evm.Machine) (zero : condition.val = 0)
    (body : Evm.run no m = .ok out 0) :
    Evm.run (MachineControl.branchTail yes no) {m with stack := .val condition :: m.stack} = .ok out 0 := by
  simp only [MachineControl.branchTail,Evm.run,Evm.exec_cons_zero,Evm.Instr.step,
    zero,ite_true,Evm.Out.ok_bind]
  change Evm.run (no ++ (.jump yes.length :: yes)) m = _
  rw [Evm.run_append_ok body]
  exact Evm.exec_length yes out

theorem Slice.execute {code : Backend.Program} (slice : Slice code)
    (input output : Scalar.Stack) (m : Evm.Machine) (represented : m.stack = irStack input)
    (executed : Scalar.run code input = some output) :
    Evm.run slice.ir m = .ok {m with stack := irStack output} 0 := by
  have law := SelectionSequence.execute slice.ir slice.certificates input m represented
  rw [slice.origin,executed] at law
  exact law

/-- The published iff certificate is genuinely discharged for exact scalar
leaves. This does not assert a reverse theorem for sequence/conditional code. -/
def Slice.lowering {code : Backend.Program} (slice : Slice code) :
    Selection.LoweringCertificate slice.ir (.code code) := by
  constructor
  intro input output m represented
  constructor
  · intro ran
    have law := SelectionSequence.execute slice.ir slice.certificates input m represented
    rw [slice.origin] at law
    cases executed : Scalar.run code input with
    | none =>
      rw [executed] at law
      have impossible : Evm.Out.fault = .ok {m with stack := irStack output} 0 := law.symm.trans ran
      cases impossible
    | some actual =>
      rw [executed] at law
      change Evm.run slice.ir m = .ok {m with stack := irStack actual} 0 at law
      have mapped : irStack actual = irStack output :=
        congrArg Evm.Machine.stack (Evm.Out.ok.inj (law.symm.trans ran)).1
      have same : actual = output := ArithmeticSelection.irStack_injective mapped
      exact StructuredExec.code (executed.trans (congrArg some same))
  · intro executed
    cases executed with
    | code run => exact slice.execute input output m represented run

def scalar {code : Backend.Program} (slice : Slice code) : Realization (.code code) :=
  ⟨slice.ir,by
    intro input output m represented executed
    cases executed with
    | code run => exact slice.execute input output m represented run⟩

def sequence {a b : Backend.Block} (left : Realization a) (right : Realization b) :
    Realization (.seq a b) :=
  ⟨left.ir ++ right.ir,by
    intro input output m represented executed
    cases executed with
    | seq first second =>
      rw [Evm.run_append_ok (left.execute _ _ m represented first)]
      exact right.execute _ _ {m with stack := irStack _} rfl second⟩

private theorem irStack_cons (w : Scalar.Word) (s : Scalar.Stack) :
    irStack (w::s) = coreWord w :: irStack s := by
  rw [ArithmeticSelection.irStack_words (w::s),ArithmeticSelection.irStack_words s]
  rfl

/-- Selected-arm-only execution: an untaken arm need not run on these operands. -/
def conditional {c : Backend.Program} {a b : Backend.Block}
    (test : Slice c) (yes : Realization a) (no : Realization b) : Realization (.ite c a b) :=
  ⟨MachineControl.branchCode test.ir yes.ir no.ir,by
    intro input output m represented executed
    cases executed with
    | @iteTrue _ _ _ _ middle _ w condition nonzero body =>
      have testRun := test.execute _ _ m represented condition
      rw [irStack_cons] at testRun
      rw [MachineControl.branchCode,Evm.run_append_ok testRun]
      have nz : w.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
      exact branch_true ⟨w.toNat,w.isLt⟩ yes.ir no.ir
        {m with stack := irStack middle} {m with stack := irStack output} nz
        (yes.execute _ _ {m with stack := irStack middle} rfl body)
    | @iteFalse _ _ _ _ middle _ condition body =>
      have testRun := test.execute _ _ m represented condition
      rw [irStack_cons] at testRun
      rw [MachineControl.branchCode,Evm.run_append_ok testRun]
      exact branch_false ⟨0,by decide⟩ yes.ir no.ir
        {m with stack := irStack middle} {m with stack := irStack output} rfl
        (no.execute _ _ {m with stack := irStack middle} rfl body)⟩

/-- Actual recursive model selection. Loops remain refused; no model loop or
source divergence theorem is assumed. Unsupported scalar certificates refuse. -/
def selectBlockWith (compileLeaf : (p : Backend.Program) → Option (Slice p)) : (block : Backend.Block) → Option (Realization block)
  | .code p => (compileLeaf p).map scalar
  | .seq a b => do
      let left ← selectBlockWith compileLeaf a
      let right ← selectBlockWith compileLeaf b
      pure (sequence left right)
  | .ite c a b => do
      let test ← compileLeaf c
      let yes ← selectBlockWith compileLeaf a
      let no ← selectBlockWith compileLeaf b
      pure (conditional test yes no)
  | .loop _ _ => none

/-- Legacy recursion uses the original leaf compiler without widening it. -/
def selectBlock : (block : Backend.Block) → Option (Realization block) :=
  selectBlockWith selectSlice

/-- Concrete compiler/source/structured/model composition; the actual compiler
emission and numeric machine representation are retained as explicit inputs. -/
theorem source_model :
∀ {c : Solidity.Yul.Control} {n fuel : Nat} {stmt : Solidity.Yul.Stmt [] [] c n}
 (compiled : Solidity.Yul.Compilation.NormalControl.Derivation fuel stmt)
 (depth : Nat) (block : Solidity.Backend.Block), compiled.emit depth = some block →
 ∀ (selected : SolidityBridge.Yul.ControlRealization.Realization block)
 (locals : Vector Solidity.Backend.Scalar.Word n) (newer : Vector Solidity.Backend.Scalar.Word depth)
 (tail : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack (newer.toList ++ (locals.toList ++ tail)) →
 Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt compiled.profile
 (Solidity.Yul.Compilation.ProducerExpressions.sourceLocals locals) =
 some ⟨Solidity.Yul.Compilation.ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩ ∧
 Solidity.Evm.run selected.ir m = .ok {m with stack := Solidity.Backend.Selection.irStack (newer.toList ++ ((compiled.update locals).toList ++ tail))} 0
 := by
  intro c n fuel stmt compiled depth block emitted selected locals newer tail m represented
  exact ⟨compiled.source locals, selected.execute _ _ m represented
    (StructuredSource.structured compiled depth block emitted locals newer tail)⟩

def branchSelected := (selectBlock StructuredSource.block).get (by rfl)
def sequenceSelected := (selectBlock StructuredSource.sequenceBlock).get (by rfl)
def nestedSelected := (selectBlock StructuredSource.nestedBlock).get (by rfl)
def prefixedSelected := (selectBlock StructuredSource.prefixedBlock).get (by rfl)

/-- Actual recursive compiler and selector instances, with all code origins
closed constructively; no target execution or blanket simulation premise. -/
abbrev branch_model := source_model StructuredSource.compiled 0 StructuredSource.block
  (by rfl) branchSelected
abbrev sequence_model := source_model StructuredSource.sequenceCompiled 0 StructuredSource.sequenceBlock
  (by rfl) sequenceSelected
abbrev nested_model := source_model StructuredSource.nestedCompiled 0 StructuredSource.nestedBlock
  (by rfl) nestedSelected
abbrev prefixed_model := source_model StructuredSource.compiled 2 StructuredSource.prefixedBlock
  (by rfl) prefixedSelected

end SolidityBridge.Yul.ControlRealization
