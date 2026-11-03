import SolidityBridge.Yul.OccurrenceSelection
import SolidityBridge.Yul.ControlCompleteness
/-! Structured selection over the EXISTING Backend.Block and published
Realization/Classified contracts. Proof packages, not new block syntax or
semantics. Native byte/PC/capacity/source-G24 closure remains separate. -/
namespace SolidityBridge.Yul.OccurrenceControl
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter
open ControlRealization ControlCompleteness

structure Selected (block : Backend.Block) where
  realization : Realization block
  classified : Classified realization

def scalar {p : Backend.Program} (slice : OccurrenceSelection.Slice p) : Realization (.code p) :=
  ⟨slice.ir,fun input output m represented executed =>
    ((OccurrenceSelection.lowering p slice).success input output m represented).mpr executed⟩

theorem scalar_classified :
∀ (p : Solidity.Backend.Program) (slice : SolidityBridge.Yul.OccurrenceSelection.Slice p),
 SolidityBridge.Yul.ControlCompleteness.Classified (SolidityBridge.Yul.OccurrenceControl.scalar slice) := by
  intro p slice input m represented
  have law := SolidityBridge.Yul.OccurrenceSelection.execute slice.ir slice.certificates input m represented
  rw [slice.origin] at law
  cases executed : Solidity.Backend.Scalar.run p input with
  | none =>
    left
    simpa only [executed] using law
  | some output =>
    right
    exact ⟨output,Solidity.Backend.Selection.StructuredExec.code executed,by simpa only [executed] using law⟩

def conditional (c : Backend.Program) (a b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (yes : Realization a) (no : Realization b) :
    Realization (.ite c a b) := by
  refine ⟨Solidity.Yul.Compilation.MachineControl.branchCode test.ir yes.ir no.ir,?_⟩
  intro input output m represented executed
  cases executed with
  | @iteTrue _ _ _ _ middle _ w condition nonzero body =>
    have testRun := ((SolidityBridge.Yul.OccurrenceSelection.lowering c test).success _ _ m represented).mpr
      (Solidity.Backend.Selection.StructuredExec.code condition)
    rw [SolidityBridge.Yul.QuotientSelection.stack_cons] at testRun
    rw [Solidity.Yul.Compilation.MachineControl.branchCode,Solidity.Evm.run_append_ok testRun]
    have nz : w.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
    exact SolidityBridge.Yul.ControlRealization.branch_true ⟨w.toNat,w.isLt⟩ yes.ir no.ir
      {m with stack := Solidity.Backend.Selection.irStack middle} {m with stack := Solidity.Backend.Selection.irStack output} nz
      (yes.execute _ _ {m with stack := Solidity.Backend.Selection.irStack middle} rfl body)
  | @iteFalse _ _ _ _ middle _ condition body =>
    have testRun := ((SolidityBridge.Yul.OccurrenceSelection.lowering c test).success _ _ m represented).mpr
      (Solidity.Backend.Selection.StructuredExec.code condition)
    rw [SolidityBridge.Yul.QuotientSelection.stack_cons] at testRun
    rw [Solidity.Yul.Compilation.MachineControl.branchCode,Solidity.Evm.run_append_ok testRun]
    exact SolidityBridge.Yul.ControlRealization.branch_false ⟨0,by decide⟩ yes.ir no.ir
      {m with stack := Solidity.Backend.Selection.irStack middle} {m with stack := Solidity.Backend.Selection.irStack output} rfl
      (no.execute _ _ {m with stack := Solidity.Backend.Selection.irStack middle} rfl body)

theorem conditional_classified :
∀ (c : Solidity.Backend.Program) (a b : Solidity.Backend.Block)
 (test : SolidityBridge.Yul.OccurrenceSelection.Slice c)
 (yes : SolidityBridge.Yul.ControlRealization.Realization a)
 (no : SolidityBridge.Yul.ControlRealization.Realization b),
 SolidityBridge.Yul.ControlCompleteness.Classified yes →
 SolidityBridge.Yul.ControlCompleteness.Classified no →
 SolidityBridge.Yul.ControlCompleteness.Classified
 (SolidityBridge.Yul.OccurrenceControl.conditional c a b test yes no) := by
  intro c a b test yes no yesClass noClass
  intro input m represented
  have law := SolidityBridge.Yul.OccurrenceSelection.execute test.ir test.certificates input m represented
  rw [test.origin] at law
  cases tested : Solidity.Backend.Scalar.run c input with
  | none =>
    left
    change Solidity.Evm.run (test.ir ++ Solidity.Yul.Compilation.MachineControl.branchTail yes.ir no.ir) m = .fault
    apply SolidityBridge.Yul.ControlCompleteness.append_fault
    simpa only [tested] using law
  | some stack =>
    rw [tested] at law
    change Solidity.Evm.run test.ir m = .ok {m with stack := Solidity.Backend.Selection.irStack stack} 0 at law
    cases stack with
    | nil =>
      left
      change Solidity.Evm.run (test.ir ++ Solidity.Yul.Compilation.MachineControl.branchTail yes.ir no.ir) m = .fault
      rw [Solidity.Evm.run_append_ok law]
      rfl
    | cons w middle =>
      rw [SolidityBridge.Yul.ArithmeticSelection.irStack_words (w::middle),List.map_cons,
        ←SolidityBridge.Yul.ArithmeticSelection.irStack_words middle] at law
      by_cases zero : w = 0
      · subst w
        rcases noClass middle {m with stack := Solidity.Backend.Selection.irStack middle} rfl with fault | ⟨output,body,ran⟩
        · left
          change Solidity.Evm.run (test.ir ++ Solidity.Yul.Compilation.MachineControl.branchTail yes.ir no.ir) m = .fault
          rw [Solidity.Evm.run_append_ok law]
          exact SolidityBridge.Yul.ControlCompleteness.false_fault ⟨0,by decide⟩ yes.ir no.ir {m with stack := Solidity.Backend.Selection.irStack middle} rfl fault
        · right
          refine ⟨output,Solidity.Backend.Selection.StructuredExec.iteFalse tested body,?_⟩
          change Solidity.Evm.run (test.ir ++ Solidity.Yul.Compilation.MachineControl.branchTail yes.ir no.ir) m = _
          rw [Solidity.Evm.run_append_ok law]
          exact SolidityBridge.Yul.ControlRealization.branch_false ⟨0,by decide⟩ yes.ir no.ir
            {m with stack := Solidity.Backend.Selection.irStack middle} {m with stack := Solidity.Backend.Selection.irStack output} rfl ran
      · have nz : w.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
        rcases yesClass middle {m with stack := Solidity.Backend.Selection.irStack middle} rfl with fault | ⟨output,body,ran⟩
        · left
          change Solidity.Evm.run (test.ir ++ Solidity.Yul.Compilation.MachineControl.branchTail yes.ir no.ir) m = .fault
          rw [Solidity.Evm.run_append_ok law]
          exact (SolidityBridge.Yul.ControlCompleteness.true_out ⟨w.toNat,w.isLt⟩ yes.ir no.ir {m with stack := Solidity.Backend.Selection.irStack middle} nz).trans fault
        · right
          refine ⟨output,Solidity.Backend.Selection.StructuredExec.iteTrue tested zero body,?_⟩
          change Solidity.Evm.run (test.ir ++ Solidity.Yul.Compilation.MachineControl.branchTail yes.ir no.ir) m = _
          rw [Solidity.Evm.run_append_ok law]
          exact (SolidityBridge.Yul.ControlCompleteness.true_out ⟨w.toNat,w.isLt⟩ yes.ir no.ir {m with stack := Solidity.Backend.Selection.irStack middle} nz).trans ran

def leaf {p : Backend.Program} (slice : OccurrenceSelection.Slice p) : Selected (.code p) :=
  ⟨scalar slice,scalar_classified p slice⟩

def combine {a b : Backend.Block} (left : Selected a) (right : Selected b) : Selected (.seq a b) :=
  ⟨ControlRealization.sequence left.realization right.realization,
    ControlCompleteness.sequence_classified left.realization right.realization left.classified right.classified⟩

def branch {c : Backend.Program} {a b : Backend.Block} (test : OccurrenceSelection.Slice c)
    (yes : Selected a) (no : Selected b) : Selected (.ite c a b) :=
  ⟨conditional c a b test yes.realization no.realization,
    conditional_classified c a b test yes.realization no.realization yes.classified no.classified⟩

/-- Classification is constructed with each real successful selection. -/
def selectBlock : (block : Backend.Block) → Option (Selected block)
  | .code p => (OccurrenceSelection.selectCode p).map leaf
  | .seq a b => do
      let left ← selectBlock a
      let right ← selectBlock b
      pure (combine left right)
  | .ite c a b => do
      let test ← OccurrenceSelection.selectCode c
      let yes ← selectBlock a
      let no ← selectBlock b
      pure (branch test yes no)
  | .loop _ _ => none

def Selected.lowering {block : Backend.Block} (selected : Selected block) :
    LoweringCertificate selected.realization.ir block :=
  ControlCompleteness.lowering selected.realization selected.classified

def byteAt (index : Solidity.Yul.Word) : Solidity.Yul.Expr [] [] 3 1 :=
  .builtin (.pure .byte) (Fin.cases (.literal index) (fun _ => .local 1))
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .seq (.assign (fun _ : Fin 1 => .local 0) (byteAt (Solidity.Yul.word 0)))
    (UnarySelection.assignment 2 .iszero 0)
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .if_ (byteAt (Solidity.Yul.word 31)) body

def compiled := (NormalControl.compile 5 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (selectBlock block).get (by rfl)
def lowering := selected.lowering
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected.realization

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (selectBlock prefixedBlock).get (by rfl)
def prefixed_lowering := prefixed.lowering
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed.realization

theorem fault_iff :
∀ (block : Solidity.Backend.Block) (selected : SolidityBridge.Yul.OccurrenceControl.Selected block)
 (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack input →
 (Solidity.Evm.run selected.realization.ir m = .fault ↔
   ¬ ∃ output, Solidity.Backend.Selection.StructuredExec block input output) := by
  intro block selected input m represented
  constructor
  · intro fault successful
    obtain ⟨output,executed⟩ := successful
    have ran := selected.realization.execute input output m represented executed
    have impossible : Solidity.Evm.Out.fault = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 := fault.symm.trans ran
    cases impossible
  · intro refused
    rcases selected.classified input m represented with fault | ⟨output,executed,_ran⟩
    · exact fault
    · exact False.elim (refused ⟨output,executed⟩)

end SolidityBridge.Yul.OccurrenceControl
