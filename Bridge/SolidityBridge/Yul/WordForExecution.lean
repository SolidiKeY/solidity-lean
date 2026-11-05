import SolidityBridge.Yul.NormalFor
import Solidity.Yul.Compilation.WhileWordExecution
/-! Whole original normal FOR source/model composition for the existing
WordControl selector. Reuses NormalFor source/emit and concrete loop execution,
without an abstract realization or assumed target run. Normal-flow certificates,
horizon bounds and reached guards remain explicit; native/Source/G24 gaps remain. -/
namespace SolidityBridge.Yul.WordForExecution
open Solidity Backend Scalar
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n af cf pf bf : Nat}
 {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {condition : Solidity.Yul.Expr [] [] n 1}
 {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
 (test : ProducerExpressions.Compiled cf condition)
 (after : ProducerStatements.Compiled pf post)
 (inside : ProducerStatements.Compiled bf body)
 (before : ProducerStatements.Compiled af pre)

/-- Actual prelude once and actual body-before-post loop execution. -/
theorem model (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : NormalFor.emit test after inside before depth = some block)
 (selected : WordControl.blockCode block = some code)
 (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word)
 (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l))
   j (before.update locals)) ≠ 0)
 (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l))
   count (before.update locals)) = 0) :
 Evm.run code {m with stack := (newer.toList++locals.toList).map MachineAdapter.coreWord++caller} =
 .ok {m with stack := (newer.toList++(Nat.repeat (fun l => after.update (inside.update l))
   count (before.update locals)).toList).map MachineAdapter.coreWord++caller} 0 := by
 unfold NormalFor.emit at emitted
 cases ha : before.lowered.code depth with
 | none => simp only [ha] at emitted; cases emitted
 | some pp =>
   cases hl : lowerWhile test.lowered (lowerSeq inside.lowered after.lowered) depth with
   | none => simp only [ha,hl] at emitted; cases emitted
   | some loop =>
     simp only [ha,hl] at emitted
     have same : Backend.Block.seq (.code pp) loop = block := Option.some.inj emitted
     subst block
     change ((WordMachine.selectCode pp).bind (fun qp =>
       (WordControl.blockCode loop).map (fun ql => qp++ql))) = some code at selected
     cases sp : WordMachine.selectCode pp with
     | none => simp only [sp,Option.bind_none] at selected; cases selected
     | some qp =>
       cases sl : WordControl.blockCode loop with
       | none => simp only [sp,sl,Option.bind_some,Option.map_none] at selected; cases selected
       | some ql =>
         simp only [sp,sl,Option.bind_some,Option.map_some,Option.some.injEq] at selected
         subst code
         rw [Evm.run_append_ok (WordExecution.loweredStmt_machine before.lowered depth pp qp
           ha sp locals newer m caller)]
         exact WhileWordExecution.lowered test.lowered (lowerSeq inside.lowered after.lowered)
           loop ql hl sl count (before.update locals) newer m caller running stopped

/-- Complete original closed-Yul FOR evaluation and actual selected model run
share the same update. Horizon bounds are real source premises, not gas budgets. -/
theorem source_model (base count : Nat) (ha : af ≤ base) (hc : cf ≤ base)
    (hp : pf ≤ base) (hb : bf ≤ base)
    (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
    (emitted : NormalFor.emit test after inside before depth = some block)
    (selected : WordControl.blockCode block = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l))
      j (before.update locals)) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after.update (inside.update l))
      count (before.update locals)) = 0) :
    (evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
      (NormalFor.profile test after inside before) (sourceLocals locals) =
      some ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l))
        count (before.update locals)),.normal⟩) ∧
    Evm.run code {m with stack := (newer.toList++locals.toList).map MachineAdapter.coreWord++caller} =
      .ok {m with stack := (newer.toList++(Nat.repeat (fun l => after.update (inside.update l))
        count (before.update locals)).toList).map MachineAdapter.coreWord++caller} 0 :=
  ⟨NormalFor.source test after inside before base count ha hc hp hb locals running stopped,
   model test after inside before depth block code emitted selected count locals newer m caller running stopped⟩

/-- info: 'SolidityBridge.Yul.WordForExecution.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model
/-- info: 'SolidityBridge.Yul.WordForExecution.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_model
end
end SolidityBridge.Yul.WordForExecution
