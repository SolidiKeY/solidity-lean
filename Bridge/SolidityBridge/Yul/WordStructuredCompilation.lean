import SolidityBridge.Yul.ScopedFor
import Solidity.Yul.Compilation.WordBlockExecution
/-! Concrete existing-word-selector consumers for actual scope/switch and
scope/switch FOR compiler certificates. No assumed model run or selected
realization callback; original source indices/profiles and guards stay intact.
Only forward finite normal execution, not native/Source/G24 adequacy. -/
namespace SolidityBridge.Yul.WordStructuredCompilation
open Solidity Backend Scalar
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions MachineAdapter

/-- Original scope/switch certificate supplies its actual structured run. -/
theorem nested_model {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : NestedSwitch.Compiled fuel stmt) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit = some block) (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (compiled.update locals).toList.map coreWord++caller} 0 := by
 have actual := compiled.structured block emitted locals []
 simp only [List.append_nil] at actual
 exact WordBlockExecution.execute actual code selected m caller

/-- The actual visitor, original evaluator and concrete target share an update. -/
theorem nested_source_model {c n fuel} (stmt : Stmt [] [] c n)
 (compiled : NestedSwitch.Compiled fuel stmt)
 (_visited : NestedSwitch.compile fuel stmt = some compiled)
 (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit = some block) (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word) :
 (evalStmt fuel .nil True.intro stmt compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals (compiled.update locals),.normal⟩) ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (compiled.update locals).toList.map coreWord++caller} 0 :=
 ⟨compiled.source locals,nested_model compiled block code emitted selected locals m caller⟩

section
variable {c : Solidity.Yul.Control} {n fuel : Nat}
 {pre : Stmt [] [] ⟨c.function,false⟩ n} {condition : Expr [] [] n 1}
 {post : Stmt [] [] ⟨c.function,false⟩ n} {body : Stmt [] [] ⟨c.function,true⟩ n}
 (compiled : ScopedFor.Prepared fuel (c := c) pre condition post body)

/-- Scopes/switches within FOR components use their existing compiler proof;
the concrete selector itself supplies the target model transport. -/
theorem scoped_for_model (block : Backend.Block) (code : List Evm.Instr)
 (emitted : ScopedFor.emit compiled = some block) (selected : WordControl.blockCode block = some code)
 (count : Nat) (locals : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word)
 (running : ∀ j, j < count → compiled.test.value
   (Nat.repeat (ScopedFor.update compiled) j (compiled.before.update locals)) ≠ 0)
 (stopped : compiled.test.value (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)) = 0) :
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (Nat.repeat (ScopedFor.update compiled) count
   (compiled.before.update locals)).toList.map coreWord++caller} 0 := by
 have actual := ScopedFor.structured compiled block emitted count locals [] running stopped
 simp only [List.append_nil] at actual
 exact WordBlockExecution.execute actual code selected m caller

/-- Whole original FOR evaluation with actual lexical scopes/switches agrees
with the selected model. Normal-flow, horizon and reached guards stay explicit. -/
theorem scoped_for_source_model (base count : Nat) (bounded : fuel ≤ base)
 (block : Backend.Block) (code : List Evm.Instr)
 (emitted : ScopedFor.emit compiled = some block) (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word)
 (running : ∀ j, j < count → compiled.test.value
   (Nat.repeat (ScopedFor.update compiled) j (compiled.before.update locals)) ≠ 0)
 (stopped : compiled.test.value (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)) = 0) :
 (evalStmt (base+(count+2)) .nil True.intro (.for_ (c := c) pre condition post body)
   (ScopedFor.profile compiled) (sourceLocals locals) =
   some ⟨sourceLocals (Nat.repeat (ScopedFor.update compiled) count
     (compiled.before.update locals)),.normal⟩) ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (Nat.repeat (ScopedFor.update compiled) count
   (compiled.before.update locals)).toList.map coreWord++caller} 0 :=
 ⟨ScopedFor.source compiled base count bounded locals running stopped,
  scoped_for_model compiled block code emitted selected count locals m caller running stopped⟩
end

/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.nested_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_model
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.nested_source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_source_model
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.scoped_for_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scoped_for_model
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.scoped_for_source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scoped_for_source_model
end SolidityBridge.Yul.WordStructuredCompilation
