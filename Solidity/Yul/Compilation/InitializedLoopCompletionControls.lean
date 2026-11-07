import Solidity.Yul.Compilation.InitializedLoopCompletion
import Solidity.Yul.Compilation.SourceLoopInitializerControls
/-! Concrete non-skip initializer recovery, arbitrary old counter/raw second
word, and exhaustion/underflow/accessibility controls. No native claim. -/
namespace Solidity.Yul.Compilation.InitializedLoopCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root test body condition post dirty work step)
open SourceLoopInitializer.Controls

/-- Recovery from the concrete compiled target, with no source-run input. The
initializer overwrites any old counter, before both actual body/post turns. -/
theorem recovered (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ fuel, evalStmt fuel .nil True.intro source profile (sourceLocals #v[a,b]) =
   some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ :=
 (completion_iff (c := root) initial condition post body 0 block code
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   #v[a,b] #v[0,~~~(~~~b+3)+3] #v[] m caller).mpr (target_done a b m caller)

/-- Actual successful whole target execution determines source completion,
normal final words, pending zero and every unchanged caller/machine field. -/
theorem reflected (a b : Scalar.Word) (m final : Evm.Machine) (caller : List Evm.Word)
 (skip : Nat) (ran : Evm.run code {m with stack := [coreWord a,coreWord b]++caller} = .ok final skip) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word 2),
 evalStmt fuel .nil True.intro source profile (sourceLocals #v[a,b]) =
   some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source (c := root) initial condition post body 0 block code
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   #v[a,b] #v[] m final caller skip ran

def initProgram := (initial.lowered.code 0).get (by rfl)
#guard Scalar.run initProgram [] = none
#guard Scalar.run initProgram [99,dirty] = some [2,dirty]
#guard (SourceLoopInitializer.emit (c := root) initial condition post body 15).isNone
#guard (evalStmt 0 .nil True.intro source profile (sourceLocals #v[99,dirty])).isNone
#guard SourceLoop.next (c := root) body post #v[2,dirty] = #v[1,~~~dirty+3]
/-- info: 'Solidity.Yul.Compilation.InitializedLoopCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.InitializedLoopCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
end Solidity.Yul.Compilation.InitializedLoopCompletion.Controls
