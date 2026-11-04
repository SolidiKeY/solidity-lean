import Solidity.Yul.Compilation.P20InterfaceV1

/-! A real nontrivial closed producer witnesses the reused part only.
No PendingG24 or PendingRepresentedSuccess instance is constructed. -/
namespace Solidity.Yul.Compilation.P20.InterfaceV1.Controls
open Backend Scalar ProducerExpressions

def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 1) (.literal dirty.toFin)
def producer : ClosedProducer 2 statement :=
  ProducerStatements.assignTargets (fun _ : Fin 1 => .local 1) (ProducerExpressions.literal 0 dirty.toFin)

#guard producer.update #v[9,0] == #v[9,dirty]
#check producer.source
#check producer.lowered.correct
#check PendingG24
#check PendingRepresentedSuccess
/-- info: 'Solidity.Yul.Compilation.P20.InterfaceV1.Controls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms producer
end Solidity.Yul.Compilation.P20.InterfaceV1.Controls
