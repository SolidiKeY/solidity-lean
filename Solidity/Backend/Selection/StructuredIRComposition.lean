import Solidity.Backend.Selection.IRBranchLowering
import Solidity.Backend.Selection.IRLoopLowering
import Solidity.Backend.Selection.Composition

/-! Actual structured-IR lowering producers feed the existing assembly
composition. The assembler may refuse its own checked layout; no bytes or
successful whole-IR behavior are supplied as an unproved premise. -/
namespace Solidity.Backend.Selection

def assembleComposition {ir : List Evm.Instr} {block : Block} {n m : Nat}
    (lowering : FramedLoweringCertificate ir block)
    (shape : LabelExec.BlockShape block n m) (room : ExpansionRoom block n m) :
    Option (CompositionCertificate ir block n m) :=
  match actual : assemble 0 LabelExec.emptyLink (block.expand 0).1 with
  | none => none
  | some out => some (compose lowering.toLoweringCertificate shape room out actual)

theorem assembleComposition_isSome {ir : List Evm.Instr} {block : Block} {n m : Nat}
    (lowering : FramedLoweringCertificate ir block)
    (shape : LabelExec.BlockShape block n m) (room : ExpansionRoom block n m)
    (fits : ∀ label ∈ refs (block.expand 0).1,
      0 + tagOffset (fun _ => (32 : Fin 33)) (block.expand 0).1 label < 256 ^ 32) :
    (assembleComposition lowering shape room).isSome := by
  have existsOut : (assemble 0 LabelExec.emptyLink (block.expand 0).1).isSome :=
    Block.expand_assemble_isSome block 0 0 LabelExec.emptyLink fits
  unfold assembleComposition
  split
  next actual => simp only [actual, Option.isSome_none, Bool.false_eq_true] at existsOut
  next out actual => rfl

#print axioms assembleComposition
#print axioms assembleComposition_isSome

end Solidity.Backend.Selection
