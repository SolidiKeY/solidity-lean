import Solidity.Backend.Selection.BranchExecution
import Solidity.Backend.Selection.LoopExecution

/-! Realization for the existing shaped structured fragment. -/
namespace Solidity.Backend.Selection.ExecutionTrace

/-- Every existing block shape with its required expansion room obtains an
actual whole-byte control certificate, including arbitrary nested loop bodies. -/
def structuredCertificate (block : Block) {n m : Nat}
    (shape : LabelExec.BlockShape block n m) (room : ExpansionRoom block n m) :
    ControlCertificate block n m := by
  induction block generalizing n m with
  | code instructions =>
    cases shape with
    | code code => exact codeCertificate code
  | seq left right ihLeft ihRight =>
    rcases room with ⟨middle,leftShape,rightShape,leftRoom,rightRoom⟩
    exact seqCertificate (ihLeft leftShape leftRoom) (ihRight rightShape rightRoom)
  | ite condition left right ihLeft ihRight =>
    cases shape with
    | @ite n m condition left right leftShape rightShape testRoom =>
      exact iteCertificate condition (ihLeft leftShape room.1)
        (ihRight rightShape room.2.1) testRoom room.2.2
  | loop condition body ih =>
    cases shape with
    | @loop n condition body bodyShape testRoom =>
      exact loopCertificate condition (ih bodyShape room) testRoom

#print axioms structuredCertificate

end Solidity.Backend.Selection.ExecutionTrace
