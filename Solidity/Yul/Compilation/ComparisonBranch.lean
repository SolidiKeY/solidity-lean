import Solidity.Yul.Compilation.ComparisonMachine
import Solidity.Yul.Compilation.NormalControl
/-! Concrete two-local unsigned comparison branch from the original source.
No general branch/native/Source-G24 closure is inferred. -/
namespace Solidity.Yul.Compilation.ComparisonBranch
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def root : Control := ⟨false,false⟩
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def source : Stmt [] [] root 2 := .if_ ComparisonMachine.ltExpr
  (.assign (fun _ : Fin 1 => .local 1) (.literal (word (2^200+257))))
def compiled := (NormalControl.compile 3 source).get (by rfl)
def lowered := (compiled.emit 0).get (by rfl)
def model := (WordControl.blockCode lowered).get (by rfl)

theorem model_shape : model = MachineControl.branchCode [.dup 2,.dup 2,.lt]
    [.push (coreWord dirty),.swap 2,.pop] [] := rfl

/-- Actual whole selected branch, all input pairs and arbitrary machine/caller.
The first local is framed; only a true unsigned test changes the second. -/
theorem model_run (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run model {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord a :: coreWord (if a.toNat < b.toNat then dirty else b) :: tail} 0 := by
  change Evm.run [.lt,.jumpi 1,.jump 3,.push (coreWord dirty),.swap 2,.pop]
    {m with stack := coreWord a :: coreWord b :: coreWord a :: coreWord b :: tail} = _
  by_cases h : a.toNat < b.toNat <;>
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Evm.bword,h,decide_true,decide_false,↓reduceIte] <;> rfl
#print axioms model_run
end Solidity.Yul.Compilation.ComparisonBranch
