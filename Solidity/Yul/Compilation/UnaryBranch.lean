import Solidity.Yul.Compilation.UnaryMachine
import Solidity.Yul.Compilation.NormalControl
/-! Concrete original-source zero-test branch using actual compiler outputs.
No general branch/native/Source-G24 closure is inferred from this slice. -/
namespace Solidity.Yul.Compilation.UnaryBranch
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def root : Control := ⟨false,false⟩
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def source : Stmt [] [] root 1 := .if_ UnaryMachine.iszeroExpr
  (.assign (fun _ : Fin 1 => .local 0) (.literal (word (2^200+257))))
def compiled := (NormalControl.compile 3 source).get (by rfl)
def lowered := (compiled.emit 0).get (by rfl)
def model := (WordControl.blockCode lowered).get (by rfl)

/-- Exact image of the actual compiler/selector output. -/
theorem model_shape : model = MachineControl.branchCode [.dup 1,.iszero]
    [.push (coreWord dirty),.swap 1,.pop] [] := rfl

/-- Whole actual selected branch, all input words and arbitrary machine/caller.
Zero writes the full dirty constant; every nonzero word is retained unchanged. -/
theorem model_run (a : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run model {m with stack := coreWord a :: tail} =
      .ok {m with stack := coreWord (if a = 0 then dirty else a) :: tail} 0 := by
  change Evm.run [.iszero,.jumpi 1,.jump 3,.push (coreWord dirty),.swap 1,.pop]
    {m with stack := coreWord a :: coreWord a :: tail} = _
  by_cases z : a = 0
  · subst a
    rfl
  · have nz : a.toNat ≠ 0 := fun h => z (BitVec.eq_of_toNat_eq h)
    simp only [Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
      coreWord,Evm.bword,decide_eq_false_iff_not.mpr nz,Bool.false_eq_true,
      if_neg z,↓reduceIte]
#print axioms model_run
end Solidity.Yul.Compilation.UnaryBranch
