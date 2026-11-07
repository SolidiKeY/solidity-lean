import Solidity.Backend.Passes.CoreBoundary
import Solidity.Backend.Passes.ReframedSequence
import Solidity.Backend.Passes.MemoryCallControls

/-! A single actual core-compiler input/output point. This fixture only supplies
joint hypotheses to generic transport statements; the allocating success family
in Audit remains the nontrivial compiler-adequacy control. -/
namespace H62.CompilerTransport.NilFixture
open Solidity Solidity.Evm Solidity.Evm.Compiler Solidity.Backend.Passes
open MemoryCallControls (C initial base machine)

def context : Ctx := []
def zero : Nat := 0
def one : Nat := 1
def frame : Nat := 128
def tail : List Word := []
def fragment : Frag [] := Frag.init []
def program : Prog C [] [] := .nil
def compiled : Compilation 1 fragment program := .core fragment rfl
def output : Solidity.Out C initial.H [] := ⟨initial,List.prefix_refl _⟩

theorem sim : Sim C 1 1 fragment initial machine := MemoryCallControls.initial_repr.1.core

theorem input : compiled.Input 1 128 base initial machine := ⟨sim,by decide⟩
theorem source_run : program.run initial = .ok output := rfl
theorem target_run : run compiled.code machine = .ok machine 0 := rfl

theorem mapped : MappedOutput compiled 1 128 base initial machine initial machine base :=
  ⟨rfl,sim⟩
theorem represented : compiled.Rep 1 128 base initial machine initial machine := sim

theorem recognized : inFragP fragment program = some fragment := rfl
theorem payment_free : Evm.Prog.pays program = false := rfl
theorem push_free : Evm.Prog.pushes program = 0 := rfl
theorem capacity : (1 + Evm.Prog.pushes program) + Evm.Prog.pushes program ≤ Lmax := by decide

theorem link : BoundaryLink compiled compiled 1 128 base base initial machine :=
  compilation_core_link compiled recognized capacity

theorem mapped_link : MappedBoundaryLink compiled compiled 1 128 base initial machine :=
  compilation_core_mapped_link compiled recognized capacity

theorem reframed_link : ReframedLink compiled compiled 1 128 128 base initial machine :=
  mapped_link

theorem overbudget : Lmax < (Lmax + 1) + Evm.Prog.pushes program := Nat.lt_succ_self Lmax

#print axioms input
#print axioms mapped
#print axioms link
#print axioms reframed_link
end H62.CompilerTransport.NilFixture
