import Solidity.Backend.Passes.HeapApplication

/-! Inhabit the new allocating-construction boundary: allocation is a separate
middle stage, with its reached five-cell budget derived from the source. -/
namespace Solidity.Backend.Passes.AllocatingMiddle
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open Backend.Passes.Controls.Fixture (C)

def firstProgram : Prog C [] [.mem Child] :=
  .cons (.declMem Child (.user "child") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil
def middleProgram : Prog C [.mem Child] Locals :=
  .cons (.declMem Parent (.user "parent") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl) .nil
def firstCode : Construction.CompiledProg 1 (Frag.init []) firstProgram :=
  (Construction.compileProg 1 _ firstProgram).get (by decide +kernel)
def middleCode : Construction.CompiledProg 1 firstCode.frag middleProgram :=
  (Construction.compileProg 1 _ middleProgram).get (by decide +kernel)
def lastCode : ReferenceArrays.CompiledProg 1 middleCode.frag mutate :=
  (ReferenceArrays.compileProg 1 _ mutate).get (by decide +kernel)

def firstOut : Solidity.Out C initial.H [.mem Child] :=
  ⟨HeapPrefix.childState,⟨[Child],rfl⟩⟩
noncomputable def middleOut : Solidity.Out C firstOut.st.H Locals :=
  ⟨first.st,⟨[Child,Child,Parent],by with_unfolding_all rfl⟩⟩

theorem first_source : firstProgram.run initial = .ok firstOut := by with_unfolding_all rfl
theorem middle_source : middleProgram.run firstOut.st = .ok middleOut := by with_unfolding_all rfl
theorem last_source : mutate.run middleOut.st = .ok second := mutation_source
theorem first_cost : Construction.allocationCostProg firstProgram initial = 2 := by decide +kernel
theorem middle_cost : Construction.allocationCostProg middleProgram firstOut.st = 5 := by decide +kernel

theorem initial_input : (Compilation.construction firstCode).Input 1 8 base initial machine := by
  refine ⟨physical,by decide +kernel,.inr ⟨by decide,⟨16,by decide⟩,allocator,?_⟩⟩
  rw [first_cost]
  decide +kernel

theorem link :
    MappedBoundaryLink (.construction firstCode) (.construction middleCode) 1 8 base initial machine := by
  apply construction_budgeted_link firstCode middleCode (by decide +kernel)
  intro actual reached
  have eqo : actual = firstOut := Except.ok.inj (reached.symm.trans first_source)
  subst actual
  rw [first_cost,middle_cost]
  exact .inr ⟨by decide,⟨16,by decide⟩,allocator,by decide⟩

theorem reached_link :
    ReachedMappedLink (.construction firstCode) (.construction middleCode) (.referenceArrays lastCode)
      1 8 base initial machine := by
  intro o mid selected _ _ _
  exact construction_referenceArrays_link middleCode lastCode

/-- Source-dependent two-cell then five-cell allocations compose through their
ACTUAL separate maps. No unallocated empty-child header is erased. -/
theorem budgeted_shared :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      next.mem 0 = w[23] ∧ ∀ tail,
        run firstCode.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        run middleCode.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
        run lastCode.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
        run ((firstCode.code ++ middleCode.code) ++ lastCode.code) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        run (firstCode.code ++ (middleCode.code ++ lastCode.code)) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        MappedOutput (.construction firstCode) 1 8 base initial {machine with stack := tail}
          firstOut.st {mid with stack := tail} mb ∧
        MappedOutput (.construction middleCode) 1 8 mb firstOut.st {mid with stack := tail}
          middleOut.st {next with stack := tail} nb ∧
        MappedOutput (.referenceArrays lastCode) 1 8 nb middleOut.st {next with stack := tail}
          second.st {final with stack := tail} ob := by
  obtain ⟨mb,nb,ob,mid,next,final,_,_,_,all⟩ :=
    compilation_triple_shared (.construction firstCode) (.construction middleCode) (.referenceArrays lastCode)
      initial_input rfl link reached_link rfl rfl rfl first_source middle_source last_source
  have hs := all []
  have growth := hs.2.2.2.2.2.1.2.2.comp hs.2.2.2.2.2.2.1.2.2
  have total : Objects.GrowsAllocator 1 8 7 initial base machine middleOut.st nb {next with stack := []} := by
    simpa only [first_cost,middle_cost] using growth
  have hc := (total ⟨16,by decide⟩ (by decide) allocator (by decide)).free.cell
  exact ⟨mb,nb,ob,mid,next,final,hc,all⟩

theorem missing_default_headers : Construction.allocationCostProg middleProgram firstOut.st ≠ 3 := by
  rw [middle_cost]
  decide

end Solidity.Backend.Passes.AllocatingMiddle
