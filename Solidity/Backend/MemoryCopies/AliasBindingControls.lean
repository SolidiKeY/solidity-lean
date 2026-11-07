import Solidity.Backend.MemoryCopies.AliasBinding
import Solidity.Evm.MemoryObjectArrayExamples

/-! Compiled indexed aliases on an actual populated input, including refusal. -/
namespace Solidity.Backend.MemoryCopies.AliasBindingControls
open Evm Evm.Memory
private abbrev child : RefTy := .array (.prim .uint)
private structure Input where
  contract : Contract
  context : Ctx
  frag : Frag context
  state : State contract context
  base : Nat → Fin W
  machine : Machine
  represented : Objects.StateRepr 1 1 8 frag state base machine
  allocator : Objects.AllocatorRepr state.heap base 8 ⟨40,by decide⟩ machine
  parent : Idx context (.mem (.fixed (.ref child) 2))
  destination : Idx context (.mem child)
private def input : Input :=
  ⟨_,_,_,_,_,_,ObjectArrayExamples.initial_repr,ObjectArrayExamples.initial_allocator,
    .here,.there (.there .here)⟩
private def path (index : Int) (bound : PrimTy.uint.inRange index = true) : MPath input.contract input.context (.ref child) :=
  .loc (.index .fixed (.var input.parent rfl) (.simple (.lit index bound)))
private def compiled (index : Int) (bound : PrimTy.uint.inRange index = true) :
    SelectedAlias 1 input.frag (path index bound) :=
  selectedAlias 1 input.frag (path index bound) rfl
private def observe : Evm.Out → Option (Word × Word × Word × Word)
  | .ok target _ => some (target.mem 0,target.mem 1,target.mem 2,target.mem 17)
  | _ => none

/-- The generic emitted-code certificate has an actual represented input. -/
theorem inhabited_outcome :
    AliasBindingOutcome 1 1 8 input.frag input.state input.base input.machine (path 0 rfl)
      input.destination ((compiled 0 rfl).code input.destination) :=
  (compiled 0 rfl).execute input.represented input.destination

/-- Indexed alias binding installs the existing child address16, preserves the
other old local24, allocator40 and populated old payload7. -/
theorem actual_target :
    observe (run ((compiled 0 rfl).code input.destination) input.machine) =
      some (w[40],w[16],w[24],w[7]) := by
  decide +kernel

theorem actual_source :
    ∃ reference, (path 0 rfl).mvalT input.state = .ok reference ∧ reference.id = 0 ∧
      TRun.rebindMem input.destination (.alias (path 0 rfl)) input.state =
        .ok ⟨input.state.setLocal input.destination (some reference),List.prefix_refl _⟩ := by
  refine ⟨⟨0,rfl⟩, ?_, rfl, ?_⟩ <;> with_unfolding_all rfl

/-- Out-of-bounds is compiled and reverts on both actual executions. -/
theorem bounds_refusal :
    TRun.rebindMem input.destination (.alias (path 2 rfl)) input.state = .error .revert ∧
      run ((compiled 2 rfl).code input.destination) input.machine = .revert := by
  constructor <;> with_unfolding_all rfl

/-- Pointer40 would claim allocation: it is not the reached alias address. -/
theorem fresh_pointer_rejected :
    observe (run ((compiled 0 rfl).code input.destination) input.machine) ≠
      some (w[40],w[40],w[24],w[7]) := by
  rw [actual_target]
  decide

/-- Skipping the actual binding leaves24 and is observably different. -/
theorem empty_code_rejected :
    observe (run ([] : List Instr) input.machine) ≠
      observe (run ((compiled 0 rfl).code input.destination) input.machine) := by
  rw [actual_target]
  decide +kernel

#print axioms inhabited_outcome
#print axioms actual_target
#print axioms actual_source
#print axioms bounds_refusal
#print axioms fresh_pointer_rejected
#print axioms empty_code_rejected
end Solidity.Backend.MemoryCopies.AliasBindingControls
