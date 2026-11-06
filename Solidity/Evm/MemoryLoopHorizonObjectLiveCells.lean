import Solidity.Evm.MemoryLoopHorizonObjectOldHeaders
import Solidity.Evm.MemoryLoopHorizonObjectOldStructs

/-! One actual reached machine preserves the explicit original typed live-cell
footprint of the allocating loop. Headers, live array payloads and typed struct
fields use their proved owner representations; deterministic target execution
aligns all component witnesses. Padding, unowned memory, general stores/copies
and unconditional allocation capacity remain outside this contract. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
open Semantics
variable {C : Contract} {Γ : Ctx}

/-- Typed, value-bearing original cells; reserved padding is not included. -/
inductive OriginalLiveCell {H : HTy} (heap : Heap H) (base : Nat → Fin W) : Nat → Prop where
  | header (E : Ty) (r : HRef H (.array E)) : OriginalLiveCell heap base (base r.id).val
  | element (A : RefTy) (E : Ty) (layout : ArrTy A E) (r : HRef H A) (i : Nat)
      (value : MVal H E) (live : (MObj.elems layout (heap.get r))[i]? = some value) :
      OriginalLiveCell heap base ((base r.id).val + Objects.header layout + i)
  | primitive (s f : Name) (p : PrimTy) (r : HRef H (.struct s))
      (field : lookupBy f (structDef s) = some (.prim p)) :
      OriginalLiveCell heap base ((base r.id).val + fieldOffset (structDef s) f)
  | reference (s f : Name) (R : RefTy) (r : HRef H (.struct s))
      (field : lookupBy f (structDef s) = some (.ref R)) :
      OriginalLiveCell heap base ((base r.id).val + fieldOffset (structDef s) f)

theorem target_old_live_cells {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ reached,
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      (∀ address, OriginalLiveCell state.heap base address → reached.mem address = machine.mem address) := by
  obtain ⟨reached,target,headers⟩ := target_old_array_headers compiled n repr capacity demand
  obtain ⟨elementReached,elementTarget,elements⟩ := target_old_array_elements compiled n repr capacity demand
  have elementSame : reached = elementReached := Sum.inl.inj (target.symm.trans elementTarget)
  subst elementReached
  obtain ⟨primitiveReached,primitiveTarget,primitives⟩ :=
    target_old_struct_primitive_fields compiled n repr capacity demand
  have primitiveSame : reached = primitiveReached := Sum.inl.inj (target.symm.trans primitiveTarget)
  subst primitiveReached
  obtain ⟨referenceReached,referenceTarget,references⟩ :=
    target_old_struct_reference_fields compiled n repr capacity demand
  have referenceSame : reached = referenceReached := Sum.inl.inj (target.symm.trans referenceTarget)
  subst referenceReached
  refine ⟨reached,target,?_⟩
  intro address live
  cases live with
  | header E r => exact headers E r
  | element A E layout r i value present => exact elements A E layout r i value present
  | primitive s f p r field => exact primitives s f p r field
  | reference s f R r field => exact references s f R r field

end Solidity.Evm.Memory.HorizonObjectAllocating
