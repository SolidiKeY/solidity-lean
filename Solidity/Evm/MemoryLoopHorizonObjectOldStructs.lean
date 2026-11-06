import Solidity.Evm.MemoryLoopHorizonObjectOldElements

/-! Actual allocating target execution preserves encoded primitive and
reference fields in original typed struct objects. Owner struct/ref-field
representations, genuine old-heap preservation and base extension fix the
same words at original field addresses. Typed field lookup is explicit;
arbitrary memory and general struct-mutating bodies remain outside scope. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
open Semantics
variable {C : Contract} {Γ : Ctx}

theorem target_old_struct_primitive_fields {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ reached,
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      (∀ (s f : Name) (primitive : PrimTy) (r : HRef state.H (.struct s)),
        lookupBy f (structDef s) = some (.prim primitive) →
        reached.mem ((base r.id).val + fieldOffset (structDef s) f) =
          machine.mem ((base r.id).val + fieldOffset (structDef s) f)) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  refine ⟨reached,target,?_⟩
  intro s f primitive r field
  have kept : Heap.Keeps out.ext state.heap out.st.heap := prefix_keeps_heap hp
  have retained := (repr.heap.structs r).keeps out.ext kept
  have before := retained.fields field
  have after := (current.heap.structs (r.wk out.ext)).fields field
  have address : nextBase (r.wk out.ext).id = base r.id := bases r
  simpa only [address] using value_word_unique (H:=out.st.H) (base:=nextBase)
    (E:=.prim primitive) after before

theorem target_old_struct_reference_fields {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ reached,
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      (∀ (s f : Name) (reference : RefTy) (r : HRef state.H (.struct s)),
        lookupBy f (structDef s) = some (.ref reference) →
        reached.mem ((base r.id).val + fieldOffset (structDef s) f) =
          machine.mem ((base r.id).val + fieldOffset (structDef s) f)) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  refine ⟨reached,target,?_⟩
  intro s f reference r field
  have kept : Heap.Keeps out.ext state.heap out.st.heap := prefix_keeps_heap hp
  have before := repr.heap.refs r field
  have after := current.heap.refs (r.wk out.ext) field
  have child : out.st.heap.field (r.wk out.ext) field = (state.heap.field r field).wk out.ext := by
    simp only [Heap.field, kept r, MObj.wk, MFields.get_wk, MVal.wk]
  have address : nextBase (r.wk out.ext).id = base r.id := bases r
  have childAddress : nextBase ((state.heap.field r field).wk out.ext).id =
      base (state.heap.field r field).id := bases (state.heap.field r field)
  rw [address, child, childAddress] at after
  exact after.trans before.symm

end Solidity.Evm.Memory.HorizonObjectAllocating
