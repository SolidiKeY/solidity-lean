import Solidity.Assurance.NonVacuityH28.AllocatorGrowth
import Solidity.Assurance.NonVacuityH28.CheckedFamilies

/-! Queries of quantified output fields at actual live objects/allocators. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

theorem concrete_object_allocator_kept :
    ∃ m : Evm.Machine, ∃ base : Nat → Fin Evm.W, ∃ m' : Evm.Machine,
      Evm.run (constructionCompiled C).code memoryMachine = .ok m 0 ∧
      Evm.run (objectCompiled C).code m = .ok m' 0 ∧
      Evm.Memory.Objects.AllocatorRepr (primitiveOutcome C).st.heap base 128
        ⟨258, by decide +kernel⟩ m ∧
      Evm.Memory.Objects.AllocatorRepr
        ((primitiveOutcome C).st.push (t := .val .uint) (⟨7, rfl⟩ : PrimTy.uint.Denote)).heap base 128
        ⟨258, by decide +kernel⟩ m' := by
  obtain ⟨m, base, ht, _, hstate, ha⟩ := construction_allocator_growth C
  obtain ⟨m', ht', _, hr⟩ := checked_success_after_source (objectCompiled C)
    (object_input C hstate) rfl (declare_memory_source C _)
  have kept := hr.2 ⟨258, by decide +kernel⟩ (by decide) ha
  exact ⟨m, base, m', ht, ht', ha, kept⟩

theorem concrete_object_cursor_kept :
    ∃ m m' : Evm.Machine,
      Evm.run (objectCompiled C).code m = .ok m' 0 ∧
      m.mem 0 = Evm.Word.val (Evm.wmod 258) ∧
      m'.mem 0 = Evm.Word.val (Evm.wmod 258) := by
  obtain ⟨m, _, m', _, ht, ha, ha'⟩ := concrete_object_allocator_kept C
  exact ⟨m, m', ht, ha.free.cell, ha'.free.cell⟩

theorem live_base_extension_queried :
    ∃ m : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      ∃ r : HRef (primitiveOutcome C).st.H (.array (.prim .uint)),
      ∃ m' : Evm.Machine, ∃ base' : Nat → Fin Evm.W,
      Evm.run (constructionCompiled C).code memoryMachine = .ok m 0 ∧
      Evm.run (copyConstructionCompiled C).code m = .ok m' 0 ∧
      TEnv.get .here (primitiveOutcome C).st.env = some r ∧
      base' r.id = base r.id ∧
      Evm.Memory.Objects.StateRepr 1 1 128 (copyConstructionResult C).frag
        (primitiveOutcome C).st base' m' := by
  obtain ⟨m, base, ht, _, hstate⟩ := construction_joint C
  obtain ⟨r, hr, _⟩ := hstate.pointers (.here : Idx MemCtx (.mem (.array (.prim .uint))))
  obtain ⟨m', ht', _, hrep⟩ := checked_success_after_source (copyConstructionCompiled C)
    (copy_construction_input C hstate) rfl (scalar_memory_source C _)
  obtain ⟨base', hstate', hext, _⟩ := hrep
  exact ⟨m, base, r, m', base', ht, ht', hr, hext r, hstate'⟩

/-- A real nonempty primitive array queries both header and element fields. -/
theorem live_array_layout_queried :
    ∃ m : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      ∃ r : HRef (primitiveOutcome emptyContract).st.H (.array (.prim .uint)),
      Evm.run (constructionCompiled emptyContract).code memoryMachine = .ok m 0 ∧
      TEnv.get .here (primitiveOutcome emptyContract).st.env = some r ∧
      m.mem (base r.id).val = .val (Evm.wmod 1) ∧
      m.mem ((base r.id).val + 1) = .val (Evm.wmod 0) := by
  obtain ⟨m, base, ht, _, hstate⟩ := construction_joint emptyContract
  let r : HRef (primitiveOutcome emptyContract).st.H (.array (.prim .uint)) :=
    (TEnv.get .here (primitiveOutcome emptyContract).st.env).get (by rfl)
  have hr : TEnv.get .here (primitiveOutcome emptyContract).st.env = some r := rfl
  have hl := (hstate.heap.arrays .dyn r).length rfl
  have hv : (MObj.elems .dyn ((primitiveOutcome emptyContract).st.heap.get r))[0]? =
      some (⟨0, rfl⟩ : PrimTy.uint.Denote) := by
    decide +kernel
  have he := (hstate.heap.arrays .dyn r).elements 0 (⟨0, rfl⟩ : PrimTy.uint.Denote) hv
  obtain ⟨word, hw, hzero⟩ := he
  change (0 : Int) = (word.val : Int) at hzero
  have hword : word = Evm.wmod 0 := by
    apply Fin.ext
    change word.val = 0
    omega
  rw [hword] at hw
  have hn : (primitiveOutcome emptyContract).st.heap.len r .dyn = 1 := by
    decide +kernel
  rw [hn] at hl
  exact ⟨m, base, r, ht, hr, hl, hw⟩

/-- This particular positive fixture has one object. Separation's distinct-ID
antecedent is intentionally unqueried; it is not a second-object witness. -/
theorem allocated_single_object : (primitiveOutcome emptyContract).st.H.length = 1 := by
  decide +kernel

/-- A successful source run plus independently checked expected observations.
The transport equality source_eq alone is not the non-vacuity witness. -/
theorem primitive_source_observations :
    ∃ o : Out emptyContract (memorySource emptyContract).H MemCtx,
      ∃ r : HRef o.st.H (.array (.prim .uint)),
      Prog.run (memorySource emptyContract) (primitiveAllocation emptyContract) = .ok o ∧
      o.st.H.length = 1 ∧ TEnv.get .here o.st.env = some r ∧
      o.st.heap.len r .dyn = 1 ∧
      (MObj.elems .dyn (o.st.heap.get r))[0]? = some (⟨0, rfl⟩ : PrimTy.uint.Denote) := by
  let r : HRef (primitiveOutcome emptyContract).st.H (.array (.prim .uint)) :=
    (TEnv.get .here (primitiveOutcome emptyContract).st.env).get (by rfl)
  refine ⟨primitiveOutcome emptyContract, r, primitive_source_eq emptyContract,
    allocated_single_object, rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem distinct_object_domain_empty {R Q : RefTy}
    (r : HRef (primitiveOutcome emptyContract).st.H R)
    (q : HRef (primitiveOutcome emptyContract).st.H Q) : r.id = q.id := by
  have hr := (List.getElem?_eq_some_iff.mp r.get?).1
  have hq := (List.getElem?_eq_some_iff.mp q.get?).1
  rw [allocated_single_object] at hr hq
  omega

end Solidity.Assurance.NonVacuityH28
