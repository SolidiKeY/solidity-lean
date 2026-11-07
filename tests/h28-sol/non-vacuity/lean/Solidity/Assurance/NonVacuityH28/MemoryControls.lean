import Solidity.Assurance.NonVacuityH28.CheckedObjects

/-! Resource and pointer observations are essential to inhabited inputs. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

def nearEndMachine : Evm.Machine :=
  { memoryMachine with mem := fun a =>
      if a = 0 then .val ⟨Evm.W - 1, by have := Evm.W_pos; omega⟩ else .val (Evm.wmod 0) }

private theorem empty_heap_any (m : Evm.Machine) :
    Evm.Memory.Objects.HeapRepr (memorySource C).heap memoryBases 128 m := by
  have noRef : ∀ {R : RefTy}, HRef (memorySource C).H R → False := by
    intro R r; cases r.get?
  exact ⟨⟨(fun r => (noRef r).elim), (fun r => (noRef r).elim),
      (fun r _ _ => (noRef r).elim)⟩,
    (fun _ r => (noRef r).elim), (fun r => (noRef r).elim),
    (fun r _ => (noRef r).elim)⟩

theorem near_end_state :
    Evm.Memory.Objects.StateRepr 1 1 128 (Evm.Frag.init [])
      (memorySource C) memoryBases nearEndMachine := by
  have h := fresh_object_state C
  exact ⟨⟨h.core.store, (fun i => nomatch i), (fun i => nomatch i),
    h.core.net, h.core.netSelf, h.core.bound, (fun i => nomatch i), h.core.env,
    h.core.funds, h.core.oracle⟩, empty_heap_any C _, (fun i => nomatch i), h.locals⟩

theorem near_end_allocator :
    Evm.Memory.Objects.AllocatorRepr (memorySource C).heap memoryBases 128
      ⟨Evm.W - 1, by have := Evm.W_pos; omega⟩ nearEndMachine := by
  refine ⟨empty_heap_any C _, ⟨by decide, by decide +kernel, rfl, ?_⟩,
    fun r => (noEmptyRef r).elim⟩
  intro a ha
  change Evm.W - 1 ≤ a at ha
  have hz : a ≠ 0 := by
    have : 0 < Evm.W - 1 := by decide +kernel
    omega
  change (if a = 0 then _ else Evm.Word.val (Evm.wmod 0)) = _
  rw [if_neg hz]
  rfl
where
  noEmptyRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

theorem near_end_allocation_rejected :
    ¬ Evm.Memory.Objects.AllocationInput 1 128 2 (memorySource C) memoryBases nearEndMachine := by
  intro hi
  rcases hi with hzero | ⟨_, cursor, ha, hs⟩
  · cases hzero
  · have hc := ha.free.cell
    change Evm.Word.val ⟨Evm.W - 1, _⟩ = .val cursor at hc
    have he : Evm.W - 1 = cursor.val := congrArg Fin.val (Evm.Word.val.inj hc)
    have := Evm.W_pos
    omega

def eraseMemory (m : Evm.Machine) : Evm.Machine :=
  {m with mem := fun _ => .val (Evm.wmod 0)}

/-- A live typed pointer cannot be represented by an erased zero word. -/
theorem pointer_erasure_rejected {Γ : Ctx} {F : Evm.Frag Γ}
    {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (h : Evm.Memory.Objects.StateRepr 1 1 128 F σ base m)
    (i : Idx Γ (.mem (.array (.prim .uint)))) :
    ¬ Evm.Memory.PointerRepr σ base 1 (eraseMemory m) := by
  intro erased
  obtain ⟨r, hr, _⟩ := h.pointers i
  obtain ⟨q, hq, hw⟩ := erased i
  have he : some r = some q := hr.symm.trans hq
  cases Option.some.inj he
  have ha := h.heap.owner.above r
  change Evm.Word.val (Evm.wmod 0) = .val (base r.id) at hw
  have hz : 0 = (base r.id).val := congrArg Fin.val (Evm.Word.val.inj hw)
  omega

theorem allocated_erasure_countercontrol :
    ∃ m : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      Evm.Memory.Objects.StateRepr 1 1 128 (constructionResult C).frag
        (primitiveOutcome C).st base m ∧
      ¬ Evm.Memory.PointerRepr (primitiveOutcome C).st base 1 (eraseMemory m) := by
  obtain ⟨m, base, _, _, h⟩ := construction_joint C
  exact ⟨m, base, h, pointer_erasure_rejected C h .here⟩

end Solidity.Assurance.NonVacuityH28
