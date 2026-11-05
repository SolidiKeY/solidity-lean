import Solidity.Assurance.NonVacuityH28.Families

/-! Joint heap/allocator premises for the existing checked memory contract.
The initial heap is empty; the checked program allocates a real typed object.
No compiler producer or interface is changed. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

def memoryBases : Nat → Fin Evm.W := fun _ => Evm.wmod 0
def memorySource : State C [] := State.init C
def memoryMachine : Evm.Machine :=
  { Evm.Machine.init with
    stack := [.val (Evm.wmod 77)]
    mem := fun a => if a = 0 then .val (Evm.wmod 256) else .val (Evm.wmod 0) }

private theorem noEmptyReference {R : RefTy} (r : HRef [] R) : False := by cases r.get?

theorem empty_object_heap :
    Evm.Memory.Objects.HeapRepr (memorySource C).heap memoryBases 128 memoryMachine :=
  ⟨⟨(fun r => (noEmptyReference r).elim), (fun r => (noEmptyReference r).elim),
      (fun r _ _ => (noEmptyReference r).elim)⟩,
    (fun _ r => (noEmptyReference r).elim), (fun r => (noEmptyReference r).elim),
    (fun r _ => (noEmptyReference r).elim)⟩

theorem fresh_object_state :
    Evm.Memory.Objects.StateRepr 1 1 128 (Evm.Frag.init []) (memorySource C) memoryBases memoryMachine := by
  have h : Evm.Sim C 1 0 (Evm.Frag.init []) (Evm.freshT C 0 (by decide) ⟨0, by decide⟩)
      (Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩) :=
    Evm.Sim.init C 0 (by decide) (fun _ => 0) ⟨0, by decide⟩ rfl
  exact ⟨⟨h.store, (fun i => nomatch i), (fun i => nomatch i), h.net, h.netSelf, h.bound,
    (fun i => nomatch i), h.env, h.funds, h.oracle⟩,
    empty_object_heap C, (fun i => nomatch i), by decide⟩

theorem fresh_free_memory : Evm.Memory.FreeMemory 128 (Evm.wmod 256) memoryMachine := by
  refine ⟨by decide, by decide, rfl, ?_⟩
  intro a ha
  have hz : a ≠ 0 := by change 256 ≤ a at ha; omega
  change (if a = 0 then Evm.Word.val (Evm.wmod 256) else .val (Evm.wmod 0)) = .val (Evm.wmod 0)
  rw [if_neg hz]

theorem fresh_object_allocator :
    Evm.Memory.Objects.AllocatorRepr (memorySource C).heap memoryBases 128 (Evm.wmod 256) memoryMachine :=
  ⟨empty_object_heap C, fresh_free_memory, fun r => (noEmptyReference r).elim⟩

def primitiveAllocation : Prog C [] [.mem (.array (.prim .uint))] :=
  .cons (.declMem (.array (.prim .uint)) (.user "xs") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil

def primitiveMemoryResult : Evm.Memory.CompiledProg 1 (Evm.Frag.init []) (primitiveAllocation C) :=
  (Evm.Memory.compileProg 1 (Evm.Frag.init []) (primitiveAllocation C)).get (by rfl)

def primitiveCompiled : Evm.Compiler.Compilation 1 (Evm.Frag.init []) (primitiveAllocation C) :=
  .memory (primitiveMemoryResult C)

theorem primitive_input : (primitiveCompiled C).Input 1 128 memoryBases (memorySource C) memoryMachine := by
  refine ⟨(fresh_object_state C).legacy, ?_, ?_⟩
  · change 2 ≤ 128
    decide +kernel
  · refine .inr ⟨by decide, Evm.wmod 256, (fresh_object_allocator C).legacy, ?_⟩
    change 256 + 2 < Evm.W
    decide +kernel

def primitiveOutcome : Out C (memorySource C).H [.mem (.array (.prim .uint))] :=
  (Prog.run (memorySource C) (primitiveAllocation C)).toOption.get (by rfl)

theorem primitive_source_eq : Prog.run (memorySource C) (primitiveAllocation C) = .ok (primitiveOutcome C) := rfl

theorem primitive_pointer :
    ∃ r : HRef (primitiveOutcome C).st.H (.array (.prim .uint)),
      TEnv.get .here (primitiveOutcome C).st.env = some r := ⟨_, rfl⟩

theorem primitive_source : ∃ o, Prog.run (memorySource C) (primitiveAllocation C) = .ok o ∧ o.st.H ≠ [] := by
  obtain ⟨r, _⟩ := primitive_pointer C
  refine ⟨primitiveOutcome C, primitive_source_eq C, ?_⟩
  intro h
  have hlen : r.id < (primitiveOutcome C).st.H.length :=
    (List.getElem?_eq_some_iff.mp r.get?).1
  have hz : (primitiveOutcome C).st.H.length = 0 := congrArg List.length h
  omega

theorem primitive_checked : (primitiveCompiled C).Agrees 1 128 memoryBases (memorySource C) memoryMachine :=
  Main.compiler_checked (primitiveCompiled C) (primitive_input C)

/-- Source success and a nonempty allocated heap jointly force the checked
compiler's actual successful target branch and retained pointer/heap relation. -/
theorem primitive_joint :
    ∃ o mc', Prog.run (memorySource C) (primitiveAllocation C) = .ok o ∧
      Evm.run (primitiveCompiled C).code memoryMachine = .ok mc' 0 ∧
      mc'.stack = memoryMachine.stack ∧ o.st.H ≠ [] ∧
      ∃ base', Evm.Memory.StateRepr 1 1 128 (primitiveMemoryResult C).frag o.st base' mc' := by
  obtain ⟨o, ho, hheap⟩ := primitive_source C
  rcases primitive_checked C with
    ⟨o', mc', hs, ht, hstack, hr⟩ | ⟨he, _⟩ | ⟨hp, _⟩ | ⟨hd, _⟩
  · have heq : (Except.ok o' : TRes (Out C (memorySource C).H _)) = .ok o := hs.symm.trans ho
    cases heq
    obtain ⟨base', hstate, _, _⟩ := hr
    exact ⟨o, mc', ho, ht, hstack, hheap, base', hstate⟩
  · rcases he with he | ⟨_, he⟩
    · have hbad : (Except.ok o : TRes (Out C (memorySource C).H _)) = .error .revert := ho.symm.trans he
      cases hbad
    · have hbad : (Except.ok o : TRes (Out C (memorySource C).H _)) = .error .panic := ho.symm.trans he
      cases hbad
  · cases hp
  · have hbad : (Except.ok o : TRes (Out C (memorySource C).H _)) = .error .diverge := ho.symm.trans hd
    cases hbad

end Solidity.Assurance.NonVacuityH28
