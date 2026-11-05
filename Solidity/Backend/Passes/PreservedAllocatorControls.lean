import Solidity.Backend.Passes.ReferenceObjectCertificate
import Solidity.Backend.Passes.HeapApplication

/-! A real nonidentity object pass followed by a fresh allocating suffix.
The prefix allocator is reached from actual construction, not assumed as
the desired preservation result of the object pass. -/
namespace Solidity.Backend.Passes.PreservedAllocatorControls
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open Backend.Passes.Controls.Fixture (C)

def objectCode : Objects.CompiledProg 1 allocation.frag mutate := referenceObjects mutation
def suffixProgram : Prog C Locals (.mem Child :: Locals) :=
  .cons (.declMem Child (.user "afterMutation") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil
def suffixCode : Construction.CompiledProg 1 objectCode.frag suffixProgram :=
  (Construction.compileProg 1 _ suffixProgram).get (by decide +kernel)
def memorySuffix : Memory.CompiledProg 1 objectCode.frag suffixProgram :=
  (Memory.compileProg 1 _ suffixProgram).get (by decide +kernel)

private theorem suffix_some : (suffixProgram.run second.st).toOption.isSome = true := by decide +kernel
noncomputable def suffixOut : Solidity.Out C second.st.H (.mem Child :: Locals) :=
  (suffixProgram.run second.st).toOption.get suffix_some

theorem suffix_source : suffixProgram.run second.st = .ok suffixOut := by
  have h : some suffixOut = (suffixProgram.run second.st).toOption := Option.some_get suffix_some
  cases hs : suffixProgram.run second.st with
  | ok o => rw [hs] at h; exact congrArg Except.ok (Option.some.inj h).symm
  | error e => rw [hs] at h; cases h

theorem suffix_cost (σ : State C Locals) :
    Construction.allocationCostProg suffixProgram σ = 2 := by with_unfolding_all rfl
theorem memory_cost (σ : State C Locals) : memorySuffix.cert.cost σ = 2 := by with_unfolding_all rfl
theorem object_code : objectCode.code = mutation.code := rfl
theorem suffix_codes : suffixCode.code = memorySuffix.code := rfl

/-- Reached full allocator at the selected first-stage map, before the
nonallocating object's preservation certificate is consumed. -/
theorem reached_allocator {tail : List Word} {mb : Nat → Fin W} {mid : Machine}
    (h : MappedOutput (.construction allocation) 1 8 base initial {machine with stack := tail}
      first.st mid mb) :
    Objects.AllocatorRepr first.st.heap mb 8 ⟨23,by decide⟩ mid := by
  have g := h.2.2 (⟨16,by decide⟩ : Fin W) (by decide)
    (allocator.mem_eq rfl) (by rw [cost]; decide)
  simpa only [cost] using g

theorem reached_link (tail : List Word) :
    ReachedMappedLink (.construction allocation) (.objects objectCode) (.construction suffixCode)
      1 8 base initial {machine with stack := tail} := by
  intro actual mid mb hs _ h
  have eqo : actual = first := Except.ok.inj (hs.symm.trans allocation_source)
  subst actual
  apply objects_budgeted_construction_link objectCode suffixCode (by decide +kernel)
  intro o _
  exact .inr ⟨by decide,⟨23,by decide⟩,reached_allocator h,by rw [suffix_cost]; decide⟩

theorem reached_memory_link (tail : List Word) :
    ReachedMappedLink (.construction allocation) (.objects objectCode) (.memory memorySuffix)
      1 8 base initial {machine with stack := tail} := by
  intro actual mid mb hs _ h
  have eqo : actual = first := Except.ok.inj (hs.symm.trans allocation_source)
  subst actual
  apply objects_budgeted_memory_link objectCode memorySuffix (by decide +kernel)
  intro o _
  exact .inr ⟨by decide,⟨23,by decide⟩,reached_allocator h,by rw [memory_cost]; decide⟩

/-- Every actual source and target stage, both code associations and full
branch outputs share three maps chosen before ALL saved tails. -/
theorem shared :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      final.mem 0 = w[25] ∧ ∀ tail,
        run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        run objectCode.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
        run suffixCode.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
        run ((allocation.code ++ objectCode.code) ++ suffixCode.code) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        run (allocation.code ++ (objectCode.code ++ suffixCode.code)) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        MappedOutput (.construction allocation) 1 8 base initial {machine with stack := tail}
          first.st {mid with stack := tail} mb ∧
        MappedOutput (.objects objectCode) 1 8 mb first.st {mid with stack := tail}
          second.st {next with stack := tail} nb ∧
        MappedOutput (.construction suffixCode) 1 8 nb second.st {next with stack := tail}
          suffixOut.st {final with stack := tail} ob := by
  obtain ⟨mb,nb,ob,mid,next,final,_,_,_,all⟩ :=
    compilation_triple_shared (.construction allocation) (.objects objectCode) (.construction suffixCode)
      input rfl (construction_objects_link allocation objectCode (by decide +kernel)) (reached_link [])
      rfl rfl rfl allocation_source mutation_source suffix_source
  obtain ⟨_,_,_,_,_,ha,hd,he⟩ := all []
  have old := reached_allocator ha
  rcases hd with ⟨same,_,keeps⟩
  subst nb
  have preserved := keeps (⟨23,by decide⟩ : Fin W) (by decide) old
  have growth := he.2.2 (⟨23,by decide⟩ : Fin W) (by decide) preserved
    (by rw [suffix_cost]; decide)
  have cursor : final.mem 0 = w[25] := by simpa only [suffix_cost] using growth.free.cell
  exact ⟨mb,mb,ob,mid,next,final,cursor,all⟩

end Solidity.Backend.Passes.PreservedAllocatorControls
