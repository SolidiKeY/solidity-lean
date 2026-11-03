import Solidity.Backend.Passes.MemoryCallReuseObservations

/-! A real short old array fails inside a second typed call. The already
reached allocation/capture prefix is kept, with no input or post-state fabricated
for the unreachable allocating suffix. -/
namespace Solidity.Backend.Passes.MemoryCallReuseFailure
open Evm Evm.Memory Evm.Compiler MemoryCallControls MemoryCallReuse MemoryCallReuseApplication

def unreachable : CompiledProg 1 wrong.frag (fresh After) :=
  (compileProg 1 _ (fresh After)).get (by decide +kernel)

theorem nonallocating : wrong.allocates = false := by decide +kernel

theorem reached : ∃ (mb : Nat → Fin W) (mid : Machine), mid.stack = [] ∧ ∀ tail,
    run leading.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    MappedOutput beginning 1 128 base initial {machine with stack := tail}
      before.st {mid with stack := tail} mb ∧
    (Compilation.memoryCalls wrong free.2.2.2).Input 1 128 mb before.st {mid with stack := tail} ∧
    run wrong.code {mid with stack := tail} = .revert ∧
    run ((leading.code ++ wrong.code) ++ unreachable.code) {machine with stack := tail} = .revert ∧
    run (leading.code ++ (wrong.code ++ unreachable.code)) {machine with stack := tail} = .revert := by
  obtain ⟨mid,mb,_,hstack,hm⟩ :=
    compilation_success_shared_mapped beginning MemoryCallReuseApplication.input
      (by decide +kernel) prefix_source
  refine ⟨mb,mid,hstack,?_⟩
  intro tail
  obtain ⟨ha,ma⟩ := hm tail
  have represented : MappedOutput beginning 1 128 base initial {machine with stack := tail}
      before.st {mid with stack := tail} mb := by
    simpa only [prefix_free,Nat.add_zero] using ma
  have hi : (Compilation.memoryCalls wrong free.2.2.2).Input 1 128 mb before.st
      {mid with stack := tail} :=
    ⟨represented.1,frames.2.2.2.2.1,.inl (wrong.zeroCost nonallocating before.st)⟩
  have failure := (compilation_revert_iff (.memoryCalls wrong free.2.2.2) hi
    (by decide +kernel)).mpr (.inl wrong_source)
  change run leading.code {machine with stack := tail} = .ok {mid with stack := tail} 0 at ha
  change run wrong.code {mid with stack := tail} = .revert at failure
  have whole : run (leading.code ++ (wrong.code ++ unreachable.code))
      {machine with stack := tail} = .revert := by
    rw [run_append_ok ha]
    exact run_append_revert failure
  exact ⟨ha,represented,hi,failure,by simpa only [List.append_assoc] using whole,whole⟩

theorem joined_source :
    ((prefixProgram.join wrongCall).join (fresh After)).run initial = .error .revert ∧
    (prefixProgram.join (wrongCall.join (fresh After))).run initial = .error .revert := by
  have firstBad : (prefixProgram.join wrongCall).run initial = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,prefix_source,wrong_source,Except.map]
  have suffix : (wrongCall.join (fresh After)).run before.st = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,wrong_source]
  constructor
  · rw [DeferredSource.join_run]
    simp only [TRun.seq,firstBad]
  · rw [DeferredSource.join_run]
    simp only [TRun.seq,prefix_source,suffix,Except.map]

/-- Bounds failure is neither asserting panic nor divergence; coarse target
revert does not manufacture public byte-level observations. -/
theorem distinct_source : wrongCall.run before.st ≠ .error .panic ∧
    wrongCall.run before.st ≠ .error .diverge := by
  rw [wrong_source]
  constructor <;> intro impossible <;> cases impossible

theorem wrong_stage : wrong.cost before.st = 0 ∧ alias.cost before.st = 1 ∧
    void.cost before.st = 2 := by
  exact ⟨wrong.zeroCost nonallocating before.st,MemoryCallReuse.costs.2.2.1,MemoryCallReuse.costs.2.2.2.1⟩

end Solidity.Backend.Passes.MemoryCallReuseFailure
