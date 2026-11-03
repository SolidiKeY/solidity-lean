import Solidity.Backend.Passes.ReframedSequence
import Solidity.Backend.Passes.MemoryCallReuseApplication

/-! A real allocated/captured memory-return call releases its private frame
before a consuming memory pass. No ABI/function-reference producer is added. -/
namespace Solidity.Backend.Passes.ReframedControls
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls MemoryCallReuse
abbrev left := MemoryCallReuseApplication.beginning
def right : CompiledProg 1 leading.frag consume :=
  (compileProg 1 _ consume).get (by decide +kernel)

/-- The prefix really cannot run under the SMALL suffix reservation. -/
theorem frame_gap : 5 < 1 + leading.need ∧
    1 + After.length ≤ 5 ∧ 1 + frameNeedProg consume ≤ 5 := by decide +kernel

theorem prefix_refused_at_suffix_frame {selected : Nat → Fin W}
    {σ : State C []} {m : Machine} : ¬ left.Input 1 5 selected σ m := by
  intro h
  have hn := h.2.1
  have gap := frame_gap.1
  exact (Nat.not_le_of_lt gap) hn

theorem physical_link :
    ReframedLink left (.memory right) 1 128 5 base initial machine :=
  memoryCalls_shrinking_link leading prefix_free right (by decide)
    frame_gap.2.1 frame_gap.2.2 MemoryCallControls.costs.2.2.2

/-- Selected maps/machines precede tails; every representation below is
indexed by its ORIGINAL physical frame, never silently replaced by5. -/
theorem shared : ∃ (mb nb : Nat → Fin W) (mid out : Machine),
    (prefixProgram.join consume).run initial =
      .ok ⟨final.st,before.ext.trans final.ext⟩ ∧
    mid.stack = [] ∧ out.stack = [] ∧ ∀ tail,
      left.Input 1 128 base initial {machine with stack := tail} ∧
      run left.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput left 1 128 base initial {machine with stack := tail}
        before.st {mid with stack := tail} mb ∧
      (Compilation.memory right).Input 1 5 mb before.st {mid with stack := tail} ∧
      run right.code {mid with stack := tail} = .ok {out with stack := tail} 0 ∧
      MappedOutput (.memory right) 1 5 mb before.st {mid with stack := tail}
        final.st {out with stack := tail} nb ∧
      run (left.code ++ right.code) {machine with stack := tail} =
        .ok {out with stack := tail} 0 := by
  simpa only [prefix_free,MemoryCallApplication.consumer_free,Nat.add_zero] using
    compilation_reframed_shared left (.memory right) MemoryCallReuseApplication.input rfl
      physical_link (by decide +kernel) (by decide +kernel) prefix_source final_source

def badProg : Prog C After After := .cons (.require (.simple (.bool false))) .nil
def bad : CompiledProg 1 leading.frag badProg :=
  (compileProg 1 _ badProg).get (by decide +kernel)
theorem bad_source : badProg.run before.st = .error .revert := by with_unfolding_all rfl
theorem bad_link : ReframedLink left (.memory bad) 1 128 5 base initial machine :=
  memoryCalls_shrinking_link leading prefix_free bad (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)

/-- A failure is reached AFTER the actual allocating/capturing call. No
post-failure machine or selected map is fabricated. -/
theorem reached_revert :
    ∃ (mid : Machine) (mb : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
      run left.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput left 1 128 base initial {machine with stack := tail}
        before.st {mid with stack := tail} mb ∧
      (Compilation.memory bad).Input 1 5 mb before.st {mid with stack := tail} ∧
      run bad.code {mid with stack := tail} = .revert ∧
      run (left.code ++ bad.code) {machine with stack := tail} = .revert := by
  obtain ⟨mid,mb,hm,empty,hall⟩ :=
    compilation_success_shared_mapped left MemoryCallReuseApplication.input
      (by decide +kernel) prefix_source
  refine ⟨mid,mb,empty,?_⟩
  intro tail
  obtain ⟨hp,out⟩ := hall tail
  have canonical : run left.code machine = .ok mid 0 := by simpa only [machine] using hm
  have canonicalOut : MappedOutput left 1 128 base initial machine before.st mid mb := by
    simpa only [prefix_free,Nat.add_zero] using
      mapped_output_stack left (hall []).2 machine.stack mid.stack
  have ib := bad_link before mid mb prefix_source canonical canonicalOut
  have ibt := compilation_input_stack (.memory bad) ib tail
  have hf := (compilation_revert_iff (.memory bad) ibt (by decide +kernel)).mpr (.inl bad_source)
  refine ⟨hp,?_,ibt,hf,?_⟩
  · simpa only [prefix_free,Nat.add_zero] using out
  · rw [run_append_ok hp]
    exact hf

private def words (o : Evm.Out) : Option (List Nat) :=
  match o with
  | .ok m _ => (m.stack ++ MemoryCallObservations.addresses.map m.mem).mapM fun w =>
    match w with | .val n => some n.val | .slot _ => none
  | _ => none

/-- Full original observations: both old and new objects, all elements,
private cells, local aliases, sentinel, cursor and both saved stack words. -/
theorem ordered_vectors :
    words (run left.code {machine with stack := [w[77],w[88]]}) =
      some [77,88,264,99,256,42,256,259,259,259,1,7,0,2,33,34,1,44] ∧
    words (run (left.code ++ right.code) {machine with stack := [w[77],w[88]]}) =
      some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,42,34,1,44] := by
  exact ⟨by decide +kernel,by decide +kernel⟩

theorem skipped_consumer :
    words (run left.code {machine with stack := [w[77],w[88]]}) ≠
      some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,42,34,1,44] := by
  rw [ordered_vectors.1]
  decide

theorem corrupted_tail :
    words (run (left.code ++ right.code) {machine with stack := [w[88],w[77]]}) ≠
      some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,42,34,1,44] := by decide +kernel

/-- Below the actual local/code bound the suffix is still refused. The
new boundary did not waive its original capacity clause. -/
theorem short_suffix_frame {selected : Nat → Fin W} {σ : State C After} {m : Machine} :
    ¬ (Compilation.memory right).Input 1 4 selected σ m := by
  intro h
  have hn := h.2.1
  have need : 1 + frameNeedProg consume = 5 := by decide +kernel
  omega
end Solidity.Backend.Passes.ReframedControls
