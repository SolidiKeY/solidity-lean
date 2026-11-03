import Solidity.Backend.Passes.PreservedAllocatorObservations

namespace Solidity.Backend.Passes.PreservedAllocatorApplication
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open PreservedAllocatorControls
open PreservedAllocatorObservations
open Backend.Passes.Controls.Fixture (C)

theorem prefix_bases {selected : Nat → Fin W} {mid : Machine}
    (input : Objects.StateRepr 1 1 8 allocation.frag first.st selected mid)
    (h1 : mid.mem 1 = w[16]) (h2 : mid.mem 2 = w[18]) :
    selected 0 = ⟨16,by decide⟩ ∧ selected 3 = ⟨18,by decide⟩ := by
  obtain ⟨r,hr,hc⟩ := input.pointers (.there .here)
  have er : r = HeapObservations.child := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change mid.mem 1 = .val (selected 0) at hc
  obtain ⟨r,hr,hp⟩ := input.pointers (.here : Idx Locals (.mem Parent))
  have er : r = HeapObservations.parent := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change mid.mem 2 = .val (selected 3) at hp
  exact ⟨Word.val.inj (hc.symm.trans h1),Word.val.inj (hp.symm.trans h2)⟩

/-- No post-state observation is a premise: the complete vector, old-reference
identity and new object's actual selected base follow from real executions. -/
theorem observed_shared :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      (addresses ob).map final.mem = expected ob ∧ ob 1 ≠ ob 2 ∧
      BaseExtends second.st.H nb ob ∧ ob 4 = ⟨23,by decide⟩ ∧ ∀ tail,
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
  obtain ⟨mb,nb,ob,mid,next,final,h0,all⟩ := PreservedAllocatorControls.shared
  obtain ⟨hm,hn,hf,_,_,ha,hd,he⟩ := all []
  obtain ⟨earlier,hr,_,h1,h2,h15⟩ := HeapPrefix.allocation_observations
  have eqm : earlier = {mid with stack := []} := (Out.ok.inj (hr.symm.trans hm)).1
  subst earlier
  obtain ⟨ec,ep⟩ := prefix_bases ha.1 h1 h2
  rw [object_code] at hn
  have eqn := (Out.ok.inj (hn.symm.trans (HeapObservations.mutation_shape ha.1))).1
  have old := PreservedAllocatorControls.reached_allocator ha
  rcases hd with ⟨same,state,keeps⟩
  subst nb
  have preserved := keeps (⟨23,by decide⟩ : Fin W) (by decide) old
  have eqf := (Out.ok.inj (hf.symm.trans (suffix_shape state preserved))).1
  have f1 : ({final with stack := []} : Machine).mem 1 = w[16] := by
    rw [eqf,eqn,ec,ep]
    change mid.mem 1 = w[16]
    exact h1
  have f2 : ({final with stack := []} : Machine).mem 2 = w[18] := by
    rw [eqf,eqn,ec,ep]
    change mid.mem 2 = w[18]
    exact h2
  have f3 : ({final with stack := []} : Machine).mem 3 = w[23] := by
    rw [eqf]
    rfl
  have f15 : ({final with stack := []} : Machine).mem 15 = w[99] := by
    rw [eqf,eqn,ec,ep]
    change mid.mem 15 = w[99]
    exact h15
  have vector := complete he.1 h0 f1 f2 f3 f15
  obtain ⟨r,hr,hp⟩ := he.1.pointers (.here : Idx (.mem Child :: Locals) (.mem Child))
  have er : r = fresh := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change final.mem 3 = .val (ob 4) at hp
  have newbase : ob 4 = ⟨23,by decide⟩ := Word.val.inj (hp.symm.trans f3)
  exact ⟨mb,mb,ob,mid,next,final,vector.1,vector.2,he.2.1,newbase,all⟩

/-- Copying old slots leaves a zero entry for the fresh object and cannot
represent the reached state. Old BaseExtends NEVER asserts such an entry. -/
def stale (selected : Nat → Fin W) : Nat → Fin W :=
  fun id => if id < 4 then selected id else wmod 0

theorem stale_refused (selected : Nat → Fin W) (m : Machine) :
    ¬ Objects.StateRepr 1 1 8 suffixCode.frag suffixOut.st (stale selected) m := by
  intro h
  have b := h.heap.owner.above fresh
  change 8 ≤ 0 at b
  omega

end Solidity.Backend.Passes.PreservedAllocatorApplication
