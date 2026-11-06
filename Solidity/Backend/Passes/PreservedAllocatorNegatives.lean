import Solidity.Backend.Passes.PreservedAllocatorApplication

namespace Solidity.Backend.Passes.PreservedAllocatorNegatives
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open PreservedAllocatorControls
open PreservedAllocatorApplication
open Backend.Passes.Controls.Fixture (C)

def failingProgram : Prog C Locals (.val .uint :: .mem Child :: Locals) :=
  .cons (.declMem Child (.user "beforeFailure") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
    (.cons (.declLocal .uint (.user "bad") (some (.readMem
      (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl)))))) .nil)
def failingCode : Construction.CompiledProg 1 objectCode.frag failingProgram :=
  (Construction.compileProg 1 _ failingProgram).get (by decide +kernel)

theorem failing_cost (σ : State C Locals) :
    Construction.allocationCostProg failingProgram σ = 2 := by with_unfolding_all rfl

theorem failed_source : failingProgram.run second.st = .error .revert := by
  with_unfolding_all rfl

theorem failed_link (tail : List Word) :
    ReachedMappedLink (.construction allocation) (.objects objectCode) (.construction failingCode)
      1 8 base initial {machine with stack := tail} := by
  intro actual mid mb hs _ h
  have eqo : actual = first := Except.ok.inj (hs.symm.trans allocation_source)
  subst actual
  apply objects_budgeted_construction_link objectCode failingCode (by decide +kernel)
  intro o _
  exact .inr ⟨by decide,⟨23,by decide⟩,reached_allocator h,by rw [failing_cost]; decide⟩

/-- Actual stage-three failure follows both preceding successful effects.
No post-failure machine/map or skipped later source execution is invented. -/
theorem failed_target (tail : List Word) :
    run ((allocation.code ++ objectCode.code) ++ failingCode.code)
      {machine with stack := tail} = .revert := by
  apply (compilation_triple_revert_iff (.construction allocation) (.objects objectCode) (.construction failingCode)
    (compilation_input_stack (.construction allocation) input tail)
    (construction_objects_link allocation objectCode (by decide +kernel)) (failed_link tail)
    rfl rfl rfl).mpr
  exact .inr ⟨first,allocation_source,.inr ⟨second,mutation_source,.inl failed_source⟩⟩

/-- Positive receiving-branch application for the SAME legacy emitted suffix.
Original object allocator is projected only after real preservation. -/
theorem memory_shared :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      final.mem 0 = w[25] ∧ ∀ tail,
        run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        run objectCode.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
        run memorySuffix.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
        run ((allocation.code ++ objectCode.code) ++ memorySuffix.code) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        run (allocation.code ++ (objectCode.code ++ memorySuffix.code)) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        MappedOutput (.construction allocation) 1 8 base initial {machine with stack := tail}
          first.st {mid with stack := tail} mb ∧
        MappedOutput (.objects objectCode) 1 8 mb first.st {mid with stack := tail}
          second.st {next with stack := tail} nb ∧
        MappedOutput (.memory memorySuffix) 1 8 nb second.st {next with stack := tail}
          suffixOut.st {final with stack := tail} ob := by
  obtain ⟨mb,nb,ob,mid,next,final,_,_,_,all⟩ :=
    compilation_triple_shared (.construction allocation) (.objects objectCode) (.memory memorySuffix)
      input rfl (construction_objects_link allocation objectCode (by decide +kernel)) (reached_memory_link [])
      rfl rfl rfl allocation_source mutation_source suffix_source
  obtain ⟨_,_,_,_,_,ha,hd,he⟩ := all []
  have old := reached_allocator ha
  rcases hd with ⟨same,_,keeps⟩
  subst nb
  have preserved := keeps (⟨23,by decide⟩ : Fin W) (by decide) old
  have growth := he.2.2 (⟨23,by decide⟩ : Fin W) (by decide) preserved.legacy
    (by rw [memory_cost]; decide)
  have cursor : final.mem 0 = w[25] := by simpa only [memory_cost] using growth.arrays.free.cell
  exact ⟨mb,mb,ob,mid,next,final,cursor,all⟩

private theorem skip_some : (suffixProgram.run first.st).toOption.isSome = true := by decide +kernel
noncomputable def skipped : Solidity.Out C first.st.H (.mem Child :: Locals) :=
  (suffixProgram.run first.st).toOption.get skip_some
theorem skipped_source : suffixProgram.run first.st = .ok skipped := by
  have h : some skipped = (suffixProgram.run first.st).toOption := Option.some_get skip_some
  cases hs : suffixProgram.run first.st with
  | ok o => rw [hs] at h; exact congrArg Except.ok (Option.some.inj h).symm
  | error e => rw [hs] at h; cases h

def skippedChild : HRef skipped.st.H Child := ⟨0,by decide +kernel⟩
theorem skipped_contents : (skipped.st.heap.get skippedChild).val = [lenU 0 (by decide)] := by
  with_unfolding_all rfl

/-- This also inhabits construction→allocating MEMORY using its real sum9
budget. Omitting the object effect leaves the actual old child zero, not42. -/
theorem skipped_target :
    ∃ final, run (allocation.code ++ memorySuffix.code) machine = .ok final 0 ∧
      final.mem 17 = w[0] ∧ final.mem 0 = w[25] := by
  have link : MappedBoundaryLink (.construction allocation) (.memory memorySuffix)
      1 8 base initial machine := by
    apply construction_budgeted_memory_link allocation memorySuffix (by decide +kernel)
    intro o _
    rw [cost,memory_cost]
    exact .inr ⟨by decide,⟨16,by decide⟩,allocator,by decide⟩
  obtain ⟨mb,ob,mid,final,_,hm,ht,_,ha,he⟩ :=
    compilation_mapped_success (.construction allocation) (.memory memorySuffix) input link
      rfl rfl allocation_source skipped_source
  obtain ⟨earlier,hr,_,h1,h2,_⟩ := HeapPrefix.allocation_observations
  have eqm : earlier = mid := (Out.ok.inj (hr.symm.trans hm)).1
  subst earlier
  have ec := (prefix_bases ha.1 h1 h2).1
  have ext := he.2.1 HeapObservations.child
  change ob 0 = mb 0 at ext
  have ev := (he.1.heap.arrays skippedChild).elements 0 (lenU 0 (by decide))
    (by rw [MObj.elems,skipped_contents]; rfl)
  change ReprV .uint (lenU 0 (by decide)) (final.mem ((ob 0).val + 1 + 0)) at ev
  rw [ext,ec] at ev
  change ReprV .uint (lenU 0 (by decide)) (final.mem 17) at ev
  obtain ⟨a,ha',he',hw⟩ := ev.uint_inv
  have zero : a = 0 := by change (0 : Int) = a at he'; omega
  subst a
  have grown := he.2.2 (⟨23,by decide⟩ : Fin W) (by decide) (reached_allocator ha).legacy
    (by rw [memory_cost]; decide)
  have cursor : final.mem 0 = w[25] := by simpa only [memory_cost] using grown.arrays.free.cell
  exact ⟨final,ht,hw,cursor⟩

theorem corrupted_tail :
    ∃ final, run (((allocation.code ++ objectCode.code) ++ suffixCode.code) ++ [.pop])
      {machine with stack := [w[77]]} = .ok final 0 ∧ final.stack = [] := by
  obtain ⟨mb,nb,ob,mid,next,final,_,all⟩ := PreservedAllocatorControls.shared
  have h := (all [w[77]]).2.2.2.1
  refine ⟨{final with stack := []},?_,rfl⟩
  rw [run_append_ok h]
  rfl

def badExpression : Val C (.mem Child :: Locals) .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl)))
def badValue : CompiledVal 1 suffixCode.frag badExpression :=
  (Memory.compileVal 1 _ badExpression).get (by decide +kernel)

theorem bad_value_source : badExpression.evalT suffixOut.st = .error .revert := by
  with_unfolding_all rfl
theorem failing_code : failingCode.code = suffixCode.code ++ (badValue.code ++ [.mstore 4]) := rfl

/-- The fresh allocation REALLY succeeds before the bounds failure. Complete
fourteen-cell observations and all selected prefix maps precede the failure;
the bad read consumes their actual transported Input, not a replacement map. -/
theorem reached_failure_witness :
    ∃ (mb nb ob : Nat → Fin W) (mid next fresh : Machine),
      (PreservedAllocatorObservations.addresses ob).map fresh.mem =
        PreservedAllocatorObservations.expected ob ∧ ob 4 = ⟨23,by decide⟩ ∧ ∀ tail,
        run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        run objectCode.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
        run suffixCode.code {next with stack := tail} = .ok {fresh with stack := tail} 0 ∧
        MappedOutput (.construction allocation) 1 8 base initial {machine with stack := tail}
          first.st {mid with stack := tail} mb ∧
        MappedOutput (.objects objectCode) 1 8 mb first.st {mid with stack := tail}
          second.st {next with stack := tail} nb ∧
        MappedOutput (.construction suffixCode) 1 8 nb second.st {next with stack := tail}
          suffixOut.st {fresh with stack := tail} ob ∧
        StateRepr 1 1 8 suffixCode.frag suffixOut.st ob {fresh with stack := tail} ∧
        run (badValue.code ++ [.mstore 4]) {fresh with stack := tail} = .revert ∧
        run failingCode.code {next with stack := tail} = .revert := by
  obtain ⟨mb,nb,ob,mid,next,fresh,vector,_,_,newbase,all⟩ := observed_shared
  refine ⟨mb,nb,ob,mid,next,fresh,vector,newbase,?_⟩
  intro tail
  obtain ⟨ha,hd,he,_,_,ma,md,me⟩ := all tail
  have input := me.1.legacy
  have bad := (value_revert_iff badValue input tail).mpr bad_value_source
  have failure : run (badValue.code ++ [.mstore 4]) {fresh with stack := tail} = .revert :=
    run_append_revert bad
  refine ⟨ha,hd,he,ma,md,me,input,failure,?_⟩
  rw [failing_code,run_append_ok he]
  exact failure

end Solidity.Backend.Passes.PreservedAllocatorNegatives
