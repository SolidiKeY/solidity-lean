import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingSource

/-! Populated mutating native return at the actual paired-unwind endpoint.
The image is assembled from checked entry and restore components, not a public
general recursive compiler. Whole source-state equality comes from native
execution, never from target determinism or heap-content preservation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingReturn
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
namespace Checks
open CountdownWitness
abbrev A := CountdownWitness.A

def image : List Instr :=
 [.loop (guardCompiled (C:=P.C) 2 F).code (MutatingActivation.code (C:=P.C) 2 F 8)] ++
 PairedUnwind.code 2 8 7 A

theorem saved : ∀ j,j<2 →
 MutatingPrefixes.Checks.machine.mem (10+2*j)=MutatingPrefixes.Checks.machine.mem 2 ∧
 MutatingPrefixes.Checks.machine.mem (10+2*j+1)=.val (wmod (2-j)) := by
 have observed := congrArg Prod.snd MutatingPrefixes.Checks.observations
 simp only [List.cons.injEq,and_true] at observed
 rcases observed with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
 intro j small
 rcases (by omega : j=0 ∨ j=1) with rfl | rfl
 · exact ⟨h10.trans h2.symm,h11⟩
 · exact ⟨h12.trans h2.symm,h13⟩

theorem available : ∃ last,
 run image ParentPrefixes.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F MutatingSource.Checks.rootOut.st MutatingPrefixes.Checks.addresses last ∧
 last.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base MutatingPrefixes.Checks.addresses ∧
 GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input MutatingSource.Checks.rootOut.st
   MutatingPrefixes.Checks.addresses last ∧
 StructAllocatorRepr MutatingSource.Checks.rootOut.st.heap MutatingPrefixes.Checks.addresses 16
   (⟨30,by decide⟩ : Fin W) last ∧
 last.mem 8=w[10] ∧ last.mem 2=MutatingPrefixes.Checks.machine.mem 2 ∧
 (∀ x,x≠8 → x≠2 → x≠3 → last.mem x=MutatingPrefixes.Checks.machine.mem x) ∧
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) 2 MutatingPrefixes.Checks.machine=.inl last ∧
 (∀ n,3≤n → loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) n MutatingPrefixes.Checks.machine=.inr (.ok last 0)) := by
 rcases MutatingPrefixes.Checks.specification with ⟨_,_,_,_,repr,_,_,_,pointer,_⟩
 have downWords := congrArg Prod.snd MutatingPrefixes.Checks.observations
 simp only [List.cons.injEq,and_true] at downWords
 rcases downWords with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
 obtain ⟨last,running,represented,stack,cursor,reference,growth,high,outside⟩ :=
   ParentPrefixes.running_prefix MutatingPrefixes.Checks.child MutatingPrefixes.Checks.addresses 2 2 2
     (by decide) (by decide) (by decide) MutatingPrefixes.Checks.machine repr
     8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) pointer h7 saved
 have finalRepr : StateRepr 1 2 16 F MutatingSource.Checks.rootOut.st MutatingPrefixes.Checks.addresses last := by
   rw [MutatingSource.Checks.root_state]
   exact represented
 have finalGrowth : GrowsAllocator 2 16 0 MutatingPrefixes.Checks.child MutatingPrefixes.Checks.addresses
     MutatingPrefixes.Checks.machine MutatingSource.Checks.rootOut.st MutatingPrefixes.Checks.addresses last := by
   rw [MutatingSource.Checks.root_state]
   exact growth
 have bottom : last.mem 7=w[10] := (outside 7 (by decide) (by decide) (by decide)).trans h7
 have stopped := ParentStop.stop_after_running running cursor bottom
 have restore := PairedUnwind.run_of_stopped stopped
 have executed := (run_append_ok MutatingPrefixes.Checks.loop_endpoint).trans restore
 have totalGrowth : GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input
     MutatingSource.Checks.rootOut.st MutatingPrefixes.Checks.addresses last := by
   simpa only [Nat.add_zero] using MutatingPrefixes.Checks.total.2.2.1.comp finalGrowth
 exact ⟨last,executed,finalRepr,stack.trans MutatingPrefixes.Checks.total.1,
   MutatingPrefixes.Checks.total.2.1,totalGrowth,
   totalGrowth (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide),
   cursor,reference,outside,running,fun n later => loopIterN_done_le later stopped⟩

noncomputable def machine : Machine := available.choose

theorem specification :
 run image ParentPrefixes.Checks.input=.ok machine 0 ∧
 StateRepr 1 2 16 F MutatingSource.Checks.rootOut.st MutatingPrefixes.Checks.addresses machine ∧
 machine.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base MutatingPrefixes.Checks.addresses ∧
 GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input MutatingSource.Checks.rootOut.st
   MutatingPrefixes.Checks.addresses machine ∧
 StructAllocatorRepr MutatingSource.Checks.rootOut.st.heap MutatingPrefixes.Checks.addresses 16
   (⟨30,by decide⟩ : Fin W) machine ∧
 machine.mem 8=w[10] ∧ machine.mem 2=MutatingPrefixes.Checks.machine.mem 2 ∧
 (∀ x,x≠8 → x≠2 → x≠3 → machine.mem x=MutatingPrefixes.Checks.machine.mem x) ∧
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) 2 MutatingPrefixes.Checks.machine=.inl machine ∧
 (∀ n,3≤n → loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) n MutatingPrefixes.Checks.machine=.inr (.ok machine 0)) :=
 available.choose_spec

theorem growing : GrowingResult 1 2 16 8 F callee P.base ParentPrefixes.Checks.input
 ((MutatingActivation.body 3).run callee) (run image ParentPrefixes.Checks.input) := by
 rcases specification with ⟨actual,repr,stack,base,growth,_⟩
 exact .inl ⟨MutatingSource.Checks.rootOut,machine,MutatingPrefixes.Checks.addresses,
   MutatingSource.Checks.root,actual,repr,stack,base,growth⟩

theorem observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,
 machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 20,machine.mem 21,
 machine.mem 22,machine.mem 23,machine.mem 24,machine.mem 25,
 machine.mem 26,machine.mem 27,machine.mem 28,machine.mem 29])=
 ([w[77]],[w[30],w[16],w[16],w[2],w[26],w[10],w[10],w[99],w[16],w[2],w[16],w[1],
 w[2],w[1],w[2],w[1],w[4],w[3],w[0],w[0],w[0],w[3],w[0],w[0],w[0]]) := by
 rcases specification with ⟨actual,repr,stack,base,growth,owner,pointer,reference,outside,_⟩
 have counter := RecursiveHistory.counter_word MutatingSource.Checks.rootOut.st 2 (by decide) rfl
   MutatingPrefixes.Checks.addresses machine repr
 have prior := congrArg Prod.snd MutatingPrefixes.Checks.observations
 simp only [List.cons.injEq,and_true] at prior
 rcases prior with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
 change machine.stack=[w[77]] at stack
 rw [stack,counter,pointer,reference,
   outside 0 (by decide) (by decide) (by decide),
   outside 1 (by decide) (by decide) (by decide),
   outside 4 (by decide) (by decide) (by decide),
   outside 7 (by decide) (by decide) (by decide),
   outside 9 (by decide) (by decide) (by decide),
   outside 10 (by decide) (by decide) (by decide),
   outside 11 (by decide) (by decide) (by decide),
   outside 12 (by decide) (by decide) (by decide),
   outside 13 (by decide) (by decide) (by decide),
   outside 16 (by decide) (by decide) (by decide),
   outside 17 (by decide) (by decide) (by decide),
   outside 18 (by decide) (by decide) (by decide),
   outside 20 (by decide) (by decide) (by decide),
   outside 21 (by decide) (by decide) (by decide),
   outside 22 (by decide) (by decide) (by decide),
   outside 23 (by decide) (by decide) (by decide),
   outside 24 (by decide) (by decide) (by decide),
   outside 25 (by decide) (by decide) (by decide),
   outside 26 (by decide) (by decide) (by decide),
   outside 27 (by decide) (by decide) (by decide),
   outside 28 (by decide) (by decide) (by decide),
   outside 29 (by decide) (by decide) (by decide)]
 rw [h0,h1,h2,h4,h7,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29]
 rfl

theorem target_facts : machine.mem 0=w[30] ∧ machine.mem 1=w[16] ∧ machine.mem 3=w[2] ∧
 machine.mem 8=w[10] ∧ machine.mem 17=w[1] ∧ machine.mem 18=w[2] ∧ machine.mem 21=w[4] := by
 have actual := congrArg Prod.snd observations
 simp only [List.cons.injEq,and_true] at actual
 rcases actual with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
 exact ⟨h0,h1,h3,h8,h17,h18,h21⟩

theorem wrong_cost : ¬GrowsAllocator 2 16 4 callee P.base ParentPrefixes.Checks.input
 MutatingSource.Checks.rootOut.st MutatingPrefixes.Checks.addresses machine := by
 intro wrong
 have wrongOwner := wrong (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide)
 have cursor := wrongOwner.arrays.free.cell
 change machine.mem 0=w[26] at cursor
 rw [target_facts.1] at cursor
 cases cursor

theorem wrong_parent : machine.mem 3≠w[0] := by rw [target_facts.2.2.1];decide
theorem unfinished_pointer : machine.mem 8≠w[14] := by rw [target_facts.2.2.2.1];decide
theorem wrong_alias : machine.mem 1≠w[20] := by rw [target_facts.2.1];decide
theorem missing_mutation : machine.mem 17≠w[7] := by rw [target_facts.2.2.2.2.1];decide
theorem unrelated_mutation : machine.mem 21≠w[1] := by rw [target_facts.2.2.2.2.2.2];decide

theorem not_revert : run image ParentPrefixes.Checks.input≠.revert := by
 rw [specification.1]
 intro impossible
 cases impossible

theorem not_fault : run image ParentPrefixes.Checks.input≠.fault := by
 rw [specification.1]
 intro impossible
 cases impossible

theorem bad_image : run image MutatingActivation.Checks.badMachine=.revert := by
 exact failing_loop (guardCompiled (C:=P.C) 2 F).code (MutatingActivation.code (C:=P.C) 2 F 8)
   (PairedUnwind.code 2 8 7 A) MutatingActivation.Checks.badMachine (MutatingPrefixes.Checks.bad_horizons 0)

theorem bad_not_fault : run image MutatingActivation.Checks.badMachine≠.fault := by
 rw [bad_image]
 intro impossible
 cases impossible

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingReturn
