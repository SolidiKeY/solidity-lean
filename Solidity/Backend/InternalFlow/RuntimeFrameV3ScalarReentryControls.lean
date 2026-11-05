import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarReentryEndpoint

/-! Complete source/target re-entry observations. The second call consumes a
real mutated-heap argument and retains the object allocated before entry.
The previous caller, physical snapshots, admission and refusal controls stay
unchanged. Exhausted source quotations are not successful source runs. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReentry.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F caller before reference)
open Endpoint

theorem complete_observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21,machine.mem 22,machine.mem 23,machine.mem 24,machine.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],w[16],w[2],w[16],w[1],w[2],w[3],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 rcases specification with ⟨executed,represented,stack,extended,destination,privateResult,counter,alias,cursor,bottom,growth,outside,saved⟩
 have referenceWord : input.mem 2=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[2]?) ScalarContinuation.Controls.complete_observations)
 have old0 : input.mem 0=w[26] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[0]?) ScalarContinuation.Controls.complete_observations)
 have old1 : input.mem 1=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[1]?) ScalarContinuation.Controls.complete_observations)
 have old2 : input.mem 2=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[2]?) ScalarContinuation.Controls.complete_observations)
 have old3 : input.mem 3=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[3]?) ScalarContinuation.Controls.complete_observations)
 have old16 : input.mem 16=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[16]?) ScalarContinuation.Controls.complete_observations)
 have old17 : input.mem 17=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[17]?) ScalarContinuation.Controls.complete_observations)
 have old18 : input.mem 18=w[9] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[18]?) ScalarContinuation.Controls.complete_observations)
 have old19 : input.mem 19=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[19]?) ScalarContinuation.Controls.complete_observations)
 have old20 : input.mem 20=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[20]?) ScalarContinuation.Controls.complete_observations)
 have old21 : input.mem 21=w[4] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[21]?) ScalarContinuation.Controls.complete_observations)
 have old22 : input.mem 22=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[22]?) ScalarContinuation.Controls.complete_observations)
 have old23 : input.mem 23=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[23]?) ScalarContinuation.Controls.complete_observations)
 have old24 : input.mem 24=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[24]?) ScalarContinuation.Controls.complete_observations)
 have old25 : input.mem 25=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[25]?) ScalarContinuation.Controls.complete_observations)
 have inputStack : input.stack=[w[77]] := congrArg Prod.fst ScalarContinuation.Controls.complete_observations
 rw [stack,
   inputStack,
   destination,
   privateResult,
   counter,
   alias,
   referenceWord,
   cursor,
   bottom,
   outside 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   old0,
   outside 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   old1,
   outside 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   old2,
   outside 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   old3,
   outside 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old16,
   outside 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old17,
   outside 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old18,
   outside 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old19,
   outside 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old20,
   outside 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old21,
   outside 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old22,
   outside 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old23,
   outside 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old24,
   outside 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   old25,
   (saved 0 (by decide)).1,
   (saved 0 (by decide)).2,
   (saved 1 (by decide)).1,
   (saved 1 (by decide)).2,
   (saved 2 (by decide)).1,
   (saved 2 (by decide)).2,referenceWord]
 decide +kernel


theorem source_state : resultState=ScalarContinuation.final := by
 with_unfolding_all rfl

theorem source_objects :
 let old := ScalarContinuation.ref.wk ScalarContinuation.extension
 let fresh := (ScalarContinuation.changed.alloc (defaultArray .uint ScalarContinuation.size)).2
 let privateOld := CompileExamples.r1.wk ScalarContinuation.extension
 (old.id,privateOld.id,fresh.id,resultState.heap.len old .dyn,resultState.heap.len privateOld .dyn,resultState.heap.len fresh .dyn,
 [resultState.heap.readAddr (.index old .dyn (countValue 0 W_pos)),
  resultState.heap.readAddr (.index old .dyn (countValue 1 (by decide))),
  resultState.heap.readAddr (.index privateOld .dyn (countValue 0 W_pos)),
  resultState.heap.readAddr (.index fresh .dyn (countValue 0 W_pos)),
  resultState.heap.readAddr (.index fresh .dyn (countValue 1 (by decide))),
  resultState.heap.readAddr (.index fresh .dyn (countValue 2 (by decide)))])=
 (0,1,2,2,1,3,[some (CountdownWitness.P.uint 3 (by decide)),some (CountdownWitness.P.uint 9 (by decide)),
 some (CountdownWitness.P.uint 4 (by decide)),some (CountdownWitness.P.uint 0 W_pos),
 some (CountdownWitness.P.uint 0 W_pos),some (CountdownWitness.P.uint 0 W_pos)]) := by
 exact ScalarContinuation.Controls.source_objects

theorem wrong_old_count : ScalarReentry.count.evalT ScalarContinuation.final≠.ok (countValue 7 (by decide)) := rejects_stale_count

theorem wrong_frontier : machine.mem 0≠w[22] := by
 rw [ownership.arrays.free.cell]
 decide

theorem retained_new_identity : addresses 2=⟨22,by decide⟩ ∧ addresses 2≠⟨16,by decide⟩ :=
 ⟨new_object_base,by rw [new_object_base];decide⟩

theorem shallow_source : (statement 3).run ScalarContinuation.final=.error .exhausted := by
 simpa only [if_neg (show ¬(3:Nat)<3 from by decide)] using source 3

theorem not_fault : run (ScalarContinuation.image++(plan.at 4).code) before≠.fault := by
 rw [whole_target]
 intro wrong
 cases wrong

theorem not_revert : run (ScalarContinuation.image++(plan.at 4).code) before≠.revert := by
 rw [whole_target]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReentry.Controls
