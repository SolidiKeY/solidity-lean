import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarContinuation

/-! Complete observations and non-vacuity controls for a returned scalar
consumed by both mutation and allocation. The suffix reuses the old alias;
its private local is dropped, while its new heap object remains allocated. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarContinuation.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

theorem complete_observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 4,target.mem 5,target.mem 6,target.mem 7,target.mem 8,target.mem 9,target.mem 10,target.mem 11,target.mem 12,target.mem 13,target.mem 14,target.mem 15,target.mem 16,target.mem 17,target.mem 18,target.mem 19,target.mem 20,target.mem 21,target.mem 22,target.mem 23,target.mem 24,target.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[2],w[3],w[22],w[3],w[3],w[10],w[10],w[16],w[3],w[16],w[2],w[16],w[1],w[2],w[3],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 have old1 : machine.mem 1=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[1]?) snapshot)
 have old2 : machine.mem 2=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[2]?) snapshot)
 have old3 : machine.mem 3=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[3]?) snapshot)
 have old4 : machine.mem 4=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[4]?) snapshot)
 have old6 : machine.mem 6=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[6]?) snapshot)
 have old7 : machine.mem 7=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[7]?) snapshot)
 have old8 : machine.mem 8=w[10] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[8]?) snapshot)
 have old9 : machine.mem 9=w[10] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[9]?) snapshot)
 have old10 : machine.mem 10=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[10]?) snapshot)
 have old11 : machine.mem 11=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[11]?) snapshot)
 have old12 : machine.mem 12=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[12]?) snapshot)
 have old13 : machine.mem 13=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[13]?) snapshot)
 have old14 : machine.mem 14=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[14]?) snapshot)
 have old15 : machine.mem 15=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[15]?) snapshot)
 have old16 : machine.mem 16=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[16]?) snapshot)
 have old18 : machine.mem 18=w[9] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[18]?) snapshot)
 have old19 : machine.mem 19=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[19]?) snapshot)
 have old20 : machine.mem 20=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[20]?) snapshot)
 have old21 : machine.mem 21=w[4] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[21]?) snapshot)
 have zero23 : machine.mem 23=w[0] := owner.arrays.free.zero 23 (by decide)
 have zero24 : machine.mem 24=w[0] := owner.arrays.free.zero 24 (by decide)
 have zero25 : machine.mem 25=w[0] := owner.arrays.free.zero 25 (by decide)
 change (machine.stack,[w[26],machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,w[22],machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,w[3],machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21,w[3],machine.mem 23,machine.mem 24,machine.mem 25])=_
 rw [specification.2.2.2.1,old1,old2,old3,old4,old6,old7,old8,old9,old10,old11,old12,old13,old14,old15,old16,old18,old19,old20,old21,zero23,zero24,zero25]


theorem source_bindings :
 ((TEnv.get (.here : Idx Γ (.val .uint)) final.env).val,
 (TEnv.get (.there .here : Idx Γ (.val .uint)) final.env).val,
 (TEnv.get (.there (.there .here) : Idx Γ (.mem CountdownWitness.A)) final.env).map HRef.id,
 (TEnv.get (.there (.there (.there .here)) : Idx Γ (.mem CountdownWitness.A)) final.env).map HRef.id,
 final.H.length)=(3,2,some 0,some 0,3) := by
 with_unfolding_all rfl

theorem source_objects :
 let old := ref.wk extension
 let fresh := (changed.alloc (defaultArray .uint size)).2
 let privateOld := CompileExamples.r1.wk extension
 (old.id,privateOld.id,fresh.id,final.heap.len old .dyn,final.heap.len privateOld .dyn,final.heap.len fresh .dyn,
 [final.heap.readAddr (.index old .dyn (countValue 0 W_pos)),
  final.heap.readAddr (.index old .dyn (countValue 1 (by decide))),
  final.heap.readAddr (.index privateOld .dyn (countValue 0 W_pos)),
  final.heap.readAddr (.index fresh .dyn (countValue 0 W_pos)),
  final.heap.readAddr (.index fresh .dyn (countValue 1 (by decide))),
  final.heap.readAddr (.index fresh .dyn (countValue 2 (by decide)))])=
 (0,1,2,2,1,3,[some (CountdownWitness.P.uint 3 (by decide)),some (CountdownWitness.P.uint 9 (by decide)),
 some (CountdownWitness.P.uint 4 (by decide)),some (CountdownWitness.P.uint 0 W_pos),
 some (CountdownWitness.P.uint 0 W_pos),some (CountdownWitness.P.uint 0 W_pos)]) := by
 with_unfolding_all rfl

theorem writes_returned_value : target.mem 17=w[3] :=
 Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[17]?) complete_observations)

theorem allocation_uses_returned_length : target.mem 22=w[3] :=
 Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[22]?) complete_observations)

theorem wrong_old_scalar : target.mem 17≠w[77] := by
 rw [writes_returned_value]
 decide

theorem wrong_old_frontier : target.mem 0≠w[22] := by
 have cursor : target.mem 0=w[26] := allocation_facts.2.2.1.arrays.free.cell
 rw [cursor]
 decide

theorem distinct_private_identity : target.mem 5=w[22] ∧ target.mem 5≠target.mem 1 := by
 have privateWord : target.mem 5=w[22] :=
   Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[5]?) complete_observations)
 have oldWord : target.mem 1=w[16] :=
   Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[1]?) complete_observations)
 exact ⟨privateWord,by rw [privateWord,oldWord];decide⟩

theorem failure_absorbs_suffix (depth : Nat) :
 (program depth).run ScalarDual.rejectedCaller=.error .revert ∧
 run image ScalarDual.rejectedMachine=.revert := by
 have failed := ScalarClaims.source_revert rfl reference ScalarDual.choice .here "scalarCountdown" depth
   ScalarDual.rejectedCaller ScalarDual.bad_eval
 constructor
 · change TRun.seq (ScalarDual.statement depth).runR suffix.runR ScalarDual.rejectedCaller=_
   change (ScalarDual.statement depth).runR ScalarDual.rejectedCaller=.error .revert at failed
   simp only [TRun.seq,failed]
 · exact run_append_revert (ScalarDemandDual.bad_execution 4)

theorem shallow_source : (program 3).run caller=.error .exhausted := by
 have shallow := ScalarClaims.source_value rfl reference ScalarDual.choice .here "scalarCountdown" 3 caller
   CountdownWitness.P.r0 (by with_unfolding_all rfl) (countValue 3 (by decide)) ScalarDual.good_eval
 rw [if_neg (show ¬(countValue 3 (by decide)).word.val<3 from by decide)] at shallow
 change (ScalarDual.statement 3).runR caller=.error .exhausted at shallow
 change TRun.seq (ScalarDual.statement 3).runR suffix.runR caller=_
 simp only [TRun.seq,shallow]

theorem target_not_revert : run image before≠.revert := by
 rw [target_execution]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarContinuation.Controls
