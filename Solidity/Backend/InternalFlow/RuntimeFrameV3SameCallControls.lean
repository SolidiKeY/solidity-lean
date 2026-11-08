import Solidity.Backend.InternalFlow.RuntimeFrameV3SameCallDual

/-! Complete observations of the successful rebinding input to failure.
Nothing here observes a state returned by the reverting call. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.SameCallControls
noncomputable section
open Evm Evm.Memory
open DisjointScalarReturn.Client (Γ F reference)
open SameCallInputs (C A origin caller before machine fresh)

def old0 : HRef caller.H A := CountdownWitness.P.r0.wk (ScalarContinuation.extension.trans (List.prefix_append _ _))
def old1 : HRef caller.H A := CompileExamples.r1.wk (ScalarContinuation.extension.trans (List.prefix_append _ _))
def old2 : HRef caller.H A := (ScalarContinuation.changed.alloc (defaultArray .uint ScalarContinuation.size)).2.wk (List.prefix_append _ _)

theorem source_locals :
 ((TEnv.get (.here : Idx Γ (.val .uint)) caller.env).val,
  (TEnv.get (.there .here : Idx Γ (.val .uint)) caller.env).val,
  (TEnv.get reference caller.env).map HRef.id,
  (TEnv.get (.there (.there (.there .here)) : Idx Γ (.mem A)) caller.env).map HRef.id)=
 ((3:Int),(2:Int),some 3,some 0) := by
 with_unfolding_all rfl

theorem source_objects :
 ([old0.id,old1.id,old2.id,fresh.id],
 [(caller.heap.get old0).1.map (fun value => value.val),
  (caller.heap.get old1).1.map (fun value => value.val),
  (caller.heap.get old2).1.map (fun value => value.val),
  (caller.heap.get fresh).1.map (fun value => value.val)])=
 ([0,1,2,3],[[3,9],[4],[0,0,0],[]]) := by
 with_unfolding_all rfl

theorem snapshot :
 (machine.stack,(List.range 27).map (fun index => machine.mem index))=
 ([w[77]],[w[27],w[16],w[26],w[2],w[3],w[22],w[3],w[3],w[10],w[10],w[16],w[3],w[16],w[2],w[16],w[1],
 w[2],w[3],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0],w[0]]) := by
 have saved := ScalarContinuation.Controls.complete_observations
 have stack : before.stack=[w[77]] := congrArg Prod.fst saved
 have old1 : before.mem 1=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[1]?) saved)
 have old3 : before.mem 3=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[3]?) saved)
 have old4 : before.mem 4=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[4]?) saved)
 have old5 : before.mem 5=w[22] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[5]?) saved)
 have old6 : before.mem 6=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[6]?) saved)
 have old7 : before.mem 7=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[7]?) saved)
 have old8 : before.mem 8=w[10] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[8]?) saved)
 have old9 : before.mem 9=w[10] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[9]?) saved)
 have old10 : before.mem 10=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[10]?) saved)
 have old11 : before.mem 11=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[11]?) saved)
 have old12 : before.mem 12=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[12]?) saved)
 have old13 : before.mem 13=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[13]?) saved)
 have old14 : before.mem 14=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[14]?) saved)
 have old15 : before.mem 15=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[15]?) saved)
 have old16 : before.mem 16=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[16]?) saved)
 have old17 : before.mem 17=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[17]?) saved)
 have old18 : before.mem 18=w[9] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[18]?) saved)
 have old19 : before.mem 19=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[19]?) saved)
 have old20 : before.mem 20=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[20]?) saved)
 have old21 : before.mem 21=w[4] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[21]?) saved)
 have old22 : before.mem 22=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[22]?) saved)
 have old23 : before.mem 23=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[23]?) saved)
 have old24 : before.mem 24=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[24]?) saved)
 have old25 : before.mem 25=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[25]?) saved)
 change (before.stack,[w[27],before.mem 1,w[26],before.mem 3,before.mem 4,before.mem 5,before.mem 6,before.mem 7,before.mem 8,before.mem 9,before.mem 10,before.mem 11,before.mem 12,before.mem 13,before.mem 14,before.mem 15,before.mem 16,before.mem 17,before.mem 18,before.mem 19,before.mem 20,before.mem 21,before.mem 22,before.mem 23,before.mem 24,before.mem 25,w[0]])=_
 rw [stack,old1,old3,old4,old5,old6,old7,old8,old9,old10,old11,old12,old13,old14,old15,old16,old17,old18,old19,old20,old21,old22,old23,old24,old25]

theorem different_callers : caller≠origin := by
  intro same
  have sizes := congrArg (fun state : State C Γ => state.H.length) same
  change (4:Nat)=3 at sizes
  cases sizes

theorem wrong_cost : SameCallInputs.checked.cost origin≠0 := by
  rw [SameCallInputs.exact_cost]
  decide

theorem wrong_frontier : machine.mem 0≠w[26] := by
  have actual : machine.mem 0=w[27] := Option.some.inj
    (congrArg (fun observed : List Word × List Word => observed.2[0]?) snapshot)
  rw [actual]
  decide

theorem wrong_alias : (TEnv.get reference caller.env).map HRef.id≠some 0 := by
  have actual := congrArg (fun observed : Int × Int × Option Nat × Option Nat => observed.2.2.1) source_locals
  change (TEnv.get reference caller.env).map HRef.id=some 3 at actual
  rw [actual]
  decide

theorem not_fault (depth : Nat) : run (SameCallDual.selected depth).plan.code machine≠.fault := by
  rw [SameCallDual.target_revert]
  intro wrong
  cases wrong

end
end Solidity.Backend.InternalFlow.RuntimeFrame.SameCallControls
