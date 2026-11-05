import Solidity.Backend.InternalFlow.RuntimeFrameCodeAuthentication
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarEmitterControls

/-! The full selected recursive image is authenticated through both loop
children, then transported to the unchanged populated endpoint. Small nested
controls exercise condition/body order and wrong destination/cursor rejection.
No general source selector or physical EVM claim is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CodeAuthentication.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

def candidate : List Instr :=
 ([.mload 2,.mstore 5] ++ [.push w[3],.mstore 6,.push w[0],.mstore 7]) ++
 (ScalarDescent.image (C:=CountdownWitness.P.C) 5 (Frag.init (Parameters CountdownWitness.A)) 9 8 ++
  (ScalarPrefixes.image (C:=CountdownWitness.P.C) 5 9 8 ((Frag.init (Parameters CountdownWitness.A)).push (.val .uint) .ok) ++
   [.mload 7,.mstore 4]))

theorem construction : candidate=ScalarEmitter.Client.emitted.code reference (.here : Idx Γ (.val .uint)) := by
 simp only [candidate,ScalarEmitter.Emission.code,DisjointScalarReturn.code,DisjointScalarEntry.code,
   ScalarReturn.image,List.append_assoc]
 rfl

theorem selected_image : code candidate (ScalarEmitter.Client.emitted.code reference (.here : Idx Γ (.val .uint)))=true := by
 rw [construction]
 exact code_self _

theorem emitted_equality : candidate=ScalarEmitter.Client.emitted.code reference (.here : Idx Γ (.val .uint)) :=
 code_sound selected_image

theorem target : run candidate before=.ok machine 0 := by
 rw [run_equal selected_image]
 exact ScalarEmitter.Client.target

theorem complete_observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[0],w[1],w[4]]) := ScalarEmitter.Client.complete_observations

theorem caller_frame : StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses machine :=
 ScalarEmitter.Client.restored_caller

def nested : List Instr := [.loop [.push w[1]] [.loop [.push w[0]] [.mload 7,.mstore 4]]]

theorem nested_positive : code nested nested=true := code_self nested

theorem inner_body_negative : code nested [.loop [.push w[1]] [.loop [.push w[0]] [.mload 7,.mstore 3]]]=false := by
 simp only [nested,code,instruction,CodeEquality.instruction]
 decide +kernel

theorem inner_condition_negative : code nested [.loop [.push w[1]] [.loop [.push w[1]] [.mload 7,.mstore 4]]]=false := by
 simp only [nested,code,instruction,CodeEquality.instruction]
 decide +kernel

theorem loop_order_negative : code nested [.loop [.loop [.push w[0]] [.mload 7,.mstore 4]] [.push w[1]]]=false := by
 simp only [nested,code,instruction,CodeEquality.instruction]
 decide +kernel

theorem wrong_destination : code candidate (ScalarEmitter.Client.emitted.code reference (.there .here : Idx Γ (.val .uint)))=false := by
 rw [construction]
 simp only [ScalarEmitter.Emission.code,DisjointScalarReturn.code,DisjointScalarEntry.code,
   ScalarReturn.image,ScalarEmitter.Client.selected_argument,List.append_assoc,common_prefix]
 simp only [code,instruction,CodeEquality.instruction]
 decide +kernel

theorem wrong_cursor : code candidate (DisjointScalarReturn.code 1 5 reference value (.here : Idx Γ (.val .uint)) 10 8)=false := by
 rw [construction]
 simp only [ScalarEmitter.Emission.code,DisjointScalarReturn.code,DisjointScalarEntry.code,
   ScalarReturn.image,ScalarEmitter.Client.selected_argument,List.append_assoc,common_prefix]
 simp only [ScalarDescent.image,List.append_assoc,List.cons_append,List.nil_append,code,instruction,CodeEquality.instruction]
 decide +kernel

theorem missing_instruction : code candidate (ScalarEmitter.Client.emitted.code reference (.here : Idx Γ (.val .uint)) ++ [.pop])=false := by
 rw [construction]
 simp only [ScalarEmitter.Emission.code,DisjointScalarReturn.code,DisjointScalarEntry.code,
   ScalarReturn.image,ScalarEmitter.Client.selected_argument,List.append_assoc,common_prefix]
 simp only [List.cons_append,List.nil_append,code,instruction,CodeEquality.instruction]
 decide +kernel


end Solidity.Backend.InternalFlow.RuntimeFrame.CodeAuthentication.Client
