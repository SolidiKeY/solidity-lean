import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarUnwind
import Solidity.Backend.InternalFlow.RuntimeFrameV3SecondAllocatingEntry

/-! An inhabited finite allocating scalar return using actual entry and unwind
instructions. Component compiler selection is retained; selection by a general
recursive compiler, a profile witness and world/physical-byte adequacy remain open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev F := AllocatingScalarTarget.F
def zeroState := SecondAllocatingEntry.child.setLocal .here (countValue 0 W_pos)
def oneState := finished (zeroState.setLocal (.there .here) (countValue 1 (by decide))) 1 (by decide)
def finalState := finished (oneState.setLocal (.there .here) (countValue 2 (by decide))) 2 (by decide)
def zeroCode : List Instr := [.push w[0],.mstore 4]
def stageCode := FullScalarUnwind.code (C:=P.C) 2 8 F
def image := SecondAllocatingEntry.image ++ (zeroCode ++ (stageCode ++ stageCode))

def zeroSelected : CompiledStmt 2 (C:=P.C) F (ScalarRecursiveSource.zero (R:=A)) :=
 ⟨F,_,.assign F .here (.simple (.lit 0 rfl)) _ (.core _ rfl)⟩
theorem zero_selection : Memory.compileStmt 2 F (ScalarRecursiveSource.zero (C:=P.C) (R:=A))=some zeroSelected := by rfl

theorem zero_code : zeroSelected.code=zeroCode := by rfl

theorem native_state : finalState=finished
 (AllocatingScalarSource.allocated (AllocatingScalarSource.allocated AllocatingScalarTarget.initial)) 2 (by decide) := by
 rfl

theorem native : (AllocatingScalarSource.body A rfl 3).run AllocatingScalarTarget.initial=
 .ok ⟨finalState,(AllocatingScalarSource.extension AllocatingScalarTarget.initial).trans
  (AllocatingScalarSource.extension (AllocatingScalarSource.allocated AllocatingScalarTarget.initial))⟩ := by
 exact AllocatingScalarSource.two_return rfl AllocatingScalarTarget.initial 0 P.r0 rfl rfl

theorem endpoint : ∃ last,
 run image AllocatorReturn.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F finalState SecondAllocatingEntry.addresses last ∧
 StructAllocatorRepr finalState.heap SecondAllocatingEntry.addresses 16 (⟨30,by decide⟩ : Fin W) last ∧
 finalState.H.length=4 ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 5,last.mem 8,last.mem 9,
 last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 14,last.mem 15,last.mem 17])=
 ([w[77]],[w[30],w[16],w[2],w[2],w[26],w[10],w[99],w[16],w[2],w[0],w[16],w[1],w[0],w[7]]) ∧
 last.mem 4≠w[0] ∧ last.mem 8≠w[16] ∧ last.mem 0≠w[22] := by
 obtain ⟨down,prefixRun,represented,owned,_,obs,_,_,_⟩ := SecondAllocatingEntry.endpoint
 have pointer : down.mem 8=w[16] := congrArg (fun t : List Word × List Word => t.2[5]!) obs
 have reference : down.mem 2=w[16] := congrArg (fun t : List Word × List Word => t.2[1]!) obs
 have nearRef : down.mem 13=w[16] := congrArg (fun t : List Word × List Word => t.2[10]!) obs
 have nearCounter : down.mem 14=w[1] := congrArg (fun t : List Word × List Word => t.2[11]!) obs
 have farRef : down.mem 10=w[16] := congrArg (fun t : List Word × List Word => t.2[7]!) obs
 have farCounter : down.mem 11=w[2] := congrArg (fun t : List Word × List Word => t.2[8]!) obs
 let zero := writeMachine down 4 w[0]
 have baseRun : run zeroCode down=.ok zero 0 := by rfl
 have zeroRepr : StateRepr 1 2 16 F zeroState SecondAllocatingEntry.addresses zero :=
   represented.setVal .here (countValue 0 W_pos) w[0] (ReprV.uint_of rfl)
 have zeroOwner : StructAllocatorRepr zeroState.heap SecondAllocatingEntry.addresses 16 (⟨30,by decide⟩ : Fin W) zero :=
   owned.localWrite 4 (by decide) (by decide) w[0]
 have zeroOutside (x : Nat) (hx : x≠4) : zero.mem x=down.mem x := upd_other _ _ hx
 obtain ⟨one,run1,repr1,stack1,cursor1,ref1,count1,result1,grow1,out1⟩ :=
   FullScalarUnwind.step zeroState SecondAllocatingEntry.addresses zero zeroRepr 0 (by decide) rfl
     8 8 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     ((zeroOutside 8 (by decide)).trans pointer)
     ((zeroOutside 13 (by decide)).trans (nearRef.trans (reference.symm.trans (zeroOutside 2 (by decide)).symm)))
     ((zeroOutside 14 (by decide)).trans nearCounter)
 have oneRepr : StateRepr 1 2 16 F oneState SecondAllocatingEntry.addresses one := repr1
 have oneRef : one.mem 2=w[16] := ref1.trans ((zeroOutside 2 (by decide)).trans reference)
 obtain ⟨last,run2,repr2,stack2,cursor2,ref2,count2,result2,grow2,out2⟩ :=
   FullScalarUnwind.step oneState SecondAllocatingEntry.addresses one oneRepr 1 (by decide) rfl
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cursor1
     ((out1 10 (by decide) (by decide) (by decide) (by decide)).trans
       ((zeroOutside 10 (by decide)).trans (farRef.trans oneRef.symm)))
     ((out1 11 (by decide) (by decide) (by decide) (by decide)).trans
       ((zeroOutside 11 (by decide)).trans farCounter))
 have owned1 := grow1 (⟨30,by decide⟩ : Fin W) (by decide) zeroOwner (by decide)
 have owned2 := grow2 (⟨30,by decide⟩ : Fin W) (by decide) owned1 (by decide)
 have outside (x : Nat) (hp : x≠8) (hr : x≠2) (hc : x≠3) (hv : x≠4) : last.mem x=down.mem x :=
   (out2 x hp hr hc hv).trans ((out1 x hp hr hc hv).trans (zeroOutside x hv))
 have refWord : last.mem 2=down.mem 2 := ref2.trans (ref1.trans (zeroOutside 2 (by decide)))
 have stack : last.stack=down.stack := stack2.trans stack1
 refine ⟨last,?_,repr2,owned2,rfl,?_,?_,?_,?_⟩
 · change run (SecondAllocatingEntry.image ++ (zeroCode ++ (stageCode ++ stageCode))) _=_
   rw [run_append_ok prefixRun,run_append_ok baseRun]
   change run (FullScalarUnwind.code (C:=P.C) 2 8 F ++ FullScalarUnwind.code (C:=P.C) 2 8 F) zero=_
   exact (run_append_ok run1).trans run2
 · rw [stack,outside 0 (by decide) (by decide) (by decide) (by decide),refWord,count2,result2,
     outside 5 (by decide) (by decide) (by decide) (by decide),cursor2,
     outside 9 (by decide) (by decide) (by decide) (by decide),
     outside 10 (by decide) (by decide) (by decide) (by decide),
     outside 11 (by decide) (by decide) (by decide) (by decide),
     outside 12 (by decide) (by decide) (by decide) (by decide),
     outside 13 (by decide) (by decide) (by decide) (by decide),
     outside 14 (by decide) (by decide) (by decide) (by decide),
     outside 15 (by decide) (by decide) (by decide) (by decide),
     outside 17 (by decide) (by decide) (by decide) (by decide)]
   exact congrArg (fun t : List Word × List Word =>
     (t.1,[t.2[0]!,t.2[1]!,w[2],w[2],t.2[4]!,w[10],t.2[6]!,t.2[7]!,t.2[8]!,t.2[9]!,t.2[10]!,t.2[11]!,t.2[12]!,t.2[13]!])) obs
 · rw [result2]
   decide
 · rw [cursor2]
   decide
 · have allocator : down.mem 0=w[30] := congrArg (fun t : List Word × List Word => t.2[0]!) obs
   rw [outside 0 (by decide) (by decide) (by decide) (by decide),allocator]
   decide

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.zero_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.zero_selection

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.zero_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.zero_code

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.native_state' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.native_state

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.native

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarEndpoint.endpoint
