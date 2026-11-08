import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTurn

/-! Two genuine allocating activations with distinct captured parent counters.
This is an actual finite entry prefix, not a recursive compiler/return theorem. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.SecondAllocatingEntry
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource AllocatingScalarEntry
open CountdownWitness
abbrev F := AllocatingScalarTarget.F
def parent := entered AllocatingScalarTarget.after 1 (by decide) AllocatingScalarEntry.Checks.ref
def ref : HRef (AllocatingScalarSource.allocated parent).H A :=
 AllocatingScalarEntry.Checks.ref.wk (AllocatingScalarSource.extension parent)
def child := entered (AllocatingScalarSource.allocated parent) 0 W_pos ref
def addresses := upd AllocatingScalarTarget.addresses parent.H.length (⟨26,by decide⟩ : Fin W)
def initialCode := [.push w[0],.mstore 4] ++
 (AllocatingScalarTarget.selected.code ++ AllocatingScalarEntry.Checks.image)
def image := initialCode ++ AllocatingScalarTurn.code 8

theorem endpoint : ∃ target,
 run image AllocatorReturn.Checks.input=.ok target 0 ∧
 StateRepr 1 2 16 F child addresses target ∧
 StructAllocatorRepr child.heap addresses 16 (⟨30,by decide⟩ : Fin W) target ∧
 child.H.length=4 ∧
 (target.stack,[target.mem 0,target.mem 2,target.mem 3,target.mem 4,target.mem 5,target.mem 8,target.mem 9,
 target.mem 10,target.mem 11,target.mem 12,target.mem 13,target.mem 14,target.mem 15,target.mem 17])=
 ([w[77]],[w[30],w[16],w[0],w[0],w[26],w[16],w[99],w[16],w[2],w[0],w[16],w[1],w[0],w[7]]) ∧
 target.mem 3≠target.mem 14 ∧ target.mem 11≠target.mem 14 ∧ target.mem 0≠w[34] := by
 obtain ⟨saved,first,_,_,_,prefixRun,repr,owned,obs,_,_,_⟩ := AllocatingScalarEntry.Checks.endpoint
 have firstPointer : first.mem 8=w[13] :=
   congrArg (fun t : List Word × List Word => t.2[5]!) obs
 obtain ⟨target,source,actual,represented,allocation,extended,stack,pointer,cursor,counter,resultWord,privateWord,payload,exterior⟩ :=
   AllocatingScalarTurn.turn (L:=1) (frame:=16) parent 0 (by decide) AllocatingScalarEntry.Checks.ref rfl rfl
     AllocatingScalarTarget.addresses first repr (⟨26,by decide⟩ : Fin W) owned (by decide) 8 8 13
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) firstPointer
 have firstStack : first.stack=[w[77]] := congrArg Prod.fst obs
 have firstAlias : first.mem 2=w[16] := congrArg (fun t : List Word × List Word => t.2[1]!) obs
 have firstCounter : first.mem 3=w[1] := congrArg (fun t : List Word × List Word => t.2[2]!) obs
 have firstResult : first.mem 4=w[0] := congrArg (fun t : List Word × List Word => t.2[3]!) obs
 have sentinel : first.mem 9=w[99] := congrArg (fun t : List Word × List Word => t.2[6]!) obs
 have oldAlias : first.mem 10=w[16] := congrArg (fun t : List Word × List Word => t.2[7]!) obs
 have oldCounter : first.mem 11=w[2] := congrArg (fun t : List Word × List Word => t.2[8]!) obs
 have oldResult : first.mem 12=w[0] := congrArg (fun t : List Word × List Word => t.2[9]!) obs
 have oldElement : first.mem 17=w[7] := congrArg (fun t : List Word × List Word => t.2[11]!) obs
 have unchanged (x : Nat) (h0 : x≠0) (h3 : x≠3) (h4 : x≠4) (h5 : x≠5)
     (hp : x≠8) (hc : x≠26) (outside : x<13 ∨ 16≤x) : target.mem x=first.mem x :=
   exterior x h0 h3 h4 h5 hp hc outside
 have aliasWord : target.mem 2=w[16] := (unchanged 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans firstAlias
 have sentinelWord : target.mem 9=w[99] := (unchanged 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans sentinel
 have oldestAlias : target.mem 10=w[16] := (unchanged 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans oldAlias
 have oldestCounter : target.mem 11=w[2] := (unchanged 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans oldCounter
 have oldestResult : target.mem 12=w[0] := (unchanged 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans oldResult
 have element : target.mem 17=w[7] := (unchanged 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans oldElement
 have savedAlias : target.mem 13=w[16] := (payload 0 (by decide)).trans firstAlias
 have savedCounter : target.mem 14=w[1] := (payload 1 (by decide)).trans firstCounter
 have savedResult : target.mem 15=w[0] := (payload 2 (by decide)).trans firstResult
 refine ⟨target,(run_append_ok prefixRun).trans actual,represented,allocation,rfl,?_,?_,?_,?_⟩
 · rw [stack,firstStack,cursor,aliasWord,counter,resultWord,privateWord,pointer,sentinelWord,
     oldestAlias,oldestCounter,oldestResult,savedAlias,savedCounter,savedResult,element]
   rfl
 · rw [counter,savedCounter]
   decide
 · rw [oldestCounter,savedCounter]
   decide
 · rw [cursor]
   decide

end Solidity.Backend.InternalFlow.RuntimeFrame.SecondAllocatingEntry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.SecondAllocatingEntry.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.SecondAllocatingEntry.endpoint
