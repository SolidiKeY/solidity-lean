import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarPrefixes
import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarLoopControls

/-! A represented midpoint of the actual allocating return loop, followed by
resumption on the SAME bottom word/code. Source recursive compilation and
arbitrary descent-history provenance remain separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource FullScalarLoop CountdownWitness
abbrev F := AllocatingScalarTarget.F
def midpoint := returned SecondAllocatingEntry.child 0 1 (by decide)
def inputCode := SecondAllocatingEntry.image ++ [.push w[10],.mstore 7]

theorem endpoint : ∃ entry target last,
 run inputCode AllocatorReturn.Checks.input=.ok entry 0 ∧
 loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 1 entry=.inl target ∧
 StateRepr 1 2 16 F midpoint SecondAllocatingEntry.addresses target ∧
 StructAllocatorRepr midpoint.heap SecondAllocatingEntry.addresses 16 (⟨30,by decide⟩ : Fin W) target ∧
 (target.stack,[target.mem 0,target.mem 2,target.mem 3,target.mem 4,target.mem 5,target.mem 7,target.mem 8,target.mem 9,
 target.mem 10,target.mem 11,target.mem 12,target.mem 13,target.mem 14,target.mem 15,target.mem 17])=
 ([w[77]],[w[30],w[16],w[1],w[1],w[26],w[10],w[13],w[99],w[16],w[2],w[0],w[16],w[1],w[0],w[7]]) ∧
 loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 2 target=.inr (.ok last 0) ∧
 run (FullScalarLoop.code (C:=P.C) (R:=A) 2 8 7 F) target=.ok last 0 ∧
 StateRepr 1 2 16 F FullScalarLoop.Controls.finalState SecondAllocatingEntry.addresses last ∧
 StructAllocatorRepr FullScalarLoop.Controls.finalState.heap SecondAllocatingEntry.addresses 16 (⟨30,by decide⟩ : Fin W) last ∧
 target.mem 4≠target.mem 15 ∧ target.mem 3≠target.mem 11 ∧
 loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 1 entry≠.inr (.ok target 0) := by
 obtain ⟨down,prefixRun,represented,owned,_,obs,_,_,_⟩ := SecondAllocatingEntry.endpoint
 have pointer : down.mem 8=w[16] := congrArg (fun t : List Word × List Word => t.2[5]!) obs
 have reference : down.mem 2=w[16] := congrArg (fun t : List Word × List Word => t.2[1]!) obs
 have nearRef : down.mem 13=w[16] := congrArg (fun t : List Word × List Word => t.2[10]!) obs
 have nearCounter : down.mem 14=w[1] := congrArg (fun t : List Word × List Word => t.2[11]!) obs
 have farRef : down.mem 10=w[16] := congrArg (fun t : List Word × List Word => t.2[7]!) obs
 have farCounter : down.mem 11=w[2] := congrArg (fun t : List Word × List Word => t.2[8]!) obs
 let entry := writeMachine down 7 w[10]
 have setup : run [.push w[10],.mstore 7] down=.ok entry 0 := by rfl
 have repr : StateRepr 1 2 16 F SecondAllocatingEntry.child SecondAllocatingEntry.addresses entry :=
   reserved_write represented 7 (by decide) (by decide) w[10]
 have owner : StructAllocatorRepr SecondAllocatingEntry.child.heap SecondAllocatingEntry.addresses 16 (⟨30,by decide⟩ : Fin W) entry :=
   owned.localWrite 7 (by decide) (by decide) w[10]
 have untouched (x : Nat) (hx : x≠7) : entry.mem x=down.mem x := upd_other _ _ hx
 have history : ∀ j,j<2 → entry.mem (10+3*j)=entry.mem 2 ∧
     entry.mem (10+3*j+1)=.val (wmod (0+2-j)) := by
   intro j small
   rcases (by omega : j=0 ∨ j=1) with rfl | rfl
   · exact ⟨(untouched 10 (by decide)).trans (farRef.trans (reference.symm.trans (untouched 2 (by decide)).symm)),
       (untouched 11 (by decide)).trans farCounter⟩
   · exact ⟨(untouched 13 (by decide)).trans (nearRef.trans (reference.symm.trans (untouched 2 (by decide)).symm)),
       (untouched 14 (by decide)).trans nearCounter⟩
 obtain ⟨target,running,targetRepr,growth,stack,cursor,targetBottom,alias,remaining,exterior⟩ :=
   at_horizon 1 2 0 (by decide) SecondAllocatingEntry.child SecondAllocatingEntry.addresses entry repr (by decide) rfl
     8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) ((untouched 8 (by decide)).trans pointer) rfl history
 have allocation := growth (⟨30,by decide⟩ : Fin W) (by decide) owner (by decide)
 have resultValue : TEnv.get (.here : Idx (Frame A) (.val .uint)) midpoint.env=countValue 1 (by decide) :=
   returned_value SecondAllocatingEntry.child 0 1 (by decide) rfl
 obtain ⟨last,_,stopped,lastRepr,lastGrowth,_,_,_,_⟩ :=
   FullScalarLoop.iter 1 1 midpoint SecondAllocatingEntry.addresses target targetRepr (by decide) resultValue
     8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) cursor targetBottom remaining
 have lastOwner := lastGrowth (⟨30,by decide⟩ : Fin W) (by decide) allocation (by decide)
 have stateEq : returned midpoint 1 1 (by decide)=FullScalarLoop.Controls.finalState :=
   returned_succ SecondAllocatingEntry.child 0 1 (by decide)
 rw [stateEq] at lastRepr lastOwner
 have resultRepr := targetRepr.core.vals (.here : Idx (Frame A) (.val .uint))
 change ReprV .uint (countValue 1 (by decide)) (target.mem 4) at resultRepr
 have resultWord : target.mem 4=w[1] := Restore.uint_unique resultRepr (ReprV.uint_of rfl)
 have counterRepr := targetRepr.core.vals (.there .here : Idx (Frame A) (.val .uint))
 change ReprV .uint (countValue 1 (by decide)) (target.mem 3) at counterRepr
 have counterWord : target.mem 3=w[1] := Restore.uint_unique counterRepr (ReprV.uint_of rfl)
 have preserved (x : Nat) (hp : x≠8) (hr : x≠2) (hc : x≠3) (hv : x≠4) (hb : x≠7) : target.mem x=down.mem x :=
   (exterior x hp hr hc hv).trans (untouched x hb)
 have refWord : target.mem 2=down.mem 2 := alias.trans (untouched 2 (by decide))
 have savedZero : target.mem 15=w[0] := (preserved 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
   (congrArg (fun t : List Word × List Word => t.2[12]!) obs)
 have parentCounter : target.mem 11=w[2] := (preserved 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans farCounter
 refine ⟨entry,target,last,(run_append_ok prefixRun).trans setup,running,targetRepr,allocation,?_,stopped,
   FullScalarLoop.run_of_stopped stopped,lastRepr,lastOwner,?_,?_,?_⟩
 · rw [stack,preserved 0 (by decide) (by decide) (by decide) (by decide) (by decide),refWord,
     counterWord,resultWord,preserved 5 (by decide) (by decide) (by decide) (by decide) (by decide),targetBottom,cursor,
     preserved 9 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 10 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 11 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 12 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 13 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 14 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 15 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 17 (by decide) (by decide) (by decide) (by decide) (by decide)]
   exact congrArg (fun t : List Word × List Word =>
     (t.1,[t.2[0]!,t.2[1]!,w[1],w[1],t.2[4]!,w[10],w[13],t.2[6]!,t.2[7]!,t.2[8]!,t.2[9]!,t.2[10]!,t.2[11]!,t.2[12]!,t.2[13]!])) obs
 · rw [resultWord,savedZero]
   decide
 · rw [counterWord,parentCounter]
   decide
 · rw [running]
   intro wrong
   cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.Controls.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.Controls.endpoint
