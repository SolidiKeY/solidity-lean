import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarLoop
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarEndpoint

/-! Actual populated loop return from the existing two allocating activations.
A checked reserved-word write installs the bottom cursor; the old fixture and
its sentinel remain unchanged. This is not general recursive compilation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev F := AllocatingScalarTarget.F
def finalState := returned SecondAllocatingEntry.child 0 2 (by decide)
def image := SecondAllocatingEntry.image ++ ([.push w[10],.mstore 7] ++ FullScalarLoop.code (C:=P.C) (R:=A) 2 8 7 F)

theorem native_state : finalState=AllocatingScalarEndpoint.finalState := by rfl

theorem endpoint : ∃ entry last,
 loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 0 entry=.inl entry ∧
 (∃ mid,loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 1 entry=.inl mid) ∧
 loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 2 entry=.inl last ∧
 loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 3 entry=.inr (.ok last 0) ∧
 (∀ horizon,3≤horizon → loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) horizon entry=.inr (.ok last 0)) ∧
 run image AllocatorReturn.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F finalState SecondAllocatingEntry.addresses last ∧
 StructAllocatorRepr finalState.heap SecondAllocatingEntry.addresses 16 (⟨30,by decide⟩ : Fin W) last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 7,last.mem 8,last.mem 9,
 last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 14,last.mem 15,last.mem 17])=
 ([w[77]],[w[30],w[16],w[2],w[2],w[10],w[10],w[99],w[16],w[2],w[0],w[16],w[1],w[0],w[7]]) ∧
 loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 2 entry≠.inr (.ok last 0) := by
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
 obtain ⟨last,running,stopped,lastRepr,growth,stack,cursor,alias,exterior⟩ :=
   iter 2 0 SecondAllocatingEntry.child SecondAllocatingEntry.addresses entry repr (by decide) rfl
     8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) ((untouched 8 (by decide)).trans pointer) rfl history
 have allocation := growth (⟨30,by decide⟩ : Fin W) (by decide) owner (by decide)
 have resultRepr := lastRepr.core.vals (.here : Idx (Frame A) (.val .uint))
 change ReprV .uint (countValue 2 (by decide)) (last.mem 4) at resultRepr
 have resultWord : last.mem 4=w[2] := Restore.uint_unique resultRepr (ReprV.uint_of rfl)
 have counterRepr := lastRepr.core.vals (.there .here : Idx (Frame A) (.val .uint))
 change ReprV .uint (countValue 2 (by decide)) (last.mem 3) at counterRepr
 have counterWord : last.mem 3=w[2] := Restore.uint_unique counterRepr (ReprV.uint_of rfl)
 have preserved (x : Nat) (hp : x≠8) (hr : x≠2) (hc : x≠3) (hv : x≠4) (hb : x≠7) : last.mem x=down.mem x :=
   (exterior x hp hr hc hv).trans (untouched x hb)
 have refWord : last.mem 2=down.mem 2 := alias.trans (untouched 2 (by decide))
 have bottomWord : last.mem 7=w[10] := exterior 7 (by decide) (by decide) (by decide) (by decide)
 have oneRunning : ∃ mid,loopIterN (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) 1 entry=.inl mid := by
   cases firstTurn : loopTurn (run (condition 8 7)) (run (FullScalarUnwind.code (C:=P.C) 2 8 F)) entry with
   | inl mid => exact ⟨mid,by simp only [loopIterN,firstTurn]⟩
   | inr out =>
     simp only [loopIterN,firstTurn] at running
     cases running
 refine ⟨entry,last,rfl,oneRunning,running,stopped,?_,?_,lastRepr,allocation,?_,?_⟩
 · intro horizon enough
   exact loopIterN_done_le enough stopped
 · have loopRun : run (FullScalarLoop.code (C:=P.C) (R:=A) 2 8 7 F) entry=.ok last 0 :=
     run_of_stopped stopped
   exact (run_append_ok prefixRun).trans ((run_append_ok setup).trans loopRun)
 · rw [stack,preserved 0 (by decide) (by decide) (by decide) (by decide) (by decide),refWord,
     counterWord,resultWord,bottomWord,cursor,
     preserved 9 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 10 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 11 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 12 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 13 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 14 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 15 (by decide) (by decide) (by decide) (by decide) (by decide),
     preserved 17 (by decide) (by decide) (by decide) (by decide) (by decide)]
   exact congrArg (fun t : List Word × List Word =>
     (t.1,[t.2[0]!,t.2[1]!,w[2],w[2],w[10],w[10],t.2[6]!,t.2[7]!,t.2[8]!,t.2[9]!,t.2[10]!,t.2[11]!,t.2[12]!,t.2[13]!])) obs
 · rw [running]
   intro wrong
   cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.Controls.native_state' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.Controls.native_state

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.Controls.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.Controls.endpoint
