import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPrefixFacts

/-! All running/stopped horizons of one populated scalar-return loop. Complete
ordered observations are projected from the actual reached states, with no
re-executed desired endpoint or new recursion cutoff. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource RecursiveActivation CountdownWitness
open ScalarUnwind.Client
noncomputable def atHorizon (n : Nat) (within : n≤3) : Machine := (horizon n within).choose

theorem specification (n : Nat) (within : n≤3) :
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (ScalarUnwind.code (C:=P.C) 2 8 ScalarUnwind.Client.F)) n input=.inl (atHorizon n within) ∧
 StateRepr 1 2 16 ScalarUnwind.Client.F (state n (Nat.lt_of_le_of_lt within (by decide))) addresses (atHorizon n within) ∧
 (atHorizon n within).stack=input.stack ∧ (atHorizon n within).mem 8=.val (wmod (10+2*(3-n))) ∧
 (atHorizon n within).mem 2=input.mem 2 ∧
 GrowsAllocator 2 16 0 (state 0 W_pos) addresses input
   (state n (Nat.lt_of_le_of_lt within (by decide))) addresses (atHorizon n within) ∧
 (∀ x,x≠8 → x≠2 → x≠3 → x≠4 → (atHorizon n within).mem x=input.mem x) :=
 (horizon n within).choose_spec

theorem scalar_words (n : Nat) (within : n≤3) :
 (atHorizon n within).mem 3=.val (wmod n) ∧ (atHorizon n within).mem 4=.val (wmod n) := by
 have represented := (specification n within).2.1
 have count := represented.core.vals (.there .here : Idx (Frame CountdownWitness.A) (.val .uint))
 have result := represented.core.vals (.here : Idx (Frame CountdownWitness.A) (.val .uint))
 have encoded : ReprV .uint (countValue n (Nat.lt_of_le_of_lt within (by decide))) (.val (wmod n)) := by
   have word : wmod n=(⟨n,Nat.lt_of_le_of_lt within (by decide)⟩ : Fin W) :=
     Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt within (by decide)))
   rw [word]
   exact ReprV.uint_of rfl
 exact ⟨Restored.value_unique count encoded,Restored.value_unique result encoded⟩

theorem snapshot (n : Nat) (within : n≤3) :
 ((atHorizon n within).stack,
 [(atHorizon n within).mem 0,(atHorizon n within).mem 1,(atHorizon n within).mem 2,
 (atHorizon n within).mem 3,(atHorizon n within).mem 4,(atHorizon n within).mem 6,
 (atHorizon n within).mem 7,(atHorizon n within).mem 8,(atHorizon n within).mem 9,
 (atHorizon n within).mem 10,(atHorizon n within).mem 11,(atHorizon n within).mem 12,
 (atHorizon n within).mem 13,(atHorizon n within).mem 14,(atHorizon n within).mem 15,
 (atHorizon n within).mem 16,(atHorizon n within).mem 17,(atHorizon n within).mem 18,
 (atHorizon n within).mem 20,(atHorizon n within).mem 21])=
 ([w[77]],[w[22],w[16],w[16],.val (wmod n),.val (wmod n),w[2],w[10],
 .val (wmod (10+2*(3-n))),w[99],w[16],w[3],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rcases specification n within with ⟨running,repr,stack,cursor,alias,growth,outside⟩
 rcases preparation with ⟨descent,baseCase,zeroRepr,zeroStack,zeroCursor,zeroRef,payload,zeroOutside,extended,zeroOwner⟩
 have values := scalar_words n within
 have inputWord (x : Nat) (hp : x≠8) (hc : x≠3) (hv : x≠4) (hb : x≠7)
     (region : x<10 ∨ 16≤x) : input.mem x=ScalarUnwind.Client.before.mem x :=
   (upd_other zero.mem w[10] hb).trans (zeroOutside x hp hc hv region)
 have stackInput : input.stack=[w[77]] := zeroStack
 have samePayload (j : Nat) (small : j<3) :
     input.mem (10+2*j)=w[16] ∧ input.mem (10+2*j+1)=.val (wmod (3-j)) :=
   ⟨(saved j small).1.trans reference,(saved j small).2⟩
 rw [stack,stackInput,values.1,values.2,cursor,alias,reference,
   outside 0 (by decide) (by decide) (by decide) (by decide),
   outside 1 (by decide) (by decide) (by decide) (by decide),
   outside 6 (by decide) (by decide) (by decide) (by decide),
   outside 7 (by decide) (by decide) (by decide) (by decide),
   outside 9 (by decide) (by decide) (by decide) (by decide),
   outside 10 (by decide) (by decide) (by decide) (by decide),
   outside 11 (by decide) (by decide) (by decide) (by decide),
   outside 12 (by decide) (by decide) (by decide) (by decide),
   outside 13 (by decide) (by decide) (by decide) (by decide),
   outside 14 (by decide) (by decide) (by decide) (by decide),
   outside 15 (by decide) (by decide) (by decide) (by decide),
   outside 16 (by decide) (by decide) (by decide) (by decide),
   outside 17 (by decide) (by decide) (by decide) (by decide),
   outside 18 (by decide) (by decide) (by decide) (by decide),
   outside 20 (by decide) (by decide) (by decide) (by decide),
   outside 21 (by decide) (by decide) (by decide) (by decide),
   (samePayload 0 (by decide)).1,(samePayload 0 (by decide)).2,
   (samePayload 1 (by decide)).1,(samePayload 1 (by decide)).2,
   (samePayload 2 (by decide)).1,(samePayload 2 (by decide)).2]
 rw [inputWord 0 (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   inputWord 1 (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   inputWord 6 (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   inputWord 9 (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   inputWord 16 (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   inputWord 17 (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   inputWord 18 (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   inputWord 20 (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   inputWord 21 (by decide) (by decide) (by decide) (by decide) (.inr (by decide))]
 rfl

theorem completed : ∃ last,
 run (image (C:=P.C) 2 8 7 ScalarUnwind.Client.F) input=.ok last 0 ∧
 (∀ n,4≤n → loopIterN (run (PairedUnwind.condition 8 7))
   (run (ScalarUnwind.code (C:=P.C) 2 8 ScalarUnwind.Client.F)) n input=.inr (.ok last 0)) ∧
 StateRepr 1 2 16 ScalarUnwind.Client.F (state 3 (by decide)) addresses last ∧
 last.stack=input.stack ∧ last.mem 8=w[10] ∧ last.mem 2=input.mem 2 ∧
 GrowsAllocator 2 16 0 (state 0 W_pos) addresses input (state 3 (by decide)) addresses last ∧
 (∀ x,x≠8 → x≠2 → x≠3 → x≠4 → last.mem x=input.mem x) := by
 have result := complete (state 0 W_pos) addresses 3 3 (Nat.le_refl _) (by decide) input initial
   8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) current rfl saved
 simpa only [Nat.sub_self,Nat.zero_add] using result

noncomputable def returned : Machine := completed.choose

theorem completion :
 run (image (C:=P.C) 2 8 7 ScalarUnwind.Client.F) input=.ok returned 0 ∧
 (∀ n,4≤n → loopIterN (run (PairedUnwind.condition 8 7))
   (run (ScalarUnwind.code (C:=P.C) 2 8 ScalarUnwind.Client.F)) n input=.inr (.ok returned 0)) ∧
 StateRepr 1 2 16 ScalarUnwind.Client.F (state 3 (by decide)) addresses returned ∧
 returned.stack=input.stack ∧ returned.mem 8=w[10] ∧ returned.mem 2=input.mem 2 ∧
 GrowsAllocator 2 16 0 (state 0 W_pos) addresses input (state 3 (by decide)) addresses returned ∧
 (∀ x,x≠8 → x≠2 → x≠3 → x≠4 → returned.mem x=input.mem x) := completed.choose_spec

def wholeImage : List Instr := [.push w[0],.mstore 4] ++
 (descentCode (C:=P.C) 2 CountdownWitness.F 8 ++
 ([.push w[0],.mstore 4] ++ ([.push w[10],.mstore 7] ++ image (C:=P.C) 2 8 7 ScalarUnwind.Client.F)))

theorem whole_target : run wholeImage ScalarUnwind.Client.before=.ok returned 0 := by
 unfold wholeImage
 rw [run_append_ok ScalarUnwind.Client.entry_run,run_append_ok preparation.1,
   run_append_ok preparation.2.1,run_append_ok initialization]
 exact completion.1

theorem native_and_target (depth : Nat) (enough : 3<depth) :
 (ScalarRecursiveSource.body CountdownWitness.A rfl depth).run ScalarRecursiveSource.Controls.entry.st=
   .ok ⟨state 3 (by decide),List.prefix_refl _⟩ ∧
 run wholeImage ScalarUnwind.Client.before=.ok returned 0 ∧
 StateRepr 1 2 16 ScalarUnwind.Client.F (state 3 (by decide)) addresses returned := by
 have native := all_horizons rfl depth ScalarRecursiveSource.Controls.entry.st 3 (by decide) P.r0 rfl rfl
 exact ⟨by simpa only [if_pos enough] using native,whole_target,completion.2.2.1⟩

theorem wrong_stopped (n : Nat) (within : n≤3) (result : Evm.Out) :
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (ScalarUnwind.code (C:=P.C) 2 8 ScalarUnwind.Client.F)) n input≠.inr result := by
 rw [(specification n within).1]
 intro wrong
 cases wrong

theorem wrong_horizon : (atHorizon 0 (by decide)).mem 4≠(atHorizon 1 (by decide)).mem 4 := by
 rw [(scalar_words 0 (by decide)).2,(scalar_words 1 (by decide)).2]
 decide

theorem wrong_alias (n : Nat) (within : n≤3) : (atHorizon n within).mem 2≠w[20] := by
 rw [(specification n within).2.2.2.2.1,reference]
 decide

theorem wrong_scalar (n : Nat) (within : n≤3) : (atHorizon n within).mem 4≠.val (wmod (n+1)) := by
 rw [(scalar_words n within).2]
 intro wrong
 have same := congrArg Fin.val (Word.val.inj wrong)
 change n%W=(n+1)%W at same
 have space : (4:Nat)<W := by decide
 rw [Nat.mod_eq_of_lt (show n<W from by omega),Nat.mod_eq_of_lt (show n+1<W from by omega)] at same
 omega

theorem wrong_cursor : returned.mem 8≠w[16] := by
 rw [completion.2.2.2.2.1]
 decide

theorem not_revert : run wholeImage ScalarUnwind.Client.before≠.revert := by
 rw [whole_target]
 intro wrong
 cases wrong

/-- The final running parent and every completed observation name the SAME
machine; the snapshot is not obtained from a separate chosen execution. -/
theorem returned_is_last : returned=atHorizon 3 (by decide) := by
 rcases specification 3 (by decide) with ⟨running,represented,stack,cursor,alias,growth,outside⟩
 have position : (atHorizon 3 (by decide)).mem 8=w[10] := cursor
 have bottom : (atHorizon 3 (by decide)).mem 7=w[10] := outside 7 (by decide) (by decide) (by decide) (by decide)
 have stopped := stop_after_running (start:=10) running position bottom
 have same := Sum.inr.inj ((completion.2.1 4 (by decide)).symm.trans stopped)
 exact (Evm.Out.ok.inj same).1

theorem completed_snapshot :
 (returned.stack,[returned.mem 0,returned.mem 1,returned.mem 2,returned.mem 3,returned.mem 4,
 returned.mem 6,returned.mem 7,returned.mem 8,returned.mem 9,returned.mem 10,returned.mem 11,
 returned.mem 12,returned.mem 13,returned.mem 14,returned.mem 15,returned.mem 16,returned.mem 17,
 returned.mem 18,returned.mem 20,returned.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[3],w[3],w[2],w[10],w[10],w[99],w[16],w[3],w[16],w[2],
 w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rw [returned_is_last]
 exact snapshot 3 (by decide)

theorem ownership_at (n : Nat) (within : n≤3) :
 StructAllocatorRepr (state n (Nat.lt_of_le_of_lt within (by decide))).heap addresses 16
   ⟨22,by decide⟩ (atHorizon n within) := by
 rcases specification n within with ⟨_,_,_,_,_,growth,_⟩
 exact growth ⟨22,by decide⟩ (by decide) owner (by decide)

theorem not_fault : run wholeImage ScalarUnwind.Client.before≠.fault := by
 rw [whole_target]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes.Client
