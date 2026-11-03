import Solidity.Backend.InternalFlow.RuntimeFrameV3GuardedCaller

/-! Exact saved history and protected caller tails at running guarded countdown
prefixes. A horizon is an observation index, not recursive compiler admission. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CallerPrefixes
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

theorem source_tail {C : Contract} {tail : Ctx} (σ : State C (.val .uint :: tail))
 (v : PrimTy.uint.Denote) : (σ.setLocal .here v).env.2=σ.env.2 := by rfl

/-- Strict-prefix generalization of the existing completed descent history.
The actual unprobed prefix is supplied by the checked guarded-prefix bridge. -/
theorem history {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (steps count : Nat) (small : steps≤count) (bound : count<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before after : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start))
 (actual : loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (activationCode (C:=C) b F pointer)) steps before=.inl after) :
 (∀ j, j<steps → after.mem (start+2*j)=before.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 (∀ x, x≠pointer → x≠b+1 → (x<start ∨ start+2*steps≤x) → after.mem x=before.mem x) := by
 induction steps generalizing count σ base before start with
 | zero =>
   have same : before=after := Sum.inl.inj actual
   subst after
   exact ⟨by intro j small;omega,by intro x hp hc ho;rfl⟩
 | succ steps ih =>
   cases count with
   | zero => omega
   | succ count =>
     let child : State C (Parameters R) := σ.withEnv (countValue count (by omega),(some ref,()))
     obtain ⟨saved,next,addresses,args,entry,captured,updated,executed,represented,stack,extended,growth,cursor,payload⟩ :=
       activation hm σ count bound ref counter alias base before repr lo pointer start localBound
         pointerAbove pointerBelow payloadAbove (by omega) (.inl pointerBefore) (by omega) current
     have first := RecursiveHistory.activation_exterior hm σ count bound ref counter alias base before next repr
       lo pointer start localBound pointerAbove pointerBelow payloadAbove (by omega) pointerBefore (by omega) current executed
     have turn := positive_turn σ count bound counter base before next repr pointer executed
     have rest : loopIterN (run (guardCompiled (C:=C) b F).code)
         (run (activationCode (C:=C) b F pointer)) steps next=.inl after := by
       simpa only [loopIterN,turn] using actual
     obtain ⟨savedTail,exterior⟩ := ih count (by omega) (by omega) child ref rfl rfl addresses next represented
       (start+2) (by omega) (by omega) (by omega) (by omega) cursor rest
     constructor
     · intro j less
       cases j with
       | zero =>
         have savedRef := payload 0 (by decide)
         have savedCounter := payload 1 (by decide)
         have refAfter := exterior start (by omega) (by omega) (.inl (by omega))
         have counterAfter := exterior (start+1) (by omega) (by omega) (.inl (by omega))
         have word := RecursiveHistory.counter_word σ (count+1) bound counter base before repr
         exact ⟨by simpa only [Nat.mul_zero,Nat.add_zero] using refAfter.trans savedRef,
           by simpa only [Nat.mul_zero,Nat.add_zero,Nat.sub_zero] using counterAfter.trans (savedCounter.trans word)⟩
       | succ j =>
         have words := savedTail j (by omega)
         have offset : start+2*(j+1)=start+2+2*j := by omega
         constructor
         · rw [offset]
           exact words.1.trans (first b (by omega) (by omega) (.inl (by omega)))
         · rw [offset]
           simpa only [Nat.add_sub_add_right] using words.2
     · intro x hp hc outside
       exact (exterior x hp hc (by omega)).trans (first x hp hc (by omega))

/-- Lower caller bindings lie strictly below the active counter cell. -/
theorem lower_address {tail : Ctx} (b : Nat) {t : LTy} (index : Idx (.mem A :: tail) t) :
 cellOf b (.there index : Idx (Parameters A ++ tail) t)<b+tail.length+1 := by
 have small := lvl_lt b index
 simpa only [cellOf,cell,lvl_there,List.length_cons,Nat.add_assoc] using small

/-- Running-frame view: active native parameters plus the suspended caller's
protected tail. This does NOT say the suspended source caller's counter changes.
Both represented prefixes and their exterior history are derived from execution. -/
theorem endpoint {C : Contract} {tail : Ctx} {L b frame : Nat}
 {F : Frag (Parameters A ++ tail)} (steps count : Nat) (small : steps≤count)
 (caller : State C (Parameters A ++ tail)) (bound : count<W) (ref : HRef caller.H A)
 (counter : TEnv.get (.here : Idx (Parameters A ++ tail) (.val .uint)) caller.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A ++ tail) (.mem A)) caller.env=some ref)
 (reads : ReadDomain (caller.withEnv (Δ:=Parameters A) (countValue count bound,(some ref,()))) ref count)
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F caller base before)
 (lo pointer start : Nat) (localBound : b+tail.length+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 let view := caller.setLocal .here (countValue (count-steps) (by omega))
 ∃ after,
 loopIterN (run (guardCompiled (C:=C) (b+tail.length) (Frag.init (Parameters A))).code)
   (run (turnCode (C:=C) (b+tail.length) (Frag.init (Parameters A)) pointer)) steps before=.inl after ∧
 StateRepr L b frame F view base after ∧ after.stack=before.stack ∧ view.env.2=caller.env.2 ∧
 after.mem (b+tail.length+1)=.val (wmod (count-steps)) ∧
 after.mem pointer=.val (wmod (start+2*steps)) ∧
 (∀ {t : LTy} (index : Idx (.mem A :: tail) t),
   after.mem (cellOf b (.there index : Idx (Parameters A ++ tail) t))=before.mem (cellOf b (Idx.there (u:=.val .uint) index))) ∧
 (∀ j, j<steps → after.mem (start+2*j)=before.mem (b+tail.length) ∧
   after.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 (∀ x, x≠pointer → x≠b+tail.length+1 → (x<start ∨ start+2*steps≤x) → after.mem x=before.mem x) := by
 let child : State C (Parameters A) := caller.withEnv (countValue count bound,(some ref,()))
 have parameters : TEnv.take (Parameters A) caller.env=(countValue count bound,(some ref,())) :=
   Prod.ext counter (Prod.ext alias rfl)
 have projected := parameter_projection (tail:=tail) initial
 rw [parameters] at projected
 obtain ⟨after,addresses,running,oldRunning,represented,stack,extended,growth,cursor⟩ :=
   GuardedPrefixes.reached_prefix steps count small bound child ref rfl rfl reads base before projected
     lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
 obtain ⟨saved,exterior⟩ := history rfl steps count small bound child ref rfl rfl base before after projected
   lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current oldRunning
 have activeCounter := RecursiveHistory.counter_word _ (count-steps) (by omega) rfl addresses after represented
 have destination : cellOf b (.here : Idx (Parameters A ++ tail) (.val .uint))=b+tail.length+1 := by
   change b+((tail.length+1+1)-1)=b+tail.length+1
   omega
 have remainingFit : count-steps<W := by omega
 let word : Word := .val ⟨count-steps,remainingFit⟩
 have wordEq : (.val (wmod (count-steps)) : Word)=word := by
   congr 1
   exact Fin.ext (Nat.mod_eq_of_lt remainingFit)
 let template := writeMachine before (cellOf b (.here : Idx (Parameters A ++ tail) (.val .uint))) word
 have templateRepr : StateRepr L b frame F (caller.setLocal .here (countValue (count-steps) remainingFit)) base template :=
   initial.setVal .here (countValue (count-steps) remainingFit) word (ReprV.uint_of rfl)
 have lower : ∀ {t : LTy} (index : Idx (.mem A :: tail) t),
     after.mem (cellOf b (.there index : Idx (Parameters A ++ tail) t))=before.mem (cellOf b (Idx.there (u:=.val .uint) index)) := by
   intro t index
   have less := lower_address (tail:=tail) b index
   exact exterior _ (by omega) (by omega) (.inl (by omega))
 have localWords : ∀ {t : LTy} (index : Idx (Parameters A ++ tail) t),
     after.mem (cellOf b index)=template.mem (cellOf b index) := by
   intro t index
   cases index with
   | here =>
     simp only [template,writeMachine,upd,if_true,destination]
     exact activeCounter.trans wordEq
   | there index =>
     have less := lower_address (tail:=tail) b index
     simpa only [template,writeMachine,destination,upd,if_neg (show cellOf b (Idx.there (u:=.val .uint) index)≠b+tail.length+1 from by omega)] using lower index
 have high : ∀ x, frame≤x → after.mem x=template.mem x := by
   intro x above
   have preserved := exterior x (by omega) (by omega) (.inr (by omega))
   simpa only [template,writeMachine,destination,upd,if_neg (show x≠b+tail.length+1 from by omega)] using preserved
 have transported := Restored.memory_transport templateRepr after.mem (fun index observed => localWords index) high
 have viewRepr : StateRepr L b frame F (caller.setLocal .here (countValue (count-steps) remainingFit)) base after :=
   ⟨⟨represented.core.store,transported.core.vals,transported.core.aliases,
     represented.core.net,represented.core.netSelf,initial.core.bound,transported.core.fragile,
     represented.core.env,represented.core.funds,represented.core.oracle⟩,
     ⟨fun r => ⟨(transported.heap.arrays r).space,(transported.heap.arrays r).length,(transported.heap.arrays r).elements⟩,
       transported.heap.above,transported.heap.separated⟩,
     transported.pointers,transported.locals,
     ⟨fun r => ⟨(transported.structs.objects r).space,(transported.structs.objects r).fields⟩,
       transported.structs.above,transported.structs.separated⟩,
     transported.separated,RefFieldsRepr.mem_eq transported.refs rfl⟩
 exact ⟨after,running,viewRepr,stack,source_tail caller _,activeCounter,cursor,lower,saved,exterior⟩

namespace Checks
open CountdownWitness
abbrev input := GuardedCaller.Checks.input

/-- Chosen only from the checked existential endpoint on the real populated
header-prefix input, not from an assumed running execution. -/
noncomputable def atPrefix (steps : Nat) (small : steps≤2) : Machine :=
 (endpoint (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) steps 2 small caller (by decide) P.r0 rfl rfl
   GuardedPrefixes.Checks.read_domain P.base input GuardedCaller.Checks.input_repr 8 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).choose

theorem specification (steps : Nat) (small : steps≤2) :
 let view := caller.setLocal .here (countValue (2-steps) (Nat.lt_of_le_of_lt (Nat.sub_le 2 steps) (by decide : 2<W)))
 loopIterN (run (guardCompiled (C:=P.C) 2 CountdownWitness.F).code)
   (run (turnCode (C:=P.C) 2 CountdownWitness.F 8)) steps input=.inl (atPrefix steps small) ∧
 StateRepr 1 0 16 (Frag.init P.Γ) view P.base (atPrefix steps small) ∧
 (atPrefix steps small).stack=input.stack ∧ view.env.2=caller.env.2 ∧
 (atPrefix steps small).mem 3=.val (wmod (2-steps)) ∧
 (atPrefix steps small).mem 8=.val (wmod (10+2*steps)) ∧
 (∀ {t : LTy} (index : Idx (.mem CountdownWitness.A :: [.mem CountdownWitness.A,.mem CountdownWitness.A]) t),
   (atPrefix steps small).mem (cellOf 0 (Idx.there (u:=.val .uint) index))=input.mem (cellOf 0 (Idx.there (u:=.val .uint) index))) ∧
 (∀ j, j<steps → (atPrefix steps small).mem (10+2*j)=input.mem 2 ∧
   (atPrefix steps small).mem (10+2*j+1)=.val (wmod (2-j))) ∧
 (∀ x, x≠8 → x≠3 → (x<10 ∨ 10+2*steps≤x) → (atPrefix steps small).mem x=input.mem x) :=
 (endpoint (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) steps 2 small caller (by decide) P.r0 rfl rfl
   GuardedPrefixes.Checks.read_domain P.base input GuardedCaller.Checks.input_repr 8 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).choose_spec

/-- The common ordered observation leaves only newly written parent cells
symbolic. It is a consequence of the SAME actual prefix, not a replay. -/
theorem base_observation (steps : Nat) (small : steps≤2) :
 (CountdownWitness.observed (atPrefix steps small),(atPrefix steps small).mem 7)=
 (([w[77]],[w[20],w[16],w[16],.val (wmod (2-steps)),.val (wmod (10+2*steps)),w[99],
   (atPrefix steps small).mem 10,(atPrefix steps small).mem 11,(atPrefix steps small).mem 12,(atPrefix steps small).mem 13,
   w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rcases specification steps small with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 change (((atPrefix steps small).stack,[(atPrefix steps small).mem 0,(atPrefix steps small).mem 1,(atPrefix steps small).mem 2,
   (atPrefix steps small).mem 3,(atPrefix steps small).mem 8,(atPrefix steps small).mem 9,
   (atPrefix steps small).mem 10,(atPrefix steps small).mem 11,(atPrefix steps small).mem 12,(atPrefix steps small).mem 13,
   (atPrefix steps small).mem 16,(atPrefix steps small).mem 17,(atPrefix steps small).mem 18,
   (atPrefix steps small).mem 20,(atPrefix steps small).mem 21]),(atPrefix steps small).mem 7)=_
 rw [stack,counter,cursor,exterior 0 (by decide) (by decide) (.inl (by decide)),
   exterior 1 (by decide) (by decide) (.inl (by decide)),exterior 2 (by decide) (by decide) (.inl (by decide)),
   exterior 7 (by decide) (by decide) (.inl (by decide)),exterior 9 (by decide) (by decide) (.inl (by decide)),
   exterior 16 (by decide) (by decide) (.inr (by omega)),exterior 17 (by decide) (by decide) (.inr (by omega)),
   exterior 18 (by decide) (by decide) (.inr (by omega)),exterior 20 (by decide) (by decide) (.inr (by omega)),
   exterior 21 (by decide) (by decide) (.inr (by omega))]
 rfl

theorem zero_observation : (CountdownWitness.observed (atPrefix 0 (by decide)),(atPrefix 0 (by decide)).mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[2],w[10],w[99],w[0],w[0],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rcases specification 0 (by decide) with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 rw [base_observation,exterior 10 (by decide) (by decide) (.inr (by decide)),
   exterior 11 (by decide) (by decide) (.inr (by decide)),exterior 12 (by decide) (by decide) (.inr (by decide)),
   exterior 13 (by decide) (by decide) (.inr (by decide))]
 rfl

theorem one_observation : (CountdownWitness.observed (atPrefix 1 (by decide)),(atPrefix 1 (by decide)).mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[1],w[12],w[99],w[16],w[2],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rcases specification 1 (by decide) with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 have parent := saved 0 (by decide)
 change (atPrefix 1 (by decide)).mem 10=input.mem 2 ∧ (atPrefix 1 (by decide)).mem 11=w[2] at parent
 rw [base_observation,parent.1,parent.2,exterior 12 (by decide) (by decide) (.inr (by decide)),
   exterior 13 (by decide) (by decide) (.inr (by decide))]
 rfl

theorem two_observation : (CountdownWitness.observed (atPrefix 2 (by decide)),(atPrefix 2 (by decide)).mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[0],w[14],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rcases specification 2 (by decide) with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 have first := saved 0 (by decide)
 have second := saved 1 (by decide)
 change (atPrefix 2 (by decide)).mem 10=input.mem 2 ∧ (atPrefix 2 (by decide)).mem 11=w[2] at first
 change (atPrefix 2 (by decide)).mem 12=input.mem 2 ∧ (atPrefix 2 (by decide)).mem 13=w[1] at second
 rw [base_observation,first.1,first.2,second.1,second.2]
 rfl

/-- The suspended native caller is still count two, but its physical active
parameter cell is now count one. Conflating those represented states is false. -/
theorem wrong_original_repr : ¬StateRepr 1 0 16 (Frag.init P.Γ) caller P.base (atPrefix 1 (by decide)) := by
 intro original
 rcases specification 1 (by decide) with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 have value := original.core.vals (.here : Idx P.Γ (.val .uint))
 change ReprV .uint (P.uint 2 (by decide)) ((atPrefix 1 (by decide)).mem 3) at value
 have word := Restore.uint_unique value (ReprV.uint_of rfl : ReprV .uint (P.uint 2 (by decide)) w[2])
 change (atPrefix 1 (by decide)).mem 3=w[1] at counter
 rw [counter] at word
 have different : w[1]≠w[2] := by decide
 exact different word

theorem wrong_cursor : (atPrefix 1 (by decide)).mem 8≠w[14] := by
 rcases specification 1 (by decide) with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 change (atPrefix 1 (by decide)).mem 8=w[12] at cursor
 rw [cursor]
 decide

theorem wrong_alias : (atPrefix 1 (by decide)).mem 1≠w[20] := by
 rcases specification 1 (by decide) with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 have value := exterior 1 (by decide) (by decide) (.inl (by decide))
 change (atPrefix 1 (by decide)).mem 1=w[16] at value
 rw [value]
 decide

/-- The next actual false guard stops at the SAME zero-counter prefix. -/
theorem stopped : loopIterN (run (guardCompiled (C:=P.C) 2 CountdownWitness.F).code)
 (run (turnCode (C:=P.C) 2 CountdownWitness.F 8)) 3 input=.inr (.ok (atPrefix 2 (by decide)) 0) := by
 rcases specification 2 (by decide) with ⟨executed,repr,stack,tail,counter,cursor,locals,saved,exterior⟩
 have projected := parameter_projection (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) repr
 have guard := guard_run _ 0 W_pos rfl P.base (atPrefix 2 (by decide)) projected
 have done := empty_turn (run (guardCompiled (C:=P.C) 2 CountdownWitness.F).code)
   (run (turnCode (C:=P.C) 2 CountdownWitness.F 8)) (atPrefix 2 (by decide)) guard
 exact finish_prefix _ _ 2 input _ _ executed done

theorem stopped_stable (horizon : Nat) (enough : 3≤horizon) :
 loopIterN (run (guardCompiled (C:=P.C) 2 CountdownWitness.F).code)
 (run (turnCode (C:=P.C) 2 CountdownWitness.F 8)) horizon input=.inr (.ok (atPrefix 2 (by decide)) 0) :=
 loopIterN_done_le enough stopped

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.CallerPrefixes

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerPrefixes.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerPrefixes.endpoint
