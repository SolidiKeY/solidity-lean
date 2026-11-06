import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarAllocatingDescent
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPairedTransport
import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeHeapProfile

/-! Actual native allocating-recursive output represented after actual target
parent returns. Complete heap identity, locals and all remaining State fields
are derived from execution; general recursive compiler selection and approved
provenance remain separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent TypedHeapExtensionality

theorem canonical_env_heq {C : Contract} {H H₁ H₂ : HTy} {R : RefTy}
 (typing : H₁=H₂) (ref : HRef H R) (first : H <+: H₁) (second : H <+: H₂) (value : PrimTy.uint.Denote) :
 HEq ((value,(value,(some (ref.wk first),()))) : TEnv C H₁ (Frame R))
     ((value,(value,(some (ref.wk second),()))) : TEnv C H₂ (Frame R)) := by
 cases typing
 rfl

theorem endpoint (depth n : Nat) {L frame : Nat} (σ : State C (Frame A))
 (fit : n<W) (ref : HRef σ.H A)
 (result : TEnv.get (.here : Idx (Frame A) (.val .uint)) σ.env=PrimTy.dflt .uint)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (n) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
 (cursor : Fin W) (owned : StructAllocatorRepr σ.heap base frame cursor before)
 (heapSpace : cursor.val+4*n<W) (lo pointer bottom start : Nat)
 (privateBelow : 5<lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (payloadAbove : lo≤start) (payloadBelow : start+3*n≤frame) (pointerBefore : pointer<start)
 (fits : start+3*n<W) (current : before.mem pointer=.val (wmod start))
 (bottomAbove : 6≤bottom) (bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer)
 (bottomValue : before.mem bottom=.val (wmod start))
 (enough : n<depth) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingScalarSource.body A (by rfl) depth).run σ=.ok out ∧
 run (ScalarPairedTransport.image guardCompiled pointer bottom) before=.ok last 0 ∧
 StateRepr L 2 frame F out.st addresses last ∧
 Heap.Keeps out.ext σ.heap out.st.heap ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator 2 frame (4*n) σ base before out.st addresses last ∧
 StructAllocatorRepr out.st.heap addresses frame (⟨cursor.val+4*n,heapSpace⟩ : Fin W) last ∧
 last.stack=before.stack ∧ last.mem pointer=.val (wmod start) ∧ last.mem 2=.val (base ref.id) ∧
 ScalarAllocationInventory.Holds σ.H.length n cursor.val out.st addresses ∧
 (∀ x,6≤x → x<frame → x≠pointer → (x<start ∨ start+3*n≤x) → last.mem x=before.mem x) := by
 obtain ⟨out,source,value,sourceSize,sourceKeeps,sourceDefaults,nativeContext⟩ :=
   NativeHeapProfile.success_with_context (by rfl) depth σ n fit ref counter alias enough
 obtain ⟨τ,e,down,addresses,running,downRepr,env,size,kept,downOwner,extended,descentGrowth,stack,position,history,words,inventory,targetContext⟩ :=
   running_with_context n 0 σ (by omega) ref result (by simpa only [Nat.zero_add] using counter) alias base before repr cursor owned heapSpace
     lo pointer start privateBelow pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits current
 have targetDefaults : Defaults σ.H.length τ.heap := of_inventory inventory size
 obtain ⟨typing,heap⟩ := profiles_heq σ.heap out.ext e out.st.heap τ.heap n sourceSize size sourceKeeps kept sourceDefaults targetDefaults
 obtain ⟨seen,seenRun,seenSize,seenEnv,seenKeeps⟩ := AllocatingScalarSource.success (by rfl) depth σ n fit ref counter alias enough
 have sameOut : seen=out := Except.ok.inj (seenRun.symm.trans source)
 subst seen
 have initialEnv : σ.env=(PrimTy.dflt .uint,(countValue n fit,(some ref,()))) :=
   Prod.ext result (Prod.ext counter (Prod.ext alias (by cases σ.env.2.2.2;rfl)))
 have nativeEnv : out.st.env=(countValue n fit,(countValue n fit,(some (ref.wk out.ext),()))) := by
   rw [seenEnv,initialEnv]
   rfl
 have zeroCounter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [env];rfl
 have zeroResult : TEnv.get (.here : Idx (Frame A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [env];rfl
 have stopped := GuardedPrefixes.finish_prefix _ _ n before down (.ok down 0) running
   (zero_turn τ zeroCounter addresses down downRepr pointer)
 have descend : run [.loop guardCompiled.code (AllocatingScalarTurn.code pointer)] before=.ok down 0 :=
   GuardedRecursion.successful_loop guardCompiled.code (AllocatingScalarTurn.code pointer) before down (n+1) stopped
 obtain ⟨reference,binding,referenceWord⟩ := downRepr.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
 have expected : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) τ.env=some (ref.wk e) := by rw [env];rfl
 have same : reference=ref.wk e := Option.some.inj (binding.symm.trans expected)
 subst reference
 change down.mem 2=.val (addresses ref.id) at referenceWord
 rw [extended ref] at referenceWord
 have saved : ∀ j,j<n → down.mem (start+3*j)=down.mem 2 ∧
     down.mem (start+3*j+1)=.val (wmod (0+n-j)) := by
   intro j small
   exact ⟨(history j small).1.trans referenceWord.symm,(history j small).2.1⟩
 have downBottom := (words bottom bottomAbove (by omega) bottomSeparate (.inl bottomBefore)).trans bottomValue
 obtain ⟨last,returns,done,lastRepr,growth,lastStack,lastPointer,lastRef,outside⟩ :=
   FullScalarLoop.iter n 0 τ addresses down downRepr (by omega) zeroResult lo pointer bottom start
     (by omega) pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore (by omega)
     bottomSeparate fits position downBottom saved
 have actual : run (ScalarPairedTransport.image guardCompiled pointer bottom) before=.ok last 0 :=
   (run_append_ok descend).trans (FullScalarLoop.run_of_stopped done)
 have total : GrowsAllocator 2 frame (4*n) σ base before
     (FullScalarLoop.returned τ 0 n (by omega)) addresses last := by
   simpa only [Nat.add_zero] using descentGrowth.comp growth
 have finalOwner := growth (⟨cursor.val+4*n,heapSpace⟩ : Fin W) (by omega) downOwner (by omega)
 have view : τ.H=(FullScalarLoop.returned τ 0 n (by omega)).H ∧
     HEq τ.heap (FullScalarLoop.returned τ 0 n (by omega)).heap ∧
     StateShell.Same τ (FullScalarLoop.returned τ 0 n (by omega)) := by
   cases n with
   | zero => exact ⟨rfl,HEq.rfl,StateShell.refl τ⟩
   | succ k => exact ⟨rfl,HEq.rfl,StateShell.refl τ⟩
 have targetEnv : HEq (FullScalarLoop.returned τ 0 n (by omega)).env
     ((countValue n fit,(countValue n fit,(some (ref.wk e),()))) : TEnv C τ.H (Frame A)) := by
   cases n with
   | zero =>
     change HEq τ.env _
     rw [env]
     rfl
   | succ k =>
     simp only [FullScalarLoop.returned]
     change HEq (countValue (0+(k+1)) _,(countValue (0+(k+1)) _,τ.env.2.2)) _
     rw [env]
     simp only [Nat.zero_add]
     rfl
 have locals : HEq out.st.env (FullScalarLoop.returned τ 0 n (by omega)).env := by
   rw [nativeEnv]
   exact (canonical_env_heq (C:=C) typing ref out.ext e (countValue n fit)).trans targetEnv.symm
 have context := StateShell.trans (StateShell.symm nativeContext) (StateShell.trans targetContext view.2.2)
 have stateEq := StateShell.state_eq out.st (FullScalarLoop.returned τ 0 n (by omega))
   (typing.trans view.1) (heap.trans view.2.1) locals context
 have finalInventory : ScalarAllocationInventory.Holds σ.H.length n cursor.val (FullScalarLoop.returned τ 0 n (by omega)) addresses := by
   cases n with
   | zero => exact inventory
   | succ k => exact inventory
 rw [←stateEq] at lastRepr total finalOwner finalInventory
 refine ⟨out,last,addresses,source,actual,lastRepr,sourceKeeps,extended,total,finalOwner,
   lastStack.trans stack,lastPointer,lastRef.trans referenceWord,finalInventory,?_⟩
 intro x lower upper different region
 exact (outside x different (by omega) (by omega) (by omega)).trans (words x lower upper different region)

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.endpoint

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.canonical_env_heq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.canonical_env_heq
