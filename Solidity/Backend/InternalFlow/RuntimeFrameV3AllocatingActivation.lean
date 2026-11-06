import Solidity.Backend.InternalFlow.RuntimeFrameV3DomainTransport

/-! An allocating intrinsic recursive family and actual allocation/probe/capture
entry. Generic activation and a witnessed return are proved; no general
recursive compiler or producer is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

def size : Fin W := ⟨3,by decide⟩
def lengthExpr {C : Contract} : Simple C (Parameters A) .uint := .lit 3 (by decide)
def object {C : Contract} (σ : State C (Parameters A)) : MObj σ.H (.array (.prim .bool)) := defaultArray .bool size
def allocated {C : Contract} (σ : State C (Parameters A)) := (σ.alloc (object σ)).1
def extension {C : Contract} (σ : State C (Parameters A)) : σ.H <+: (allocated σ).H := List.prefix_append _ _

def step {C : Contract} (depth : Nat) (back : Unit → Prog C (Parameters A) (Parameters A)) :
 Prog C (Parameters A) (Parameters A) :=
 .cons (.ite nonzero
   (.cons (DomainTransport.scopedNew .bool lengthExpr)
     (.cons GuardedRecursion.probe (.cons (.callRec "allocatingCountdown" depth (nextArgs A rfl) .none back) .nil))) .nil) .nil

def body {C : Contract} (depth : Nat) : Prog C (Parameters A) (Parameters A) := recUnroll Prog.recBase step depth

theorem allocated_parameters {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref) :
 TEnv.get (.here : Idx (Parameters A) (.val .uint)) (allocated σ).env=countValue (n+1) fit ∧
 TEnv.get (.there .here : Idx (Parameters A) (.mem A)) (allocated σ).env=some (ref.wk (extension σ)) := by
 constructor
 · exact counter
 · change (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env).map (HRef.wk (extension σ))=_
   rw [alias]
   rfl

theorem allocated_read {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn) : ∃ v, ArrayProbe.value.evalT (allocated σ)=.ok v := by
 obtain ⟨v,read⟩ := (HeapDomain.success_iff σ n fit ref counter alias).2 within
 have parameters := allocated_parameters σ n fit ref counter alias
 have same := DomainTransport.probe_keeps σ (allocated σ) (extension σ) (Heap.keeps_alloc σ.heap (object σ))
   n fit ref counter alias parameters.1 parameters.2
 exact ⟨v,same.trans read⟩

/-- Positive source branch exposes the ACTUAL native child call, with the
allocation extension composed into its output, at every quotation depth. -/
theorem source_positive {C : Contract} (σ : State C (Parameters A)) (depth n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn) :
 (body (depth+1)).run σ=
 ((.call "allocatingCountdown" (nextArgs A rfl) .none (body depth) : Stmt C (Parameters A) (Parameters A)).run (allocated σ)).map
   (fun out => (⟨out.st,(extension σ).trans out.ext⟩ : Solidity.Out C σ.H (Parameters A))) := by
 have guard := guard_eval σ (n+1) (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have source := DomainTransport.scoped_source σ .bool lengthExpr size rfl
 obtain ⟨v,read⟩ := allocated_read σ n fit ref counter alias within
 have probed := probe_success (allocated σ) v read
 let call : TStep C (Parameters A) (Parameters A) := TRun.call (nextArgs A rfl) .none .refl (body depth).runR
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq (DomainTransport.scopedNew .bool lengthExpr).runR
     (TRun.seq GuardedRecursion.probe.runR (TRun.seq call TRun.nil))) .refl TRun.nil) TRun.nil σ=_
 change (DomainTransport.scopedNew .bool lengthExpr).runR σ=.ok ⟨allocated σ,extension σ⟩ at source
 change GuardedRecursion.probe.runR (allocated σ)=.ok ⟨allocated σ,List.prefix_refl _⟩ at probed
 change _=(call (allocated σ)).map _
 simp only [TRun.seq,TRun.ite,guard,positive,boolT,source,probed,Except.map,ok_bind,if_true]
 cases actual : call (allocated σ) with
 | error halt => rfl
 | ok out => simp only [TRun.nil];cases out;rfl

theorem source_zero {C : Contract} (σ : State C (Parameters A)) (depth : Nat)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue 0 W_pos) :
 (body (depth+1)).run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
 have guard := guard_eval σ 0 (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq (DomainTransport.scopedNew .bool lengthExpr).runR
     (TRun.seq GuardedRecursion.probe.runR (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (body depth).runR) TRun.nil)))
     .refl TRun.nil) TRun.nil σ=_
 simp only [TRun.seq,TRun.ite,guard,boolT,TRun.nil,Except.map]
 rfl

theorem base_exhausts {C : Contract} (σ : State C (Parameters A)) : (body 0).run σ=.error .exhausted := by rfl

def code {C : Contract} (b : Nat) (F : Frag (Parameters A)) (pointer : Nat) : List Instr :=
 declareNewCode b (lengthExpr (C:=C)) ++ ArrayProbe.code (C:=C) b F ++ activationCode (C:=C) b F pointer

/-- Capture and entered-child representation follow actual allocating body
execution. No source child run, target outcome, midpoint or frame oracle is supplied. -/
theorem activation {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (payloadBelow : start+2≤frame)
 (pointerBefore : pointer<start) (fits : start+2<W)
 (current : before.mem pointer=.val (wmod start)) :
 let parent := allocated σ
 let child := parent.withEnv (Δ:=Parameters A) (countValue n (by omega),(some (ref.wk (extension σ)),()))
 let allocationMachine := writeMachine (allocateMachine before cursor size) (cell (b+2)) (.val cursor)
 ∃ next addresses,
 (nextArgs A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters A) [] (Parameters A)).enterT (parent.withEnv child.env)).st=child ∧
 run (code (C:=C) b F pointer) before=.ok next 0 ∧
 StateRepr L b frame F child addresses next ∧ next.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame 4 σ base before child addresses next ∧
 next.mem pointer=.val (wmod (start+2)) ∧
 (∀ i, i<2 → next.mem (start+i)=allocationMachine.mem (b+i)) ∧
 (∀ x, x≠pointer → x≠b+1 → (x<start ∨ start+2≤x) → next.mem x=allocationMachine.mem x) := by
 obtain ⟨source,declRun,declRepr,declOwner,declStack,words⟩ :=
   Footprint.declare repr owner positive .bool lengthExpr rfl size rfl heapSpace (lo:=lo) localBound (by change b+(2+1)≤frame;omega)
 let allocationBase := upd base σ.H.length cursor
 let allocationMachine := writeMachine (allocateMachine before cursor size) (cell (b+2)) (.val cursor)
 have parentRepr : StateRepr L b frame F (allocated σ) allocationBase allocationMachine := declRepr.drop (.push .refl)
 have parameters := allocated_parameters σ n fit ref counter alias
 obtain ⟨v,read⟩ := allocated_read σ n fit ref counter alias within
 have checkedProbe := ArrayProbe.success parentRepr v read
 have parentCurrent : allocationMachine.mem pointer=.val (wmod start) := (words pointer pointerAbove pointerBelow).trans current
 obtain ⟨saved,next,addresses,args,entered,captureRun,updateRun,executed,represented,stack,extended,growth,newCursor,payload⟩ :=
   RecursiveActivation.activation rfl (allocated σ) n fit (ref.wk (extension σ)) parameters.1 parameters.2
     allocationBase allocationMachine parentRepr lo pointer start (by omega) pointerAbove pointerBelow payloadAbove payloadBelow
     (.inl pointerBefore) fits parentCurrent
 have exterior := RecursiveHistory.activation_exterior rfl (allocated σ) n fit (ref.wk (extension σ)) parameters.1 parameters.2
   allocationBase allocationMachine next parentRepr lo pointer start (by omega) pointerAbove pointerBelow payloadAbove payloadBelow
   pointerBefore fits parentCurrent executed
 have allocatedGrowth : GrowsAllocator b frame 4 σ base before (allocated σ) allocationBase allocationMachine := by
   intro other hb initial hs
   have same : other=cursor := Word.val.inj (initial.arrays.free.cell.symm.trans owner.arrays.free.cell)
   subst other
   exact declOwner
 have baseExtended : BaseExtends σ.H base allocationBase := fun r => allocationBase_old base cursor r
 have combined := allocatedGrowth.comp growth
 exact ⟨next,addresses,args,entered,
   (run_append_ok declRun).trans ((run_append_ok checkedProbe).trans executed),represented,stack.trans declStack,
   baseExtended.trans (extension σ) extended,by simpa only [Nat.add_zero] using combined,newCursor,payload,exterior⟩

namespace Checks
open CountdownWitness
abbrev F := CountdownWitness.F
def initial := callee.setLocal (.here : Idx (Parameters GuardedRecursion.A) (.val .uint)) (countValue 1 (by decide))
def before := writeMachine ParentPrefixes.Checks.input 3 w[1]

theorem source_prefix : (Stmt.assignLocal (.here : Idx (Parameters GuardedRecursion.A) (.val .uint)) (.simple (.lit 1 rfl))).run callee=
 .ok ⟨initial,List.prefix_refl _⟩ := by rfl

theorem target_prefix : run [.push w[1],.mstore 3] ParentPrefixes.Checks.input=.ok before 0 := by rfl

theorem initial_repr : StateRepr 1 2 16 F initial P.base before :=
 ParentPrefixes.Checks.initial.setVal .here (countValue 1 (by decide)) w[1] (ReprV.uint_of rfl)

theorem initial_owner : StructAllocatorRepr initial.heap P.base 16 (⟨22,by decide⟩ : Fin W) before :=
 ParentPrefixes.Checks.ownership.localWrite 3 (by decide) (by decide) w[1]

theorem within : 0<initial.heap.len P.r0 .dyn := by
 change 0<callee.heap.len P.r0 .dyn
 rw [HeapDomain.Checks.length_zero]
 decide

/-- A real callRec invocation enters a zero-counter child and returns after
one allocating activation; source heap growth survives native caller restore. -/
theorem native_return : (body 2).run initial=.ok ⟨allocated initial,extension initial⟩ := by
 let parent := allocated initial
 let ref := P.r0.wk (extension initial)
 let child : State P.C (Parameters GuardedRecursion.A) := parent.withEnv (countValue 0 W_pos,(some ref,()))
 have parameters := allocated_parameters initial 0 (by decide) P.r0 rfl rfl
 have args := next_eval rfl parent 0 (by decide) ref parameters.1 parameters.2
 have childRun := source_zero child 0 rfl
 have native := call_return (nextArgs GuardedRecursion.A rfl) .none .refl (body (C:=P.C) 1).runR
   parent child.env args (⟨child,List.prefix_refl _⟩ : Solidity.Out P.C parent.H (Parameters GuardedRecursion.A)) childRun
 have returned : (.call "allocatingCountdown" (nextArgs GuardedRecursion.A rfl) .none (body 1) : Stmt P.C (Parameters GuardedRecursion.A) (Parameters GuardedRecursion.A)).run parent=
     .ok ⟨parent,List.prefix_refl _⟩ := by
   change TRun.call (nextArgs GuardedRecursion.A rfl) .none .refl (body 1).runR parent=_
   rw [native]
   simp only [exported,CallRet.enterT,CallRet.leaveT,TEnv.wk_self]
   rfl
 rw [source_positive initial 1 0 (by decide) P.r0 rfl rfl within,returned]
 rfl

noncomputable def childMachine : Machine :=
 (activation initial 0 (by decide) P.r0 rfl rfl within P.base before initial_repr
   (⟨22,by decide⟩ : Fin W) initial_owner (by decide) (by decide) 8 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).choose

def parent := allocated initial
def reference := P.r0.wk (extension initial)
def child := parent.withEnv (Δ:=Parameters GuardedRecursion.A) (countValue 0 W_pos,(some reference,()))
def allocationMachine := writeMachine (allocateMachine before (⟨22,by decide⟩ : Fin W) size) 4 w[22]
noncomputable def childAddresses : Nat → Fin W :=
 (activation initial 0 (by decide) P.r0 rfl rfl within P.base before initial_repr
   (⟨22,by decide⟩ : Fin W) initial_owner (by decide) (by decide) 8 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).choose_spec.choose

theorem specification :
 (nextArgs GuardedRecursion.A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters GuardedRecursion.A) [] (Parameters GuardedRecursion.A)).enterT (parent.withEnv child.env)).st=child ∧
 run (code (C:=P.C) 2 F 8) before=.ok childMachine 0 ∧
 StateRepr 1 2 16 F child childAddresses childMachine ∧ childMachine.stack=before.stack ∧
 BaseExtends initial.H P.base childAddresses ∧
 GrowsAllocator 2 16 4 initial P.base before child childAddresses childMachine ∧
 childMachine.mem 8=w[12] ∧
 (∀ i, i<2 → childMachine.mem (10+i)=allocationMachine.mem (2+i)) ∧
 (∀ x, x≠8 → x≠3 → (x<10 ∨ 12≤x) → childMachine.mem x=allocationMachine.mem x) :=
 (activation initial 0 (by decide) P.r0 rfl rfl within P.base before initial_repr
   (⟨22,by decide⟩ : Fin W) initial_owner (by decide) (by decide) 8 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).choose_spec.choose_spec

theorem child_owner : StructAllocatorRepr child.heap childAddresses 16 (⟨26,by decide⟩ : Fin W) childMachine :=
 specification.2.2.2.2.2.2.1 (⟨22,by decide⟩ : Fin W) (by decide) initial_owner (by decide)

theorem child_observations :
 (childMachine.stack,[childMachine.mem 0,childMachine.mem 1,childMachine.mem 2,childMachine.mem 3,childMachine.mem 4,
 childMachine.mem 7,childMachine.mem 8,childMachine.mem 9,childMachine.mem 10,childMachine.mem 11,childMachine.mem 12,childMachine.mem 13,
 childMachine.mem 16,childMachine.mem 17,childMachine.mem 18,childMachine.mem 20,childMachine.mem 21,
 childMachine.mem 22,childMachine.mem 23,childMachine.mem 24,childMachine.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[0],w[22],w[10],w[12],w[99],w[16],w[1],w[0],w[0],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 rcases specification with ⟨args,entry,executed,repr,stack,base,growth,cursor,payload,exterior⟩
 have counter := RecursiveHistory.counter_word child 0 W_pos rfl childAddresses childMachine repr
 have refWord := payload 0 (by decide)
 have countWord := payload 1 (by decide)
 change childMachine.mem 10=allocationMachine.mem 2 at refWord
 change childMachine.mem 11=allocationMachine.mem 3 at countWord
 rw [stack,counter,cursor,refWord,countWord,
   exterior 0 (by decide) (by decide) (.inl (by decide)),exterior 1 (by decide) (by decide) (.inl (by decide)),
   exterior 2 (by decide) (by decide) (.inl (by decide)),exterior 4 (by decide) (by decide) (.inl (by decide)),
   exterior 7 (by decide) (by decide) (.inl (by decide)),exterior 9 (by decide) (by decide) (.inl (by decide)),
   exterior 12 (by decide) (by decide) (.inr (by decide)),exterior 13 (by decide) (by decide) (.inr (by decide)),
   exterior 16 (by decide) (by decide) (.inr (by decide)),exterior 17 (by decide) (by decide) (.inr (by decide)),
   exterior 18 (by decide) (by decide) (.inr (by decide)),exterior 20 (by decide) (by decide) (.inr (by decide)),
   exterior 21 (by decide) (by decide) (.inr (by decide)),exterior 22 (by decide) (by decide) (.inr (by decide)),
   exterior 23 (by decide) (by decide) (.inr (by decide)),exterior 24 (by decide) (by decide) (.inr (by decide)),
   exterior 25 (by decide) (by decide) (.inr (by decide))]
 with_unfolding_all rfl

theorem running_turn : loopTurn (run (guardCompiled (C:=P.C) 2 F).code) (run (code (C:=P.C) 2 F 8)) before=.inl childMachine := by
 have guard := guard_run initial 1 (by decide) rfl P.base before initial_repr
 exact successful_turn _ _ _ _ guard specification.2.2.1

theorem stopped_turn : loopTurn (run (guardCompiled (C:=P.C) 2 F).code) (run (code (C:=P.C) 2 F 8)) childMachine=.inr (.ok childMachine 0) := by
 have guard := guard_run child 0 W_pos rfl childAddresses childMachine specification.2.2.2.1
 exact empty_turn _ _ _ guard

theorem stopped : loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (code (C:=P.C) 2 F 8)) 2 before=.inr (.ok childMachine 0) := by
 simp only [loopIterN,running_turn,stopped_turn]

theorem not_returned_parent : ¬StateRepr 1 2 16 F parent childAddresses childMachine := by
 intro parentRepr
 have old := parentRepr.core.vals (.here : Idx (Parameters GuardedRecursion.A) (.val .uint))
 change ReprV .uint (countValue 1 (by decide)) (childMachine.mem 3) at old
 have word := Restore.uint_unique old (ReprV.uint_of rfl : ReprV .uint (countValue 1 (by decide)) w[1])
 have counter := RecursiveHistory.counter_word child 0 W_pos rfl childAddresses childMachine specification.2.2.2.1
 change childMachine.mem 3=w[0] at counter
 rw [counter] at word
 have different : w[0]≠w[1] := by decide
 exact different word


/-- Actual paired unwind restores this native parent while retaining the
allocated object and cursor. Saved words are derived from the same entry. -/
theorem returned_parent : ∃ last,
 run (PairedUnwind.code 2 8 7 GuardedRecursion.A) childMachine=.ok last 0 ∧
 StateRepr 1 2 16 F parent childAddresses last ∧ last.stack=childMachine.stack ∧
 last.mem 8=w[10] ∧ last.mem 2=childMachine.mem 2 ∧
 GrowsAllocator 2 16 0 child childAddresses childMachine parent childAddresses last ∧
 (∀ x,16≤x → last.mem x=childMachine.mem x) ∧
 (∀ x,x≠8 → x≠2 → x≠3 → last.mem x=childMachine.mem x) := by
 rcases specification with ⟨args,entered,run,repr,stack,base,growth,cursor,payload,exterior⟩
 have bottom : childMachine.mem 7=w[10] := exterior 7 (by decide) (by decide) (.inl (by decide))
 have saved : ∀ j,j<1 → childMachine.mem (10+2*j)=childMachine.mem 2 ∧
     childMachine.mem (10+2*j+1)=.val (wmod (1-j)) := by
   intro j small
   have zero : j=0 := by omega
   subst j
   have r := payload 0 (by decide)
   have c := payload 1 (by decide)
   have unchanged := exterior 2 (by decide) (by decide) (.inl (by decide))
   exact ⟨r.trans unchanged.symm,c⟩
 obtain ⟨last,running,reached,finalStack,finalCursor,reference,growth0,high,outside⟩ :=
   ParentPrefixes.running_prefix parent childAddresses 1 1 1 (by decide) (by decide) (by decide)
     childMachine repr 8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) cursor bottom saved
 have finalBottom : last.mem 7=w[10] := (outside 7 (by decide) (by decide) (by decide)).trans bottom
 have stopped := ParentStop.stop_after_running running finalCursor finalBottom
 exact ⟨last,PairedUnwind.run_of_stopped stopped,reached,finalStack,finalCursor,reference,growth0,high,outside⟩

def image : List Instr := [.loop (guardCompiled (C:=P.C) 2 F).code (code (C:=P.C) 2 F 8)] ++
 PairedUnwind.code 2 8 7 GuardedRecursion.A

/-- A completed actual allocating recursive source call and the SAME fixed
runtime image meet at the represented returned parent and exact growth four. -/
theorem whole : GrowingResult 1 2 16 4 F initial P.base before ((body 2).run initial) (run image before) := by
 obtain ⟨last,returned,represented,stack,cursor,reference,growth0,high,outside⟩ := returned_parent
 have descended := successful_loop _ _ _ _ _ stopped
 have complete : run image before=.ok last 0 := (run_append_ok descended).trans returned
 rcases specification with ⟨args,entered,run,repr,entryStack,base,growth,entryCursor,payload,exterior⟩
 have combined := growth.comp growth0
 exact .inl ⟨⟨parent,extension initial⟩,last,childAddresses,native_return,complete,represented,
   stack.trans entryStack,base,by simpa only [Nat.add_zero] using combined⟩

/-- A too-shallow quotation still exhausts, even though allocation and the
first read are valid. No failed source state is reconstructed. -/
theorem shallow_exhausts : (body 1).run initial=.error .exhausted := by
 let parent := allocated initial
 let ref := P.r0.wk (extension initial)
 have parameters := allocated_parameters initial 0 (by decide) P.r0 rfl rfl
 have args := next_eval rfl parent 0 (by decide) ref parameters.1 parameters.2
 have failed : (.call "allocatingCountdown" (nextArgs GuardedRecursion.A rfl) .none (body 0) : Stmt P.C (Parameters GuardedRecursion.A) (Parameters GuardedRecursion.A)).run parent=.error .exhausted := by
   change TRun.call (nextArgs GuardedRecursion.A rfl) .none .refl (body 0).runR parent=_
   simp only [TRun.call,args,CallRet.enterT]
   rfl
 rw [source_positive initial 0 0 (by decide) P.r0 rfl rfl within,failed]
 rfl

theorem shallow_unmatched : ¬GrowingResult 1 2 16 4 F initial P.base before ((body 1).run initial) (run image before) := by
 rw [shallow_exhausts]
 intro same
 rcases same with ⟨out,target,addresses,source,rest⟩ | ⟨source,rest⟩
 · cases source
 · cases source

/-- All returned-parent observations are transported from the SAME entered
child snapshot using actual unwind word preservation, without replaying code. -/
theorem return_observations : ∃ last,
 run image before=.ok last 0 ∧ StateRepr 1 2 16 F parent childAddresses last ∧
 (last.stack,[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 4,last.mem 7,last.mem 8,last.mem 9,
 last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21,
 last.mem 22,last.mem 23,last.mem 24,last.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[1],w[22],w[10],w[10],w[99],w[16],w[1],w[0],w[0],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 obtain ⟨last,returned,represented,stack,cursor,reference,growth0,high,outside⟩ := returned_parent
 have descended := successful_loop _ _ _ _ _ stopped
 have complete : run image before=.ok last 0 := (run_append_ok descended).trans returned
 have counter := RecursiveHistory.counter_word parent 1 (by decide) rfl childAddresses last represented
 have observed := congrArg (fun obs : List Word × List Word => (obs.1,(obs.2.set 3 w[1]).set 6 w[10])) child_observations
 refine ⟨last,complete,represented,?_⟩
 have transfer : (last.stack,[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 4,last.mem 7,last.mem 8,last.mem 9,
     last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21,
     last.mem 22,last.mem 23,last.mem 24,last.mem 25])=
     (childMachine.stack,([childMachine.mem 0,childMachine.mem 1,childMachine.mem 2,childMachine.mem 3,childMachine.mem 4,
       childMachine.mem 7,childMachine.mem 8,childMachine.mem 9,childMachine.mem 10,childMachine.mem 11,childMachine.mem 12,childMachine.mem 13,
       childMachine.mem 16,childMachine.mem 17,childMachine.mem 18,childMachine.mem 20,childMachine.mem 21,
       childMachine.mem 22,childMachine.mem 23,childMachine.mem 24,childMachine.mem 25].set 3 w[1]).set 6 w[10]) := by
   rw [stack,counter,cursor,reference,outside 0 (by decide) (by decide) (by decide),outside 1 (by decide) (by decide) (by decide),
     outside 4 (by decide) (by decide) (by decide),outside 7 (by decide) (by decide) (by decide),outside 9 (by decide) (by decide) (by decide),
     outside 10 (by decide) (by decide) (by decide),outside 11 (by decide) (by decide) (by decide),outside 12 (by decide) (by decide) (by decide),
     outside 13 (by decide) (by decide) (by decide),outside 16 (by decide) (by decide) (by decide),outside 17 (by decide) (by decide) (by decide),
     outside 18 (by decide) (by decide) (by decide),outside 20 (by decide) (by decide) (by decide),outside 21 (by decide) (by decide) (by decide),
     outside 22 (by decide) (by decide) (by decide),outside 23 (by decide) (by decide) (by decide),outside 24 (by decide) (by decide) (by decide),
     outside 25 (by decide) (by decide) (by decide)]
   rfl
 exact transfer.trans observed

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.Checks.whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.Checks.whole
