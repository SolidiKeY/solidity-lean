import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeUnwind
/-! Actual old-object mutation before allocating recursive call entry.
Length and frame transport replace global heap-contents preservation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

def value {C : Contract} : Val C (Parameters A) .uint := .simple (.local .here)
def write {C : Contract} : Stmt C (Parameters A) (Parameters A) :=
 .assignMem (.index .dyn (.var (.there .here) rfl) decrement) (.val value)
def valueCompiled {C : Contract} (b : Nat) (F : Frag (Parameters A)) : CompiledVal b F (value (C:=C)) :=
 ⟨_,.core _ rfl⟩
def selected {C : Contract} (b : Nat) (F : Frag (Parameters A)) : CompiledStmt b F (write (C:=C)) :=
 ⟨F,_,.write F (.there .here) rfl decrement value _ _ (compiled b F).cert (valueCompiled b F).cert⟩
def changed {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A) (n : Nat) :=
 σ.withHeap (σ.heap.set ref (MObj.setElem .dyn (σ.heap.get ref) n σ.env.1))

theorem public_selection {C : Contract} (b : Nat) (F : Frag (Parameters A)) :
 compileStmt b F (write (C:=C))=some (selected b F) := rfl

theorem write_addr {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (n : Nat) (fit : n<W) (within : n<σ.heap.len ref .dyn) :
 σ.heap.writeAddr (.index ref .dyn (countValue n fit)) σ.env.1=some (changed σ ref n).heap := by
 simp only [Heap.writeAddr,Heap.setIndex,HeapDomain.index_nat]
 exact if_pos within

theorem source_write {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn) :
 (write (C:=C)).run σ=.ok ⟨changed σ ref n,List.prefix_refl _⟩ := by
 have index := decrement_eval rfl σ n fit ref counter alias
 change TRun.assignMem (.index .dyn (.var (.there .here) rfl) decrement) (.val value) σ=_
 simp only [TRun.assignMem,MSrc.mvalT,value,Val.evalT,Simple.evalT,MLoc.addrT,MPath.mvalT,alias,index,ok_bind]
 simp only [pure,Except.pure,bind,Except.bind]
 change (do
   let hp ← TRes.ofOpt (σ.heap.writeAddr (.index ref .dyn (countValue n (by omega))) σ.env.1)
   pure (⟨σ.withHeap hp,List.prefix_refl _⟩ : Solidity.Out C σ.H (Parameters A)))=_
 rw [write_addr σ ref n (by omega) within]
 rfl

theorem lengths {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (n : Nat) (fit : n<W) (within : n<σ.heap.len ref .dyn) {R : RefTy} {E : Ty}
 (other : HRef σ.H R) (a : ArrTy R E) :
 (changed σ ref n).heap.len other a=σ.heap.len other a :=
 Heap.len_writeAddr (write_addr σ ref n fit within) other a

theorem read_after_write {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn) :
 ArrayProbe.value.evalT (changed σ ref n)=.ok σ.env.1 := by
 rw [HeapDomain.probe_eval (changed σ ref n) n fit ref counter alias,
   Heap.readAddr_writeAddr_same (write_addr σ ref n (by omega) within)]
 rfl

/-- Consume the existing complete expression/receiver/index write producer.
The SAME changed heap has full representation and allocator ownership; every
runtime word below the heap remains unchanged even though old contents differ. -/
theorem written {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before) :
 ∃ word,
 ReprV .uint σ.env.1 word ∧
 run (selected (C:=C) b F).code before=.ok (writeMachine before ((base ref.id).val+1+n) word) 0 ∧
 StateRepr L b frame F (changed σ ref n) base (writeMachine before ((base ref.id).val+1+n) word) ∧
 GrowsAllocator b frame 0 σ base before (changed σ ref n) base (writeMachine before ((base ref.id).val+1+n) word) ∧
 Footprint.Words 0 frame before (writeMachine before ((base ref.id).val+1+n) word) := by
 obtain ⟨word,represented,source,target,after,words⟩ := Footprint.write_local repr (.there .here) ref alias
   decrement value (compiled b F) (valueCompiled b F) ⟨n,by omega⟩
   (decrement_eval rfl σ n fit ref counter alias) σ.env.1 rfl within 0
 refine ⟨word,represented,target,after,?_,words⟩
 intro cursor positive owned space
 simpa only [Nat.add_zero] using owned.setArray ref n within σ.env.1 word represented

def code {C : Contract} (b : Nat) (F : Frag (Parameters A)) (pointer : Nat) : List Instr :=
 (selected (C:=C) b F).code ++ AllocatingActivation.code (C:=C) b F pointer

/-- A complete old-object write followed by actual allocating call-frame entry.
There is no Heap.Keeps premise or conclusion for the mutation. Lengths,
representation, ownership and reserved words come from the reached writes. -/
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
 let mutated := changed σ ref n
 let parent := AllocatingActivation.allocated mutated
 let child := parent.withEnv (Δ:=Parameters A)
   (countValue n (by omega),(some (ref.wk (AllocatingActivation.extension mutated)),()))
 ∃ (word : Word) (after : Machine) (addresses : Nat → Fin W),
 ReprV .uint σ.env.1 word ∧
 (write (C:=C)).run σ=.ok ⟨mutated,List.prefix_refl _⟩ ∧
 (nextArgs A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters A) [] (Parameters A)).enterT (parent.withEnv child.env)).st=child ∧
 run (code (C:=C) b F pointer) before=.ok after 0 ∧
 StateRepr L b frame F child addresses after ∧ after.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame 4 σ base before child addresses after ∧
 after.mem pointer=.val (wmod (start+2)) ∧
 (∀ i,i<2 → after.mem (start+i)=before.mem (b+i)) ∧
 (∀ x,0<x → x<frame → x≠b+1 → x≠b+2 → x≠pointer →
   (x<start ∨ start+2≤x) → after.mem x=before.mem x) ∧
 (∀ x,x≠pointer → x≠b+1 → (x<start ∨ start+2≤x) →
   after.mem x=(writeMachine (allocateMachine (writeMachine before ((base ref.id).val+1+n) word)
     cursor AllocatingActivation.size) (cell (b+2)) (.val cursor)).mem x) := by
 obtain ⟨word,wordRepr,writeRun,writeRepr,writeGrowth,writeWords⟩ :=
   written σ n fit ref counter alias within base before repr
 let mutated := changed σ ref n
 let writtenMachine := writeMachine before ((base ref.id).val+1+n) word
 have nextOwner : StructAllocatorRepr mutated.heap base frame cursor writtenMachine :=
   writeGrowth cursor positive owner (by omega)
 have nextWithin : n<mutated.heap.len ref .dyn := by
   rw [lengths σ ref n (by omega) within ref .dyn]
   exact within
 have nextCurrent : writtenMachine.mem pointer=.val (wmod start) :=
   (writeWords pointer (by omega) pointerBelow).trans current
 obtain ⟨after,addresses,args,entered,actual,represented,stack,extended,growth,newPointer,payload,exterior⟩ :=
   AllocatingActivation.activation mutated n fit ref counter alias nextWithin base writtenMachine writeRepr cursor nextOwner
     positive heapSpace lo pointer start localBound pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits nextCurrent
 let allocationMachine := writeMachine (allocateMachine writtenMachine cursor AllocatingActivation.size) (cell (b+2)) (.val cursor)
 have low : ∀ x,0<x → x<frame → x≠b+2 → allocationMachine.mem x=before.mem x := by
   intro x above below privateCell
   have allocatedWords := Footprint.allocation_words (m:=writtenMachine) (lo:=1) (by decide)
     cursor AllocatingActivation.size nextOwner.arrays.free.above
   exact (upd_other _ _ privateCell).trans ((allocatedWords x above below).trans (writeWords x (by omega) below))
 refine ⟨word,after,addresses,wordRepr,source_write σ n fit ref counter alias within,args,entered,
   (run_append_ok writeRun).trans actual,represented,stack,extended,?_,newPointer,?_,?_,exterior⟩
 · simpa only [Nat.zero_add] using writeGrowth.comp growth
 · intro i small
   exact (payload i small).trans (low (b+i) (by omega) (by have bound:=repr.locals;change b+2≤frame at bound;omega) (by omega))
 · intro x above below counterCell privateCell pointerCell outside
   exact (exterior x pointerCell counterCell outside).trans (low x above below privateCell)

def step {C : Contract} (depth : Nat) (back : Unit → Prog C (Parameters A) (Parameters A)) :
 Prog C (Parameters A) (Parameters A) :=
 .cons (.ite nonzero
   (.cons write (.cons (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr)
     (.cons GuardedRecursion.probe (.cons (.callRec "mutatingCountdown" depth (nextArgs A rfl) .none back) .nil)))) .nil) .nil

def body {C : Contract} (depth : Nat) : Prog C (Parameters A) (Parameters A) := recUnroll Prog.recBase step depth

theorem allocated_probe {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn) :
 ArrayProbe.value.evalT (AllocatingActivation.allocated (changed σ ref n))=.ok σ.env.1 := by
 have parameters := AllocatingActivation.allocated_parameters (changed σ ref n) n fit ref counter alias
 have kept : Heap.Keeps (AllocatingActivation.extension (changed σ ref n)) (changed σ ref n).heap
     (AllocatingActivation.allocated (changed σ ref n)).heap :=
   Heap.keeps_alloc (changed σ ref n).heap (AllocatingActivation.object (changed σ ref n))
 exact (DomainTransport.probe_keeps _ _ _ kept n fit ref counter alias parameters.1 parameters.2).trans
   (read_after_write σ n fit ref counter alias within)

/-- Expose the NEW native recursive family, not the old read-only body's
source equation. The actual mutation precedes allocation, probe and call. -/
theorem source_positive {C : Contract} (σ : State C (Parameters A)) (depth n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn) :
 (body (depth+1)).run σ=
 ((.call "mutatingCountdown" (nextArgs A rfl) .none (body depth) : Stmt C (Parameters A) (Parameters A)).run
   (AllocatingActivation.allocated (changed σ ref n))).map
   (fun out => (⟨out.st,(AllocatingActivation.extension (changed σ ref n)).trans out.ext⟩ : Solidity.Out C σ.H (Parameters A))) := by
 have guard := guard_eval σ (n+1) (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have wrote := source_write σ n fit ref counter alias within
 have allocated := DomainTransport.scoped_source (changed σ ref n) .bool AllocatingActivation.lengthExpr AllocatingActivation.size rfl
 have probed := probe_success (AllocatingActivation.allocated (changed σ ref n)) σ.env.1
   (allocated_probe σ n fit ref counter alias within)
 let call : TStep C (Parameters A) (Parameters A) := TRun.call (nextArgs A rfl) .none .refl (body depth).runR
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq write.runR (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
     (TRun.seq GuardedRecursion.probe.runR (TRun.seq call TRun.nil)))) .refl TRun.nil) TRun.nil σ=_
 change write.runR σ=.ok ⟨changed σ ref n,List.prefix_refl _⟩ at wrote
 change (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR (changed σ ref n)=
   .ok ⟨AllocatingActivation.allocated (changed σ ref n),AllocatingActivation.extension (changed σ ref n)⟩ at allocated
 change GuardedRecursion.probe.runR (AllocatingActivation.allocated (changed σ ref n))=
   .ok ⟨AllocatingActivation.allocated (changed σ ref n),List.prefix_refl _⟩ at probed
 change _=(call (AllocatingActivation.allocated (changed σ ref n))).map _
 simp only [TRun.seq,TRun.ite,guard,positive,boolT,wrote,allocated,probed,ok_bind,if_true,Except.map]
 cases actual : call (AllocatingActivation.allocated (changed σ ref n)) with
 | error halt => rfl
 | ok out => simp only [TRun.nil];cases out;rfl

theorem source_zero {C : Contract} (σ : State C (Parameters A)) (depth : Nat)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue 0 W_pos) :
 (body (depth+1)).run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
 have guard := guard_eval σ 0 (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq write.runR (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
     (TRun.seq GuardedRecursion.probe.runR (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (body depth).runR) TRun.nil))))
   .refl TRun.nil) TRun.nil σ=_
 simp only [TRun.seq,TRun.ite,guard,boolT,TRun.nil,Except.map]
 rfl

theorem base_exhausts {C : Contract} (σ : State C (Parameters A)) : (body 0).run σ=.error .exhausted := rfl

/-- Actual write failure absorbs the following private allocation and child
call at each positive quotation; it supplies no failed output state. -/
theorem source_failure {C : Contract} (σ : State C (Parameters A)) (depth : Nat) (halt : THalt)
 (guard : nonzero.evalT σ=.ok true) (failed : write.runR σ=.error halt) :
 (body (depth+1)).run σ=.error halt := by
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq write.runR (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
     (TRun.seq GuardedRecursion.probe.runR (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (body depth).runR) TRun.nil))))
   .refl TRun.nil) TRun.nil σ=_
 simp only [TRun.seq,TRun.ite,guard,boolT,if_true,failed,ok_bind,Except.map]

/-- Abstract one-step boundary: converting iterator and turn equations must
not normalize a concrete compiled instruction image or caller machine. -/
theorem one_eq_turn (condition action : Machine → Evm.Out) (m : Machine) :
 loopIterN condition action 1 m=loopTurn condition action m := by
 change (match loopTurn condition action m with
   | .inl next => .inl next
   | .inr result => .inr result)=loopTurn condition action m
 cases loopTurn condition action m <;> rfl

namespace Checks
open CountdownWitness
abbrev F := CountdownWitness.F
abbrev before := ParentPrefixes.Checks.input

def mutated := changed callee P.r0 1
def parent := AllocatingActivation.allocated mutated
def reference := P.r0.wk (AllocatingActivation.extension mutated)
def child := parent.withEnv (Δ:=Parameters A) (countValue 1 (by decide),(some reference,()))
def writtenMachine := writeMachine before 18 w[2]
def allocationMachine := writeMachine (allocateMachine writtenMachine (⟨22,by decide⟩ : Fin W) AllocatingActivation.size) 4 w[22]

theorem source_prefix : (write (C:=P.C)).run callee=.ok ⟨mutated,List.prefix_refl _⟩ :=
 source_write callee 1 (by decide) P.r0 rfl rfl (by rw [HeapDomain.Checks.length_zero];decide)

theorem probe_value : ArrayProbe.value.evalT parent=.ok (P.uint 2 (by decide)) :=
 allocated_probe callee 1 (by decide) P.r0 rfl rfl (by rw [HeapDomain.Checks.length_zero];decide)

theorem not_keeps : ¬Heap.Keeps (List.prefix_refl callee.H) callee.heap mutated.heap := by
 intro kept
 have same := DomainTransport.probe_keeps callee mutated (List.prefix_refl _) kept 1 (by decide) P.r0 rfl rfl rfl rfl
 change ArrayProbe.value.evalT (changed callee P.r0 1)=ArrayProbe.value.evalT callee at same
 rw [read_after_write callee 1 (by decide) P.r0 rfl rfl (by rw [HeapDomain.Checks.length_zero];decide),
   ArrayProbe.Checks.good_evaluated] at same
 have values := congrArg (fun v : PrimTy.uint.Denote => v.val) (Except.ok.inj same)
 change (2:Int)=9 at values
 omega

theorem available : ∃ after addresses,
 (nextArgs A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters A) [] (Parameters A)).enterT (parent.withEnv child.env)).st=child ∧
 run (code (C:=P.C) 2 F 8) before=.ok after 0 ∧
 StateRepr 1 2 16 F child addresses after ∧ after.stack=before.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 4 callee P.base before child addresses after ∧
 after.mem 8=w[12] ∧
 (∀ i,i<2 → after.mem (10+i)=before.mem (2+i)) ∧
 (∀ x,0<x → x<16 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 12≤x) → after.mem x=before.mem x) ∧
 (∀ x,x≠8 → x≠3 → (x<10 ∨ 12≤x) → after.mem x=allocationMachine.mem x) := by
 obtain ⟨word,after,addresses,represented,source,args,entry,actual,repr,stack,extended,growth,cursor,payload,low,exterior⟩ :=
   activation callee 1 (by decide) P.r0 rfl rfl (by rw [HeapDomain.Checks.length_zero];decide)
     P.base before ParentPrefixes.Checks.initial (⟨22,by decide⟩ : Fin W) ParentPrefixes.Checks.ownership
     (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
 have same : word=w[2] := Restore.uint_unique represented (ReprV.uint_of rfl)
 subst word
 exact ⟨after,addresses,args,entry,actual,repr,stack,extended,growth,cursor,payload,low,exterior⟩

noncomputable def machine : Machine := available.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose

theorem specification :
 (nextArgs A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters A) [] (Parameters A)).enterT (parent.withEnv child.env)).st=child ∧
 run (code (C:=P.C) 2 F 8) before=.ok machine 0 ∧
 StateRepr 1 2 16 F child addresses machine ∧ machine.stack=before.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 4 callee P.base before child addresses machine ∧
 machine.mem 8=w[12] ∧
 (∀ i,i<2 → machine.mem (10+i)=before.mem (2+i)) ∧
 (∀ x,0<x → x<16 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 12≤x) → machine.mem x=before.mem x) ∧
 (∀ x,x≠8 → x≠3 → (x<10 ∨ 12≤x) → machine.mem x=allocationMachine.mem x) :=
 available.choose_spec.choose_spec

theorem observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,
 machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 20,machine.mem 21,
 machine.mem 22,machine.mem 23,machine.mem 24,machine.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[1],w[22],w[10],w[12],w[99],w[16],w[2],w[0],w[0],w[2],w[7],w[2],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 rcases specification with ⟨args,entry,actual,repr,stack,extended,growth,cursor,payload,low,exterior⟩
 have counter := RecursiveHistory.counter_word child 1 (by decide) rfl addresses machine repr
 have refWord := payload 0 (by decide)
 have countWord := payload 1 (by decide)
 change machine.mem 10=before.mem 2 at refWord
 change machine.mem 11=before.mem 3 at countWord
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

/-- Ordered source lengths and contents after actual mutation and allocation;
the unrelated older root is framed by address separation, not Heap.Keeps. -/
theorem source_objects :
 child.heap.len reference .dyn=2 ∧
 child.heap.readAddr (.index reference .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) ∧
 child.heap.readAddr (.index reference .dyn (countValue 1 (by decide)))=some (P.uint 2 (by decide)) ∧
 child.heap.len (Evm.Memory.CompileExamples.r1.wk (AllocatingActivation.extension mutated)) .dyn=1 ∧
 child.heap.readAddr (.index (Evm.Memory.CompileExamples.r1.wk (AllocatingActivation.extension mutated)) .dyn (countValue 0 W_pos))=
   some (P.uint 4 (by decide)) := by
 have wrote := write_addr callee P.r0 1 (by decide) (by rw [HeapDomain.Checks.length_zero];decide)
 have kept : Heap.Keeps (AllocatingActivation.extension mutated) mutated.heap parent.heap :=
   Heap.keeps_alloc mutated.heap (AllocatingActivation.object mutated)
 have old7 : callee.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) := by with_unfolding_all rfl
 have old4 : callee.heap.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) := by with_unfolding_all rfl
 have first7 : mutated.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) :=
   (Heap.readAddr_writeAddr_apart wrote (bd:=.index P.r0 .dyn (countValue 0 W_pos)) (by
     change P.r0.id=P.r0.id → (countValue 1 (by decide))≠countValue 0 W_pos
     intro _ same
     have values := congrArg (fun v : PrimTy.uint.Denote => v.val) same
     change (1:Int)=0 at values
     omega)).trans old7
 have other4 : mutated.heap.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) :=
   (Heap.readAddr_writeAddr_apart wrote (bd:=.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos)) (by
     intro same
     change (0:Nat)=1 at same
     omega)).trans old4
 have written2 : mutated.heap.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))=some (P.uint 2 (by decide)) :=
   Heap.readAddr_writeAddr_same wrote
 have len0 := lengths callee P.r0 1 (by decide) (by rw [HeapDomain.Checks.length_zero];decide) P.r0 .dyn
 have len1 := lengths callee P.r0 1 (by decide) (by rw [HeapDomain.Checks.length_zero];decide) Evm.Memory.CompileExamples.r1 .dyn
 refine ⟨(kept.len P.r0 .dyn).trans (len0.trans HeapDomain.Checks.length_zero),?_,?_,
   (kept.len Evm.Memory.CompileExamples.r1 .dyn).trans (len1.trans HeapDomain.Checks.length_one),?_⟩
 · have same := kept.readAddr (.index P.r0 .dyn (countValue 0 W_pos))
   rw [first7] at same
   exact same
 · have same := kept.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))
   rw [written2] at same
   exact same
 · have same := kept.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))
   rw [other4] at same
   exact same

theorem running_turn : loopTurn (run (guardCompiled (C:=P.C) 2 F).code) (run (code (C:=P.C) 2 F 8)) before=.inl machine := by
 have guard := guard_run callee 2 (by decide) rfl P.base before ParentPrefixes.Checks.initial
 exact successful_turn _ _ _ _ guard specification.2.2.1

theorem running_prefix : loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (code (C:=P.C) 2 F 8)) 1 before=.inl machine := by
 exact (one_eq_turn _ _ before).trans running_turn

theorem wrong_probe : ArrayProbe.value.evalT parent≠.ok (P.uint 9 (by decide)) := by
 rw [probe_value]
 intro bad
 have values := congrArg (fun v : PrimTy.uint.Denote => v.val) (Except.ok.inj bad)
 change (2:Int)=9 at values
 omega

theorem target_facts : machine.mem 0=w[26] ∧ machine.mem 1=w[16] ∧ machine.mem 18=w[2] ∧
 machine.mem 21=w[4] ∧ machine.mem 11=w[2] ∧ machine.stack=[w[77]] := by
 have stack := (Prod.mk.inj observations).1
 have cells := (Prod.mk.inj observations).2
 simp only [List.cons.injEq] at cells
 rcases cells with ⟨a0,a1,a2,a3,a4,a7,a8,a9,a10,a11,a12,a13,a16,a17,a18,a20,a21,a22,a23,a24,a25,tail⟩
 exact ⟨a0,a1,a18,a21,a11,stack⟩

theorem missing_mutation : machine.mem 18≠w[9] := by rw [target_facts.2.2.1];decide
theorem unrelated_mutation : machine.mem 21≠w[2] := by rw [target_facts.2.2.2.1];decide
theorem wrong_alias : machine.mem 1≠w[20] := by rw [target_facts.2.1];decide
theorem missing_allocation : machine.mem 0≠w[22] := by rw [target_facts.1];decide
theorem wrong_parent : machine.mem 11≠w[1] := by rw [target_facts.2.2.2.2.1];decide

/-- This is a successful represented bad-index input, not a failed capacity
premise. The real write fails before the actual allocating-entry suffix. -/
abbrev bad := ArrayProbe.Checks.bad
abbrev badMachine := ArrayProbe.Checks.badMachine

theorem bad_source : (write (C:=P.C)).run bad=.error .revert := by
 have index := decrement_eval rfl bad 2 (by decide) P.r0 rfl rfl
 change TRun.assignMem (.index .dyn (.var (.there .here) rfl) decrement) (.val value) bad=_
 simp only [TRun.assignMem,MSrc.mvalT,value,Val.evalT,Simple.evalT,MLoc.addrT,MPath.mvalT,index,ok_bind]
 change (do
   let hp ← TRes.ofOpt (bad.heap.writeAddr (.index P.r0 .dyn (countValue 2 (by decide))) bad.env.1)
   pure (⟨bad.withHeap hp,List.prefix_refl _⟩ : Solidity.Out P.C bad.H (Parameters A)))=_
 have failed : bad.heap.writeAddr (.index P.r0 .dyn (countValue 2 (by decide))) bad.env.1=none := by
   simp only [Heap.writeAddr,Heap.setIndex,HeapDomain.index_nat]
   apply if_neg
   change ¬2<callee.heap.len P.r0 .dyn
   rw [HeapDomain.Checks.length_zero]
   omega
 rw [failed]
 rfl

theorem bad_target : run (code (C:=P.C) 2 F 8) badMachine=.revert := by
 have actual := (selected (C:=P.C) 2 F).cert.correct ArrayProbe.Checks.bad_repr (by decide) (.inl rfl)
 rcases actual with ⟨out,last,addresses,source,target,repr,stack,extended,growth⟩ | ⟨source,target⟩
 · rw [bad_source] at source
   cases source
 · exact run_append_revert target

theorem bad_turn : loopTurn (run (guardCompiled (C:=P.C) 2 F).code) (run (code (C:=P.C) 2 F 8)) badMachine=.inr .revert := by
 have guard := guard_run bad 3 (by decide) rfl P.base badMachine ArrayProbe.Checks.bad_repr
 have actual : loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (code (C:=P.C) 2 F 8)) 1 badMachine=.inr .revert :=
   failing_turn _ _ _ guard bad_target
 exact (one_eq_turn _ _ badMachine).symm.trans actual

theorem bad_body (depth : Nat) : (body (depth+1)).run bad=.error .revert :=
 source_failure bad depth .revert (by simpa only using (guard_eval bad 3 rfl)) bad_source

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation
