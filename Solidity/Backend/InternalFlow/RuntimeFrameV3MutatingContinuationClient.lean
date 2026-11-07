import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingContinuation

/-! Populated checked continuation: mutate through the returned old alias,
then allocate and drop a private array. The prefix is actual native recursive
completion; no endpoint is supplied by a client oracle. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingContinuation.Client
noncomputable section
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes CountdownWitness
abbrev A := CountdownWitness.A
abbrev origin := MutatingSource.Checks.rootOut.st
abbrev before := MutatingReturn.Checks.machine
abbrev bases := MutatingPrefixes.Checks.addresses

def write : Stmt P.C (Parameters A) (Parameters A) :=
 .assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 37 rfl)))
def suffix : Prog P.C (Parameters A) (Parameters A) :=
 .cons write (.cons (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr) .nil)
def compiled : CompiledProg 2 F suffix := (compileProg 2 F suffix).get (by decide)
def checked : Calls.Program 2 F suffix := Calls.plain compiled

theorem public_selection : compileProg 2 F suffix=some compiled := rfl

theorem code : checked.code=writeLocalValueCode 2 (.there .here : Idx (Parameters A) (.mem A)) [.push w[0]] [.push w[37]] ++
 declareNewCode (C:=P.C) (Γ:=Parameters A) 2 AllocatingActivation.lengthExpr := rfl

def reference : HRef origin.H A := P.r0.wk MutatingSource.Checks.rootOut.ext
def changed := origin.withHeap (origin.heap.set reference (MObj.setElem .dyn (origin.heap.get reference) 0 (P.uint 37 (by decide))))
def final := AllocatingActivation.allocated changed
def output : Solidity.Out P.C origin.H (Parameters A) := ⟨final,AllocatingActivation.extension changed⟩

theorem old_length : origin.heap.len reference .dyn=2 := MutatingSource.Checks.objects.1

theorem write_source : write.run origin=.ok ⟨changed,List.prefix_refl _⟩ := by
 obtain ⟨word,represented,source,target,repr,words⟩ := Footprint.write_local
   MutatingReturn.Checks.specification.2.1 (.there .here) reference rfl
   (.simple (.lit 0 rfl)) (.simple (.lit 37 rfl))
   ⟨_,.core _ rfl⟩ ⟨_,.core _ rfl⟩ (⟨0,by decide⟩ : Fin W) rfl (P.uint 37 (by decide)) rfl (by rw [old_length];decide) 8
 exact source

theorem source_suffix : suffix.run origin=.ok output := by
 have written := write_source
 have allocated := DomainTransport.scoped_source changed .bool AllocatingActivation.lengthExpr AllocatingActivation.size rfl
 change write.runR origin=.ok ⟨changed,List.prefix_refl _⟩ at written
 change (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR changed=.ok output at allocated
 change TRun.seq write.runR (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR TRun.nil) origin=_
 simp only [TRun.seq,written,allocated,TRun.nil,Except.map]


theorem exact_cost : checked.cost origin=4 := by decide +kernel

theorem capacity : AllocationInput 2 16 12 callee P.base ParentPrefixes.Checks.input :=
 .inr ⟨by decide,⟨22,by decide⟩,ParentPrefixes.Checks.ownership,by decide⟩

def program : Prog P.C (Parameters A) (Parameters A) :=
 .cons (.block (MutatingActivation.body 3)) suffix
def image : List Instr := MutatingCompletion.image (C:=P.C) 2 F 8 7 ++ checked.code

theorem matched : GrowingResult 1 2 16 12 checked.frag callee P.base ParentPrefixes.Checks.input
 (program.run callee) (run image ParentPrefixes.Checks.input) := by
 have costBound : ∀ out, (MutatingActivation.body 3).run callee=.ok out → checked.cost out.st≤4 := by
   intro out actual
   have same : out=MutatingSource.Checks.rootOut := Except.ok.inj (actual.symm.trans MutatingSource.Checks.root)
   rw [same,exact_cost]
   decide
 obtain ⟨out,source,result⟩ := after_return 2 (by decide) callee P.r0 rfl rfl MutatingSource.Checks.read_bound
   P.base ParentPrefixes.Checks.input ParentPrefixes.Checks.initial ⟨22,by decide⟩ ParentPrefixes.Checks.ownership
   (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) rfl 7 (by decide) (by decide) (by decide) rfl suffix checked 4 (by decide) costBound capacity
 have same : out=MutatingSource.Checks.rootOut := Except.ok.inj (source.symm.trans MutatingSource.Checks.root)
 simpa only [same,exact_cost] using result

def written := writeMachine before 17 w[37]
def machine := writeMachine (allocateMachine written (⟨30,by decide⟩ : Fin W) AllocatingActivation.size) 4 w[30]
def addresses := upd bases origin.H.length (⟨30,by decide⟩ : Fin W)

theorem write_facts :
 run (writeLocalValueCode 2 (.there .here : Idx (Parameters A) (.mem A)) [.push w[0]] [.push w[37]]) before=.ok written 0 ∧
 StateRepr 1 2 16 F changed bases written ∧ Footprint.Words 8 16 before written := by
 obtain ⟨word,represented,source,target,repr,words⟩ := Footprint.write_local
   MutatingReturn.Checks.specification.2.1 (.there .here) reference rfl
   (.simple (.lit 0 rfl)) (.simple (.lit 37 rfl))
   ⟨_,.core _ rfl⟩ ⟨_,.core _ rfl⟩ (⟨0,by decide⟩ : Fin W) rfl (P.uint 37 (by decide)) rfl (by rw [old_length];decide) 8
 obtain ⟨n,fit,value,wordEqual⟩ := represented.uint_inv
 have numeric : n=37 := by change (37:Int)=(n:Int) at value;omega
 have wordValue : word=w[37] := by rw [wordEqual];congr 1;apply Fin.ext;exact numeric
 have address : bases reference.id=P.base P.r0.id := MutatingReturn.Checks.specification.2.2.2.1 P.r0
 simpa only [wordValue,address] using (And.intro target (And.intro repr words))

theorem allocation_facts :
 run (declareNewCode (C:=P.C) (Γ:=Parameters A) 2 AllocatingActivation.lengthExpr) written=.ok machine 0 ∧
 StateRepr 1 2 16 F final addresses machine ∧
 StructAllocatorRepr final.heap addresses 16 (⟨34,by decide⟩ : Fin W) machine ∧
 machine.stack=before.stack ∧ Footprint.Words 8 16 before machine := by
 have original := MutatingReturn.Checks.specification.2.2.2.2.2.1
 have owner : StructAllocatorRepr changed.heap bases 16 (⟨30,by decide⟩ : Fin W) written := by
   have changedOwner := original.setArray reference 0 (by rw [old_length];decide) (P.uint 37 (by decide)) w[37] (ReprV.uint_of rfl)
   have address : bases reference.id=P.base P.r0.id := MutatingReturn.Checks.specification.2.2.2.1 P.r0
   simpa only [address] using changedOwner
 obtain ⟨source,target,represented,owned,stack,words⟩ := Footprint.declare write_facts.2.1 owner (by decide)
   .bool AllocatingActivation.lengthExpr rfl AllocatingActivation.size rfl (by decide) (lo:=8) (by decide) (by decide)
 exact ⟨target,represented.drop (.push .refl),owned,stack,Footprint.words_trans write_facts.2.2 words⟩

theorem suffix_target : run checked.code before=.ok machine 0 := by
 rw [code,run_append_ok write_facts.1]
 exact allocation_facts.1

theorem target : run image ParentPrefixes.Checks.input=.ok machine 0 :=
 (run_append_ok MutatingReturn.Checks.specification.1).trans suffix_target

def sourceOutput : Solidity.Out P.C callee.H (Parameters A) :=
 ⟨final,MutatingSource.Checks.rootOut.ext.trans output.ext⟩

theorem source_program : program.run callee=.ok sourceOutput := by
 have root := MutatingSource.Checks.root
 have blockSource : (.block (MutatingActivation.body 3) : Stmt P.C (Parameters A) (Parameters A)).run callee=
     .ok MutatingSource.Checks.rootOut := by
   change TRun.block (MutatingActivation.body 3).ext (MutatingActivation.body 3).runR callee=_
   unfold TRun.block
   change (MutatingActivation.body 3).runR callee=.ok MutatingSource.Checks.rootOut at root
   rw [root]
   rfl
 rw [program,Prog.run_cons_ok blockSource,source_suffix]
 rfl

theorem growth : GrowsAllocator 2 16 12 callee P.base ParentPrefixes.Checks.input final addresses machine := by
 have suffixGrowth : GrowsAllocator 2 16 4 origin bases before final addresses machine := by
   intro cursor positive owner space
   have original := MutatingReturn.Checks.specification.2.2.2.2.2.1
   have same : cursor=(⟨30,by decide⟩ : Fin W) := Word.val.inj (owner.arrays.free.cell.symm.trans original.arrays.free.cell)
   subst cursor
   exact allocation_facts.2.2.1
 exact MutatingReturn.Checks.specification.2.2.2.2.1.comp suffixGrowth

theorem bases_preserved : BaseExtends callee.H P.base addresses :=
 BaseExtends.trans MutatingSource.Checks.rootOut.ext MutatingReturn.Checks.specification.2.2.2.1
   (fun r => allocationBase_old bases (⟨30,by decide⟩ : Fin W) r)

theorem endpoint :
 program.run callee=.ok sourceOutput ∧ run image ParentPrefixes.Checks.input=.ok machine 0 ∧
 StateRepr 1 2 16 F final addresses machine ∧ machine.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 12 callee P.base ParentPrefixes.Checks.input final addresses machine :=
 ⟨source_program,target,allocation_facts.2.1,allocation_facts.2.2.2.1.trans MutatingReturn.Checks.specification.2.2.1,
 bases_preserved,growth⟩

theorem source_bindings :
 ((TEnv.get (.here : Idx (Parameters A) (.val .uint)) final.env).val,
 (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) final.env).map HRef.id,final.H.length)=(2,some 0,5) := rfl

theorem written_source : final.heap.readAddr
 (.index (reference.wk (AllocatingActivation.extension changed)) .dyn (countValue 0 W_pos))=some (P.uint 37 (by decide)) := by
 have changedWrite : origin.heap.writeAddr (.index reference .dyn (countValue 0 W_pos)) (P.uint 37 (by decide))=some changed.heap := by
   simp only [Heap.writeAddr,Heap.setIndex,HeapDomain.index_nat]
   exact if_pos (by rw [←show origin.heap.len reference .dyn=(MObj.elems .dyn (origin.heap.get reference)).length from rfl,old_length];decide)
 have changedRead := Heap.readAddr_writeAddr_same changedWrite
 have kept : Heap.Keeps (AllocatingActivation.extension changed) changed.heap final.heap :=
   Heap.keeps_alloc changed.heap (AllocatingActivation.object changed)
 have finalRead := Heap.Keeps.readAddr kept (.index reference .dyn (countValue 0 W_pos))
 rw [changedRead] at finalRead
 exact finalRead

theorem observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,
 machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 20,machine.mem 21,
 machine.mem 22,machine.mem 23,machine.mem 24,machine.mem 25,machine.mem 26,machine.mem 27,machine.mem 28,machine.mem 29,
 machine.mem 30,machine.mem 31,machine.mem 32,machine.mem 33])=
 ([w[77]],[w[34],w[16],w[16],w[2],w[30],w[10],w[10],w[99],w[16],w[2],w[16],w[1],
 w[2],w[37],w[2],w[1],w[4],w[3],w[0],w[0],w[0],w[3],w[0],w[0],w[0],w[3],w[0],w[0],w[0]]) := by
 have prior := MutatingReturn.Checks.observations
 have stack := (Prod.mk.inj prior).1
 have cells := (Prod.mk.inj prior).2
 simp only [List.cons.injEq] at cells
 rcases cells with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,tail⟩
 have owner := MutatingReturn.Checks.specification.2.2.2.2.2.1
 change (before.stack,[w[34],before.mem 1,before.mem 2,before.mem 3,w[30],before.mem 7,before.mem 8,before.mem 9,
 before.mem 10,before.mem 11,before.mem 12,before.mem 13,before.mem 16,w[37],before.mem 18,before.mem 20,before.mem 21,
 before.mem 22,before.mem 23,before.mem 24,before.mem 25,before.mem 26,before.mem 27,before.mem 28,before.mem 29,
 w[3],before.mem 31,before.mem 32,before.mem 33])=_
 rw [stack,h1,h2,h3,h7,h8,h9,h10,h11,h12,h13,h16,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,
 owner.arrays.free.zero 31 (by decide),owner.arrays.free.zero 32 (by decide),owner.arrays.free.zero 33 (by decide)]

theorem wrong_cost : ¬GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input final addresses machine := by
 intro wrong
 have owned := wrong (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide)
 have cursor := owned.arrays.free.cell
 rw [allocation_facts.2.2.1.arrays.free.cell] at cursor
 cases cursor

theorem not_revert : run image ParentPrefixes.Checks.input≠.revert := by rw [target];intro wrong;cases wrong

theorem wrong_source_value : final.heap.readAddr
 (.index (reference.wk (AllocatingActivation.extension changed)) .dyn (countValue 0 W_pos))≠some (P.uint 1 (by decide)) := by
 rw [written_source]
 decide

theorem target_facts : machine.mem 0=w[34] ∧ machine.mem 2=w[16] ∧ machine.mem 3=w[2] ∧
 machine.mem 4=w[30] ∧ machine.mem 17=w[37] ∧ machine.mem 21=w[4] := by
 have cells := (Prod.mk.inj observations).2
 simp only [List.cons.injEq] at cells
 rcases cells with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,tail⟩
 exact ⟨h0,h2,h3,h4,h17,h21⟩

theorem wrong_alias : machine.mem 2≠machine.mem 4 := by rw [target_facts.2.1,target_facts.2.2.2.1];decide
theorem omitted_allocation : machine.mem 0≠w[30] := by rw [target_facts.1];decide
theorem wrong_scalar : machine.mem 3≠w[3] := by rw [target_facts.2.2.1];decide
theorem wrong_root : machine.mem 21≠w[37] := by rw [target_facts.2.2.2.2.2];decide
theorem fresh_identity : (changed.alloc (AllocatingActivation.object changed)).2.id=4 ∧ reference.id=0 := ⟨rfl,rfl⟩
theorem not_fault : run image ParentPrefixes.Checks.input≠.fault := by rw [target];intro wrong;cases wrong

def programAt (depth : Nat) : Prog P.C (Parameters A) (Parameters A) :=
 .cons (.block (MutatingActivation.body depth)) suffix

/-- Every actually sufficient native index reaches the SAME continuation and
runtime image. This is not a recursion-admission cutoff. -/
theorem source_at (depth : Nat) (enough : 2<depth) : (programAt depth).run callee=.ok sourceOutput := by
 obtain ⟨out,actual,size,locals,lengths⟩ := MutatingSource.success depth callee 2 (by decide) P.r0 rfl rfl
   MutatingSource.Checks.read_bound enough
 have same := MutatingSource.bodies depth 3 callee out MutatingSource.Checks.rootOut actual MutatingSource.Checks.root
 rw [same] at actual
 have blockSource : (.block (MutatingActivation.body depth) : Stmt P.C (Parameters A) (Parameters A)).run callee=
     .ok MutatingSource.Checks.rootOut := by
   change TRun.block (MutatingActivation.body depth).ext (MutatingActivation.body depth).runR callee=_
   unfold TRun.block
   change (MutatingActivation.body depth).runR callee=.ok MutatingSource.Checks.rootOut at actual
   rw [actual]
   have scope : (MutatingActivation.body (C:=P.C) depth).ext=Ext.refl := Subsingleton.elim _ _
   simp only [Except.map,scope]
   rfl
 rw [programAt,Prog.run_cons_ok blockSource,source_suffix]
 rfl

theorem matched_at (depth : Nat) (enough : 2<depth) :
 GrowingResult 1 2 16 12 F callee P.base ParentPrefixes.Checks.input
 ((programAt depth).run callee) (run image ParentPrefixes.Checks.input) :=
 .inl ⟨sourceOutput,machine,addresses,source_at depth enough,target,endpoint.2.2.1,endpoint.2.2.2.1,bases_preserved,growth⟩

theorem shallow (depth : Nat) (short : depth≤2) : (programAt depth).run callee=.error .exhausted := by
 have failed := MutatingSource.exhaustion depth callee 2 (by decide) P.r0 rfl rfl MutatingSource.Checks.read_bound short
 change (MutatingActivation.body depth).runR callee=.error .exhausted at failed
 change TRun.seq (TRun.block (MutatingActivation.body depth).ext (MutatingActivation.body depth).runR) suffix.runR callee=_
 simp only [TRun.seq,TRun.block,failed,Except.map]

theorem shallow_refused (depth : Nat) (short : depth≤2) :
 ¬GrowingResult 1 2 16 12 F callee P.base ParentPrefixes.Checks.input
 ((programAt depth).run callee) (run image ParentPrefixes.Checks.input) := by
 intro matched
 rcases matched with ⟨out,last,base,source,rest⟩ | ⟨source,rest⟩
 · rw [shallow depth short] at source
   cases source
 · rw [shallow depth short] at source
   cases source

end
end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingContinuation.Client
