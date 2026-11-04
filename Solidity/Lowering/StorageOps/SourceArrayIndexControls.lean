import Solidity.Lowering.StorageOps.SourceArrayIndex
import Solidity.Lowering.StorageOps.SourceWordWriteControls
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Real raw Source cells, PUBLIC represented graph and guarded target reads.
An older populated child remains a raw alias while fresh indexing rejects it. -/
namespace Solidity.Lowering.StorageOps.SourceArrayIndexControls
open Solidity.Backend.StorageOps TypeGraph Solidity.Storage.Representation Solidity.Storage.Representation.Graph
abbrev graph := CopyDemandControls.graph
def ix (i : Fin 3) : Index := ⟨i.val,by omega⟩
def two : Semantics.Word := ⟨2,by decide⟩
def w53 : Semantics.Word := ⟨53,by decide⟩
def w59 : Semantics.Word := ⟨59,by decide⟩
def w61 : Semantics.Word := ⟨61,by decide⟩
def old : Value graph (.array (.prim .uint)) :=
 .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
 (fun i=>.present (.prim (if i.val=0 then w53 else if i.val=1 then w59 else w61)))
def base : Solidity.Storage.Loc := .root 0
def store : Solidity.Storage.Representation.Store := fun l=>
 if l=base then two else if l=.data base 0 then w53 else if l=.data base 1 then w59 else if l=.data base 2 then w61 else ClearDemands.zero

def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
 (.cons (.stateVar (.array SourceWordWriteControls.uintSyntax .none) none none none false "values" .none)
  (.cons (.stateVar SourceWordWriteControls.uintSyntax none none none false "other" .none) .nil))) .nil)
def env : Source.Env := unit.env
def path : Source.SPath := ⟨⟨some "C","values"⟩,[]⟩
def other : Source.SPath := ⟨⟨some "C","other"⟩,[]⟩
def child (i : Nat) := path.go (.index i)
def address : Roadmap.Address := ⟨7,by decide⟩
def storage : Source.Storage env.layout env.cellTy :=
 let s0 := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write path (.int 2 (by decide))
 let s1 := s0.write (child 0) (.int 53 (by decide))
 let s2 := s1.write (child 1) (.int 59 (by decide))
 let s3 := s2.write (child 2) (.int 61 (by decide))
 s3.write other (.int 97 (by decide))
def state : Source.St env :=
 { ex :=
    { world := ⟨fun a=>if a=address then
        {balance := 19,nonce:=3,code:=some 0,storage:=storage}
        else Source.Account.empty _⟩
      transient:=Source.Transient.empty
      journal:=[] }
   heap:=Source.Heap.empty
   events:=[]
   logs:=[]
   fnLocals:=⟨[],.nil⟩ }
def frame : Source.Fr := {this:=address,sender:=⟨13,by decide⟩,value:=⟨0,by decide⟩,static:=true,contract:="C"}
def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
def target : Evm.Machine := {SourceWordWriteControls.machine with
 store:=.ofFn (fun s=>if s=.root 0 then 2 else if s=.data (.root 0) 0 then 53 else
  if s=.data (.root 0) 1 then 59 else if s=.data (.root 0) 2 then 61 else if s=.root 9 then 99 else 0)}
def sourceRun (i : Nat) := (SourceArrayIndex.read (E:=env) (Γ:=[]) frame path (.int Source.IntTy.u256) i).run initial
def targetInput (i : Fin 3) : Evm.Machine := {target with stack:=.val ⟨(ix i).val,(ix i).isLt⟩ :: .slot (.root 0) :: target.stack}
def targetRun (i : Fin 3) := Evm.run TargetArrayRead.code (targetInput i)
def captured : Source.Loc env.layout [] (.int Source.IntTy.u256) := .stor (child 2)
def aliasRead := (Source.readLoc frame captured).run initial
def unguarded := Evm.run (TargetOperations.readCode (.data (.root 0) 2)) target

open Solidity.Storage

theorem before : Represented old (PrimitivePop.queries [ix 1]) base store := by
  intro q member
  simp only [Solidity.Backend.StorageOps.PrimitivePop.queries,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed
    change some two=some word at observed
    cases observed
    rfl
  · refine ⟨⟨by change 1<lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed
    change some w59=some word at observed
    cases observed
    rfl

def sourceView (s : Source.St env) :=
 ([SourceArrayDeleteTarget.wordAt frame s.ex path,SourceArrayDeleteTarget.wordAt frame s.ex (child 0),
 SourceArrayDeleteTarget.wordAt frame s.ex (child 1),SourceArrayDeleteTarget.wordAt frame s.ex (child 2),
 SourceArrayDeleteTarget.wordAt frame s.ex other],s.ex.journal.length,
 (s.ex.world.accounts address).balance,(s.ex.world.accounts address).nonce,
 (s.ex.world.accounts address).code,s.events.length,s.logs.length)
def targetView (m : Evm.Machine) :=
 ([m.store (.root 0),m.store (.data (.root 0) 0),m.store (.data (.root 0) 1),m.store (.data (.root 0) 2),m.store (.root 9)],
 m.stack,m.mem 0,m.bal (Evm.wmod 0),m.bal₀ (Evm.wmod 0),m.self,m.caller,m.callvalue,m.timestamp,m.accepts (Evm.wmod 0) (Evm.wmod 0))
def ordered : Prop :=
 (sourceRun 0,sourceRun 1,sourceRun 2,aliasRead,targetRun 0,targetRun 1,targetRun 2,unguarded,
 (TargetArrayRead.path (ix 2)).read Value.dflt old,(TargetArrayRead.path (ix 2)).readLive Value.dflt old,
 sourceView state,sourceView (sourceRun 1).2.2,targetView target,
 targetView {target with stack:=.val (Evm.wmod 59)::target.stack}) =
 ((.ok (.int 53 (by decide)),initial),(.ok (.int 59 (by decide)),initial),
 (.error (.revert (Source.panicData .index)),initial),(.ok (.int 61 (by decide)),initial),
 .ok {target with stack:=.val (Evm.wmod 53)::target.stack} 0,
 .ok {target with stack:=.val (Evm.wmod 59)::target.stack} 0,.revert,
 .ok {target with stack:=.val (Evm.wmod 61)::target.stack} 0,
 some (.prim w61),none,
 ([some 2,some 53,some 59,some 61,some 97],0,19,3,some 0,0,0),
 ([some 2,some 53,some 59,some 61,some 97],0,19,3,some 0,0,0),
 ([2,53,59,61,99],[.val (Evm.wmod 23),.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false),
 ([2,53,59,61,99],[.val (Evm.wmod 59),.val (Evm.wmod 23),.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false))

theorem initial_agreement : ∀ q ∈ PrimitivePop.queries (G:=graph) (p:=.uint) [ix 1],
 target.store.cells (TargetOperations.toSlot (q.location base) (TargetOperations.query_keysFit q base True.intro)) = TargetOperations.encodeWord (store (q.location base)) := by decide

def certificate := SourceArrayIndex.represented_read env [] frame path .nil state rfl rfl
 (.int 2 (by decide)) 2 (by decide) rfl rfl 0 graph old (ix 1) (.prim w59) rfl rfl
 rfl (.int 59 (by decide)) rfl rfl base True.intro store target target.stack before initial_agreement

def failure_certificate := SourceArrayIndex.bounds_failure env [] frame path (.int Source.IntTy.u256) 2
 .nil state rfl rfl (.int 2 (by decide)) 2 (by decide) rfl rfl target target.stack (.root 0) (by decide) rfl (by decide)

theorem observations : ordered := by
  have s0 : sourceRun 0=(.ok (.int 53 (by decide)),initial) := by rfl
  have s1 : sourceRun 1=(.ok (.int 59 (by decide)),initial) := certificate.1
  have s2 : sourceRun 2=(.error (.revert (Source.panicData .index)),initial) := failure_certificate.1
  have t0 : targetRun 0=.ok {target with stack:=.val (Evm.wmod 53)::target.stack} 0 := by
    rw [targetRun,targetInput,Solidity.Backend.StorageOps.TargetArrayRead.run_current,if_pos (by decide)]
    rfl
  have t1 : targetRun 1=.ok {target with stack:=.val (Evm.wmod 59)::target.stack} 0 := certificate.2.1
  have t2 : targetRun 2=.revert := failure_certificate.2
  unfold ordered
  rw [s0,s1,s2,t0,t1,t2]
  rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndexControls.before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms before
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndexControls.initial_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_agreement
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndexControls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndexControls.failure_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceArrayIndexControls.observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms observations
end Solidity.Lowering.StorageOps.SourceArrayIndexControls
