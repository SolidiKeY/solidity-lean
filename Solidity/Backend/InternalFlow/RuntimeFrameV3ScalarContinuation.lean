import Solidity.Backend.InternalFlow.RuntimeFrameReturnContinuation
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDemandDual

/-! A populated scalar return is consumed by an actual old-array write and
private allocation. The same returned scalar is the write RHS and allocation
length. The original recursive call and all earlier observations are intact. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarContinuation
noncomputable section
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

abbrev origin := caller.setLocal (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))
def scalar : Simple CountdownWitness.P.C Γ .uint := .local .here
def index : Val CountdownWitness.P.C Γ .uint := .simple (.lit 0 rfl)
def rhs : Val CountdownWitness.P.C Γ .uint := .simple scalar
def write : Stmt CountdownWitness.P.C Γ Γ :=
 .assignMem (.index .dyn (.var reference rfl) index) (.val rhs)
def privateAllocation : Stmt CountdownWitness.P.C Γ Γ :=
 .block (.cons (.declMem (.array (.prim .uint)) (.user "private") (some (.newArr scalar rfl)) rfl rfl) .nil)
def suffix : Prog CountdownWitness.P.C Γ Γ := .cons write (.cons privateAllocation .nil)
def compiled : CompiledProg 1 F suffix := (compileProg 1 F suffix).get (by rfl)
def checked : Calls.Program 1 F suffix := Calls.plain compiled

theorem selected : compileProg 1 F suffix=some compiled := rfl

theorem code : checked.code=writeLocalValueCode 1 reference [.push w[0]] [.mload 4] ++ declareNewCode 1 scalar := rfl

def ref : HRef origin.H CountdownWitness.A := CountdownWitness.P.r0
def changed := origin.withHeap (origin.heap.set ref (MObj.setElem .dyn (origin.heap.get ref) 0 (CountdownWitness.P.uint 3 (by decide))))
def size : Fin W := ⟨3,by decide⟩
def final := (changed.alloc (defaultArray .uint size)).1
def extension : caller.H <+: final.H := List.prefix_append _ _
def output : Solidity.Out CountdownWitness.P.C caller.H Γ := ⟨final,extension⟩
def suffixOutput : Solidity.Out CountdownWitness.P.C origin.H Γ := ⟨final,List.prefix_append _ _⟩
def written := writeMachine machine 17 w[3]
def target := writeMachine (allocateMachine written (⟨22,by decide⟩ : Fin W) size) 5 w[22]
def finalBase := upd addresses origin.H.length (⟨22,by decide⟩ : Fin W)

theorem old_length : origin.heap.len ref .dyn=2 := by
 with_unfolding_all rfl

theorem write_facts : write.run origin=.ok ⟨changed,List.prefix_refl _⟩ ∧
 run (writeLocalValueCode 1 reference [.push w[0]] [.mload 4]) machine=.ok written 0 ∧
 StateRepr 1 1 16 F changed addresses written ∧ Footprint.Words 8 16 machine written := by
 obtain ⟨word,encoded,source,executed,represented,words⟩ := Footprint.write_local
   specification.2.2.1 reference ref rfl index rhs
   ⟨_,.core _ rfl⟩ ⟨_,.core _ rfl⟩ (⟨0,by decide⟩ : Fin W) rfl (CountdownWitness.P.uint 3 (by decide)) rfl (by rw [old_length];decide) 8
 have wordEqual : word=w[3] := Restored.value_unique encoded (ReprV.uint_of rfl)
 have address : addresses ref.id=CountdownWitness.P.base CountdownWitness.P.r0.id := specification.2.2.2.2.1 CountdownWitness.P.r0
 simpa only [wordEqual,address] using (And.intro source (And.intro executed (And.intro represented words)))

theorem private_source : privateAllocation.run changed=.ok suffixOutput := by
 have declared := newArray_decl changed .uint scalar size (show scalar.evalT changed=indexValue size from rfl)
 change TRun.block (.push .refl)
   (TRun.seq (TRun.declMem (.array (.prim .uint)) (some (.newArr scalar rfl)) rfl) TRun.nil) changed=_
 simp only [TRun.block,TRun.seq,declared,TRun.nil,Except.map]
 rfl

theorem source_suffix : suffix.run origin=.ok suffixOutput := by
 have written := write_facts.1
 have allocated := private_source
 change write.runR origin=.ok ⟨changed,List.prefix_refl _⟩ at written
 change privateAllocation.runR changed=.ok suffixOutput at allocated
 change TRun.seq write.runR (TRun.seq privateAllocation.runR TRun.nil) origin=_
 simp only [TRun.seq,written,allocated,TRun.nil,Except.map]

theorem exact_cost : checked.cost origin=4 := by decide +kernel

theorem capacity : AllocationInput 1 16 4 caller CountdownWitness.P.base before :=
 .inr ⟨by decide,⟨22,by decide⟩,initial_owner,by decide⟩

def program (depth : Nat) : Prog CountdownWitness.P.C Γ Γ := .cons (ScalarDual.statement depth) suffix
def image : List Instr := (ScalarDemandDual.outputPlan.at 4).code++checked.code

theorem matched : GrowingResult 1 1 16 4 checked.frag caller CountdownWitness.P.base before
 ((program 4).run caller) (run image before) := by
 have combined := ReturnContinuation.after_return
   (ScalarDemandDual.producer.required_return 4) (ScalarDemandDual.good_entry 4)
   ScalarDual.good_source suffix checked (by decide) (by
     change AllocationInput 1 16 (0+checked.cost origin) caller CountdownWitness.P.base before
     rw [Nat.zero_add,exact_cost]
     exact capacity)
 simpa only [ScalarDemandDual.outputPlan,ScalarDemand.plan,InterfaceV1.RecursiveEmission.at,Nat.zero_add,exact_cost] using combined


theorem allocation_facts :
 run (declareNewCode 1 scalar) written=.ok target 0 ∧
 StateRepr 1 1 16 F final finalBase target ∧
 StructAllocatorRepr final.heap finalBase 16 (⟨26,by decide⟩ : Fin W) target ∧
 target.stack=machine.stack ∧ Footprint.Words 8 16 machine target := by
 have address : addresses ref.id=CountdownWitness.P.base CountdownWitness.P.r0.id := specification.2.2.2.2.1 CountdownWitness.P.r0
 have owner : StructAllocatorRepr changed.heap addresses 16 (⟨22,by decide⟩ : Fin W) written := by
   have updated := DisjointScalarReturn.Client.owner.setArray ref 0 (by change 0<origin.heap.len ref .dyn;rw [old_length];decide)
     (CountdownWitness.P.uint 3 (by decide)) w[3] (ReprV.uint_of rfl)
   simpa only [address] using updated
 obtain ⟨source,executed,represented,allocator,stack,words⟩ :=
   Footprint.declare write_facts.2.2.1 owner (by decide) .uint scalar rfl size rfl (by decide)
     (lo:=8) (by decide) (by decide)
 exact ⟨executed,represented.drop (.push .refl),allocator,stack,Footprint.words_trans write_facts.2.2.2 words⟩

theorem suffix_target : run checked.code machine=.ok target 0 := by
 rw [code,run_append_ok write_facts.2.1]
 exact allocation_facts.1

theorem target_execution : run image before=.ok target 0 :=
 (run_append_ok (ScalarDemandDual.good_execution 4)).trans suffix_target

theorem source_program : (program 4).run caller=.ok output := by
 rw [program,Prog.run_cons_ok ScalarDual.good_source,source_suffix]
 rfl


theorem growth : GrowsAllocator 1 16 4 caller CountdownWitness.P.base before final finalBase target := by
 have suffixGrowth : GrowsAllocator 1 16 4 origin addresses machine final finalBase target := by
   intro cursor positive owner space
   have same : cursor=(⟨22,by decide⟩ : Fin W) :=
     Word.val.inj (owner.arrays.free.cell.symm.trans DisjointScalarReturn.Client.owner.arrays.free.cell)
   subst cursor
   exact allocation_facts.2.2.1
 have prefixGrowth : GrowsAllocator 1 16 0 caller CountdownWitness.P.base before origin addresses machine := by
   rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,actual,_,_⟩
   exact actual
 exact prefixGrowth.comp suffixGrowth

theorem bases_preserved : BaseExtends caller.H CountdownWitness.P.base finalBase :=
 BaseExtends.trans (List.prefix_refl _) specification.2.2.2.2.1
   (fun r => allocationBase_old addresses (⟨22,by decide⟩ : Fin W) r)

theorem endpoint :
 (program 4).run caller=.ok output ∧ run image before=.ok target 0 ∧
 StateRepr 1 1 16 F final finalBase target ∧ target.stack=before.stack ∧
 BaseExtends caller.H CountdownWitness.P.base finalBase ∧
 GrowsAllocator 1 16 4 caller CountdownWitness.P.base before final finalBase target :=
 ⟨source_program,target_execution,allocation_facts.2.1,
   allocation_facts.2.2.2.1.trans (specification.2.2.2.1.trans rfl),bases_preserved,growth⟩

end
end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarContinuation
