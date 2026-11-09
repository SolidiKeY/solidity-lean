import Solidity.Backend.InternalFlow.RuntimeFrameV3HeapDomain
import Solidity.Backend.InternalFlow.RuntimeFrameFootprint

/-! Transport actual guarded reads through existing typed allocation extension.
Heap.Keeps is consumed only where real allocation supplies it; it is not a
preservation assertion for arbitrary mutating callees. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DomainTransport
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Exact old read VALUE survives a genuine heap-keeping extension. -/
theorem probe_keeps {C : Contract} (σ τ : State C (Parameters A)) (e : σ.H <+: τ.H)
 (kept : Heap.Keeps e σ.heap τ.heap) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (oldCounter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (oldAlias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (newCounter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue (n+1) fit)
 (newAlias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) τ.env=some (ref.wk e)) :
 ArrayProbe.value.evalT τ=ArrayProbe.value.evalT σ := by
 rw [HeapDomain.probe_eval τ n fit (ref.wk e) newCounter newAlias,
   HeapDomain.probe_eval σ n fit ref oldCounter oldAlias]
 have inherited := kept.readAddr (.index ref .dyn (countValue n (by omega)))
 change τ.heap.readAddr (.index (ref.wk e) .dyn (countValue n (by omega)))=
   (σ.heap.readAddr (.index ref .dyn (countValue n (by omega)))).map (MVal.wk e (.prim .uint)) at inherited
 rw [inherited]
 cases actual : σ.heap.readAddr (.index ref .dyn (countValue n (by omega))) <;> rfl

/-- A domain fact transports with the exact dependent reference weakening.
The published length law is reused, not reproved or assumed as an oracle. -/
theorem domain_keeps {C : Contract} (σ τ : State C (Parameters A)) (e : σ.H <+: τ.H)
 (kept : Heap.Keeps e σ.heap τ.heap) (count : Nat) (fit : count<W) (ref : HRef σ.H A) :
 ReadDomain σ ref count ↔ ReadDomain τ (ref.wk e) count := by
 rw [HeapDomain.domain_iff σ ref count fit,HeapDomain.domain_iff τ (ref.wk e) count fit,kept.len ref .dyn]

/-- Actual existing allocation discharges Heap.Keeps for every older object. -/
theorem allocation_domain {C : Contract} (σ : State C (Parameters A)) {R : RefTy} (object : MObj σ.H R)
 (count : Nat) (fit : count<W) (ref : HRef σ.H A) :
 ReadDomain σ ref count ↔ ReadDomain (σ.alloc object).1 (ref.wk (List.prefix_append σ.H [R])) count :=
 domain_keeps σ (σ.alloc object).1 (List.prefix_append σ.H [R]) (Heap.keeps_alloc σ.heap object) count fit ref

def scopedNew {C : Contract} (p : PrimTy) (n : Simple C (Parameters A) .uint) :
 Stmt C (Parameters A) (Parameters A) :=
 .block (.cons (.declMem (.array (.prim p)) (.user "private") (some (.newArr n rfl)) rfl rfl) .nil)

/-- The fresh private local is actually dropped; heap growth remains. -/
theorem scoped_source {C : Contract} (σ : State C (Parameters A)) (p : PrimTy)
 (n : Simple C (Parameters A) .uint) (size : Fin W) (value : n.evalT σ=indexValue size) :
 (scopedNew p n).run σ=.ok ⟨(σ.alloc (defaultArray p size)).1,List.prefix_append _ _⟩ := by
 have declared := newArray_decl σ p n size value
 change TRun.block (.push .refl)
   (TRun.seq (TRun.declMem (.array (.prim p)) (some (.newArr n rfl)) rfl) TRun.nil) σ=_
 simp only [TRun.block,TRun.seq,declared,TRun.nil,Except.map]
 rfl

namespace Checks
open CountdownWitness
abbrev F := CountdownWitness.F
abbrev input := AllocatorReturn.Checks.input
def size : Fin W := ⟨3,by decide⟩
def lengthExpr : Simple P.C (Parameters GuardedRecursion.A) .uint := .lit 3 (by decide)
def object : MObj callee.H (.array (.prim .bool)) := defaultArray .bool size
def after := (callee.alloc object).1
def extension : callee.H <+: after.H := List.prefix_append _ _
def reference := P.r0.wk extension
def addresses := upd P.base callee.H.length (⟨22,by decide⟩ : Fin W)
def target := writeMachine (allocateMachine input (⟨22,by decide⟩ : Fin W) size) 4 w[22]

def program : Prog P.C (Parameters GuardedRecursion.A) (Parameters GuardedRecursion.A) :=
 .cons (scopedNew .bool lengthExpr) (.cons GuardedRecursion.probe .nil)

theorem kept : Heap.Keeps extension callee.heap after.heap := Heap.keeps_alloc callee.heap object

theorem read_preserved : ArrayProbe.value.evalT after=.ok (P.uint 9 (by decide)) :=
 (probe_keeps callee after extension kept 1 (by decide) P.r0 rfl rfl rfl rfl).trans ArrayProbe.Checks.good_evaluated

theorem domain_preserved : ReadDomain after reference 2 :=
 (allocation_domain callee object 2 (by decide) P.r0).1 HeapDomain.Checks.domain_from_heap

theorem allocation_facts :
 run (declareNewCode 2 lengthExpr) input=.ok target 0 ∧
 StateRepr 1 2 16 F after addresses target ∧
 StructAllocatorRepr after.heap addresses 16 (⟨26,by decide⟩ : Fin W) target ∧
 target.stack=input.stack ∧ Footprint.Words 8 16 input target := by
 obtain ⟨source,executed,represented,allocator,stack,words⟩ :=
   Footprint.declare AllocatorReturn.Checks.represented AllocatorReturn.Checks.ownership (by decide)
     .bool lengthExpr rfl size rfl (by decide) (lo:=8) (by decide) (by decide)
 have dropped := represented.drop (.push .refl)
 exact ⟨executed,dropped,allocator,stack,words⟩

theorem source_program : program.run callee=.ok ⟨after,extension⟩ := by
 have allocated := scoped_source callee .bool lengthExpr size rfl
 have probed := probe_success after _ read_preserved
 change TRun.seq (scopedNew .bool lengthExpr).runR (TRun.seq GuardedRecursion.probe.runR TRun.nil) callee=_
 change (scopedNew .bool lengthExpr).runR callee=.ok ⟨after,extension⟩ at allocated
 change GuardedRecursion.probe.runR after=.ok ⟨after,List.prefix_refl _⟩ at probed
 simp only [TRun.seq,allocated,probed,TRun.nil,Except.map]

theorem target_program : run (declareNewCode 2 lengthExpr ++ ArrayProbe.code (C:=P.C) 2 F) input=.ok target 0 :=
 (run_append_ok allocation_facts.1).trans (ArrayProbe.success allocation_facts.2.1 _ read_preserved)

theorem read_target : run (ArrayProbe.selected (C:=P.C) 2 F).code target=.ok (target.push w[9]) 0 :=
 ArrayProbe.read_success allocation_facts.2.1 _ _ read_preserved (ReprV.uint_of rfl)

theorem observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 4,target.mem 8,target.mem 9,
 target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21,target.mem 22,target.mem 23,target.mem 24,target.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[2],w[22],w[10],w[99],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 with_unfolding_all rfl

theorem wrong_cursor : target.mem 0≠w[25] := by
 have actual : target.mem 0=w[26] := by rfl
 rw [actual]
 decide

theorem wrong_read : run (ArrayProbe.selected (C:=P.C) 2 F).code target≠.ok (target.push w[7]) 0 := by
 rw [read_target]
 intro bad
 have stacks := congrArg Machine.stack (Evm.Out.ok.inj bad).1
 have mismatch : w[9]=w[7] := (List.cons.inj stacks).1
 have different : w[9]≠w[7] := by decide
 exact different mismatch

theorem identities : reference.id=0 ∧ (callee.alloc object).2.id=2 ∧ after.H.length=3 := by
 exact ⟨rfl,rfl,rfl⟩

theorem no_private_escape : target.mem 2=w[16] ∧ target.mem 4=w[22] ∧ target.mem 2≠target.mem 4 := by
 have old : target.mem 2=w[16] := by rfl
 have fresh : target.mem 4=w[22] := by rfl
 refine ⟨old,fresh,?_⟩
 rw [old,fresh]
 decide

/-- Actual write through the retained old reference: existence of reads is
weaker than preservation of their values. No withinM guard is weakened. -/
def changed := after.withHeap (after.heap.set reference (MObj.setElem .dyn (after.heap.get reference) 1 (P.uint 99 (by decide))))
def changedTarget := writeMachine target 18 w[99]

theorem changed_facts :
 after.heap.writeAddr (.index reference .dyn (countValue 1 (by decide))) (P.uint 99 (by decide))=some changed.heap ∧
 run (writeArrayCode (addresses reference.id)) ((target.push w[99]).push w[1])=.ok changedTarget 0 ∧
 StateRepr 1 2 16 F changed addresses changedTarget := by
 have length : after.heap.len reference .dyn=2 := (kept.len P.r0 .dyn).trans HeapDomain.Checks.length_zero
 have facts := Footprint.array_write allocation_facts.2.1 reference (⟨1,by decide⟩ : Fin W)
   (by change 1<after.heap.len reference .dyn;rw [length];decide) (P.uint 99 (by decide)) w[99] (ReprV.uint_of rfl) 8
 exact ⟨facts.1,facts.2.1,facts.2.2.1⟩

set_option backward.isDefEq.respectTransparency false in
theorem changed_read : ArrayProbe.value.evalT changed=.ok (P.uint 99 (by decide)) := by
 have read := Heap.readAddr_writeAddr_same changed_facts.1
 rw [HeapDomain.probe_eval changed 1 (by decide) reference rfl rfl,read]
 rfl

set_option backward.isDefEq.respectTransparency false in
theorem changed_domain : ReadDomain changed reference 2 := by
 rw [HeapDomain.domain_iff changed reference 2 (by decide),Heap.len_writeAddr changed_facts.1 reference .dyn]
 exact (HeapDomain.domain_iff after reference 2 (by decide)).1 domain_preserved

theorem changed_target_read : run (ArrayProbe.selected (C:=P.C) 2 F).code changedTarget=.ok (changedTarget.push w[99]) 0 :=
 ArrayProbe.read_success changed_facts.2.2 _ _ changed_read (ReprV.uint_of rfl)

theorem mutation_not_keeps : ¬Heap.Keeps (List.prefix_refl after.H) after.heap changed.heap := by
 intro impossible
 have same := probe_keeps after changed (List.prefix_refl after.H) impossible 1 (by decide) reference rfl rfl rfl rfl
 rw [read_preserved,changed_read] at same
 have value := congrArg Subtype.val (Except.ok.inj same)
 change (99:Int)=9 at value
 omega

/-- The reached allocator has the actual three elements plus one header. -/
theorem allocation_growth : GrowsAllocator 2 16 4 callee P.base input after addresses target := by
 intro cursor positive allocator space
 have cell := allocator.arrays.free.cell
 have initialCell : input.mem 0=w[22] := by rfl
 have same : cursor=(⟨22,by decide⟩ : Fin W) := Word.val.inj (cell.symm.trans initialCell)
 subst cursor
 exact allocation_facts.2.2.1

theorem base_extension : BaseExtends callee.H P.base addresses := by
 intro R r
 rcases r with ⟨id,typed⟩
 cases id with
 | zero => rfl
 | succ id => cases id with
   | zero => rfl
   | succ id => cases typed

theorem growing_endpoint : GrowingResult 1 2 16 4 F callee P.base input
 (program.run callee) (run (declareNewCode 2 lengthExpr ++ ArrayProbe.code (C:=P.C) 2 F) input) :=
 .inl ⟨⟨after,extension⟩,target,addresses,source_program,target_program,allocation_facts.2.1,
   allocation_facts.2.2.2.1,base_extension,allocation_growth⟩

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.DomainTransport

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DomainTransport.probe_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DomainTransport.probe_keeps
