import Solidity.Backend.MemoryOps.SourceMemory
import Solidity.Evm.MemoryAllocSource
import Solidity.Evm.MemoryDelete

/-! Actual published independent Source zero-default construction and existing
intrinsic/word allocators. Supported empty dynamic Boolean array only; no new
allocator, source profile, all-type construction or allocation-failure theorem. -/
namespace Solidity.Backend.MemoryOps

private theorem empty_source_data {D : Source.Layout} :
    Source.Data.array (D := D) (l := .memory) (τ := .bool) (n := none) 0
      (fun _ h => nomatch h) Fin.elim0=sourceBoolMemory [] := by
  unfold sourceBoolMemory
  congr 1
  funext i
  exact Fin.elim0 i

theorem source_bool_default_run {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (fuel : Nat) :
    (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory .bool none)).run y=
      (.ok (.memRef rfl y.2.heap.next),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory .bool none,sourceBoolMemory []⟩).1})) := by
  have hz : (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory .bool none)).run y=
      (Source.allocRef (E := E) (Γ := Γ) (Source.Data.array (l := .memory) (τ := .bool) (n := none)
        0 (fun _ h => nomatch h) Fin.elim0)).run y := by rfl
  rw [empty_source_data] at hz
  exact hz.trans (source_bool_alloc y [])

/-- Compare actual independently executed default builders at their fresh roots.
Initial heaps need not have equal addresses or a global injective address map. -/
theorem source_bool_default_intrinsic {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (fuel : Nat) :
    let g := hp.allocDefault (.array (.prim .bool)) rfl
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory .bool none)).run y).2
    SourceBoolMemoryAt z y.2.heap.next g.heap g.val .dyn ∧
      Heap.Keeps g.ext hp g.heap ∧ H.length≤g.val.id := by
  dsimp only
  have he : MObj.elems .dyn ((hp.allocDefault (.array (.prim .bool)) rfl).heap.get
      (hp.allocDefault (.array (.prim .bool)) rfl).val)=[] := by
    apply List.length_eq_zero_iff.mp
    exact Heap.allocDefault_array_len hp (.prim .bool) rfl
  refine ⟨?_,SVal.keeps_copyStToM _ rfl hp,SVal.copyStToM_id_ge hp _ rfl⟩
  unfold SourceBoolMemoryAt
  rw [source_bool_default_run,he]
  exact Source.Heap.alloc_get _ _

theorem source_bool_default_memOK {E : Source.Env} {Γ : Source.RCtx}
    (SH : Source.HeapTy) (fuel : Nat) :
    Source.Hoare (Source.MemOK E SH)
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory .bool none))
      (fun v y => Source.MemOK E SH y ∧ v.RefOK E y.2.heap.ty) (fun _ y => Source.MemOK E SH y) := by
  intro y hy
  have h := source_bool_alloc_memOK (E := E) (Γ := Γ) SH [] y hy
  have he := (source_bool_default_run y fuel).trans (source_bool_alloc y []).symm
  change (match (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory .bool none)).run y with
    | (.ok v,z) => Source.MemOK E SH z ∧ v.RefOK E z.2.heap.ty
    | (.error _,z) => Source.MemOK E SH z)
  rw [he]
  exact h

/-- Old represented contents survive BOTH actual builders; new-root logical
identity and Source address separation are derived from existing allocation facts. -/
theorem SourceBoolMemoryAt.default_frame {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a) (fuel : Nat) :
    let g := hp.allocDefault (.array (.prim .bool)) rfl
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory .bool none)).run y).2
    SourceBoolMemoryAt z address g.heap (r.wk g.ext) a ∧
      (r.wk g.ext).id=r.id ∧ g.val.id≠(r.wk g.ext).id ∧ y.2.heap.next≠address := by
  dsimp only
  have h := source_bool_default_intrinsic y hp fuel
  have he : MObj.elems a ((hp.allocDefault (.array (.prim .bool)) rfl).heap.get
      (r.wk (hp.allocDefault (.array (.prim .bool)) rfl).ext))=MObj.elems a (hp.get r) := by
    rw [h.2.1 r,MObj.elems_wk,List.map_id''
      (f := MVal.wk (hp.allocDefault (.array (.prim .bool)) rfl).ext (.prim .bool)) (fun _ => rfl)]
  have ha : address≠y.2.heap.next := by
    intro heq
    have hf := y.2.heap.alloc_fresh ⟨.array .memory .bool none,sourceBoolMemory []⟩
    change y.2.heap.get y.2.heap.next=none at hf
    rw [←heq,hr] at hf
    cases hf
  refine ⟨?_,rfl,?_,Ne.symm ha⟩
  · unfold SourceBoolMemoryAt
    rw [source_bool_default_run,he]
    rw [Source.Heap.alloc_other _ _ ha]
    exact hr
  · have hi := r.id_lt
    have hf := h.2.2
    change (hp.allocDefault (.array (.prim .bool)) rfl).val.id≠r.id
    omega

/-- Supported constructor application of the EXISTING word allocator compiler.
Initial allocator/frame/capacity premises stay explicit, never final preservation. -/
theorem source_bool_default_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (y : Source.EMState E Γ) (fuel : Nat) (σ : State C Δ)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let o := Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let r' := (σ.alloc o).2
    let base' := Evm.upd base σ.H.length cursor
    let m' := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cell (b+Δ.length)) (.val cursor)
    ∃ z : Source.EMState E Γ,
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory .bool none)).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
      TRun.declMem (.array (.prim .bool)) none rfl σ=.ok ⟨σ',List.prefix_append _ _⟩ ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok m' 0 ∧
      SourceBoolMemoryAt z y.2.heap.next σ'.heap r' .dyn ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem (.array (.prim .bool))) .ok) σ' base' m' ∧
      Evm.Memory.StructAllocatorRepr σ'.heap base' frame ⟨cursor.val+1,hspace⟩ m' ∧
      m'.stack=m.stack ∧ r'.id=σ.H.length := by
  dsimp only
  have ht := Evm.Memory.newArray_correct hm ha hb .bool (.lit 0 rfl) rfl ⟨0,Evm.W_pos⟩ rfl hspace hcap
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory .bool none,sourceBoolMemory []⟩).1})
  refine ⟨z,source_bool_default_run y fuel,
    (Evm.Memory.defaultArray_eq_allocate σ .bool).trans ht.1,ht.2.1,?_,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2,rfl⟩
  unfold SourceBoolMemoryAt
  have he : MObj.elems .dyn ((σ.allocPush (Evm.Memory.defaultArray .bool ⟨0,Evm.W_pos⟩)).heap.get
      (σ.alloc (Evm.Memory.defaultArray .bool ⟨0,Evm.W_pos⟩)).2)=[] := by
    rw [State.allocPush_get,MObj.elems_wk,MObj.elems_dyn]
    simp only [Evm.Memory.defaultArray,List.replicate_zero,List.map_nil]
  rw [he]
  exact Source.Heap.alloc_get _ _

/-- Insufficient existing interpreter fuel has its real timeout result; it
allocates no object, and is not silently removed from the source profile. -/
theorem source_bool_default_lowfuel {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.zeroVal (E := E) (Γ := Γ) 0 (.array .memory .bool none)).run y=(.error .timeout,y) ∧
    (Source.zeroVal (E := E) (Γ := Γ) 1 (.array .memory .bool none)).run y=(.error .timeout,y) := by
  exact ⟨rfl,rfl⟩

/-- A negative boundary of the published unchecked word allocator: without
its space premise the cursor wraps. This is not a checked failure theorem. -/
theorem word_empty_allocator_wrap (m : Evm.Machine) (cursor : Fin Evm.W)
    (hc : m.mem 0=.val cursor) (hw : cursor.val+1=Evm.W) :
    Evm.run Evm.Memory.allocateArrayCode (m.push (.val ⟨0,Evm.W_pos⟩))=
      .ok ((Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩).push (.val cursor)) 0 ∧
    (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩).mem 0=Evm.Word.val ⟨0,Evm.W_pos⟩ ∧
    ∀ frame,0<frame → ¬Evm.Memory.FreeMemory frame ⟨0,Evm.W_pos⟩
      (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩) := by
  refine ⟨Evm.Memory.allocateArray_run m cursor ⟨0,Evm.W_pos⟩ hc,?_,?_⟩
  · simp only [Evm.Memory.allocateMachine,Evm.Memory.writeMachine,Evm.upd_same]
    have he : cursor.val+0+1=Evm.W := by omega
    rw [he]
    apply congrArg Evm.Word.val
    apply Fin.ext
    exact Nat.mod_self _
  · intro frame hf hfree
    have hh := hfree.above
    change frame≤0 at hh
    omega

/-- info: 'Solidity.Backend.MemoryOps.source_bool_default_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_default_run
/-- info: 'Solidity.Backend.MemoryOps.source_bool_default_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_default_intrinsic
/-- info: 'Solidity.Backend.MemoryOps.source_bool_default_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_default_memOK
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.default_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.default_frame
/-- info: 'Solidity.Backend.MemoryOps.source_bool_default_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_default_word
/-- info: 'Solidity.Backend.MemoryOps.source_bool_default_lowfuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_default_lowfuel
/-- info: 'Solidity.Backend.MemoryOps.word_empty_allocator_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms word_empty_allocator_wrap
end Solidity.Backend.MemoryOps
