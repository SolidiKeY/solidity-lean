import Solidity.Backend.MemoryOps.SourceUintMemory
import Solidity.Evm.MemoryAllocSource
import Solidity.Evm.MemoryDelete

/-! Actual published independent Source zero-default construction and existing
intrinsic/word allocators. Supported empty dynamic uint256 array only; no new
allocator, source profile, all-type construction or allocation-failure theorem. -/
namespace Solidity.Backend.MemoryOps

private theorem empty_source_data {D : Source.Layout} :
    Source.Data.array (D := D) (l := .memory) (τ := .int .u256) (n := none) 0
      (fun _ h => nomatch h) Fin.elim0=sourceUintMemory [] := by
  unfold sourceUintMemory
  congr 1
  funext i
  exact Fin.elim0 i

theorem source_uint_default_run {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (fuel : Nat) :
    (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none)).run y=
      (.ok (.memRef rfl y.2.heap.next),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩).1})) := by
  have hz : (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none)).run y=
      (Source.allocRef (E := E) (Γ := Γ) (Source.Data.array (l := .memory) (τ := .int .u256) (n := none)
        0 (fun _ h => nomatch h) Fin.elim0)).run y := by rfl
  rw [empty_source_data] at hz
  exact hz.trans (source_uint_alloc y [])

/-- Compare actual independently executed default builders at their fresh roots.
Initial heaps need not have equal addresses or a global injective address map. -/
theorem source_uint_default_intrinsic {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (fuel : Nat) :
    let g := hp.allocDefault (.array (.prim .uint)) rfl
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none)).run y).2
    SourceUintMemoryAt z y.2.heap.next g.heap g.val .dyn ∧
      Heap.Keeps g.ext hp g.heap ∧ H.length≤g.val.id := by
  dsimp only
  have he : MObj.elems .dyn ((hp.allocDefault (.array (.prim .uint)) rfl).heap.get
      (hp.allocDefault (.array (.prim .uint)) rfl).val)=[] := by
    apply List.length_eq_zero_iff.mp
    exact Heap.allocDefault_array_len hp (.prim .uint) rfl
  refine ⟨?_,SVal.keeps_copyStToM _ rfl hp,SVal.copyStToM_id_ge hp _ rfl⟩
  unfold SourceUintMemoryAt
  rw [source_uint_default_run,he]
  exact Source.Heap.alloc_get _ _

theorem source_uint_default_memOK {E : Source.Env} {Γ : Source.RCtx}
    (SH : Source.HeapTy) (fuel : Nat) :
    Source.Hoare (Source.MemOK E SH)
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none))
      (fun v y => Source.MemOK E SH y ∧ v.RefOK E y.2.heap.ty) (fun _ y => Source.MemOK E SH y) := by
  intro y hy
  have h := source_uint_alloc_memOK (E := E) (Γ := Γ) SH [] y hy
  have he := (source_uint_default_run y fuel).trans (source_uint_alloc y []).symm
  change (match (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none)).run y with
    | (.ok v,z) => Source.MemOK E SH z ∧ v.RefOK E z.2.heap.ty
    | (.error _,z) => Source.MemOK E SH z)
  rw [he]
  exact h

/-- Old represented contents survive BOTH actual builders; new-root logical
identity and Source address separation are derived from existing allocation facts. -/
theorem SourceUintMemoryAt.default_frame {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a) (fuel : Nat) :
    let g := hp.allocDefault (.array (.prim .uint)) rfl
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none)).run y).2
    SourceUintMemoryAt z address g.heap (r.wk g.ext) a ∧
      (r.wk g.ext).id=r.id ∧ g.val.id≠(r.wk g.ext).id ∧ y.2.heap.next≠address := by
  dsimp only
  have h := source_uint_default_intrinsic y hp fuel
  have he : MObj.elems a ((hp.allocDefault (.array (.prim .uint)) rfl).heap.get
      (r.wk (hp.allocDefault (.array (.prim .uint)) rfl).ext))=MObj.elems a (hp.get r) := by
    rw [h.2.1 r,MObj.elems_wk,List.map_id''
      (f := MVal.wk (hp.allocDefault (.array (.prim .uint)) rfl).ext (.prim .uint)) (fun _ => rfl)]
  have ha : address≠y.2.heap.next := by
    intro heq
    have hf := y.2.heap.alloc_fresh ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩
    change y.2.heap.get y.2.heap.next=none at hf
    rw [←heq,hr] at hf
    cases hf
  refine ⟨?_,rfl,?_,Ne.symm ha⟩
  · unfold SourceUintMemoryAt
    rw [source_uint_default_run,he]
    rw [Source.Heap.alloc_other _ _ ha]
    exact hr
  · have hi := r.id_lt
    have hf := h.2.2
    change (hp.allocDefault (.array (.prim .uint)) rfl).val.id≠r.id
    omega

/-- Supported constructor application of the EXISTING word allocator compiler.
Initial allocator/frame/capacity premises stay explicit, never final preservation. -/
theorem source_uint_default_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (y : Source.EMState E Γ) (fuel : Nat) (σ : State C Δ)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let o := Evm.Memory.defaultArray (H := σ.H) .uint ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let r' := (σ.alloc o).2
    let base' := Evm.upd base σ.H.length cursor
    let m' := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cell (b+Δ.length)) (.val cursor)
    ∃ z : Source.EMState E Γ,
      (Source.zeroVal (E := E) (Γ := Γ) (fuel+2) (.array .memory (.int .u256) none)).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
      TRun.declMem (.array (.prim .uint)) none rfl σ=.ok ⟨σ',List.prefix_append _ _⟩ ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok m' 0 ∧
      SourceUintMemoryAt z y.2.heap.next σ'.heap r' .dyn ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem (.array (.prim .uint))) .ok) σ' base' m' ∧
      Evm.Memory.StructAllocatorRepr σ'.heap base' frame ⟨cursor.val+1,hspace⟩ m' ∧
      m'.stack=m.stack ∧ r'.id=σ.H.length := by
  dsimp only
  have ht := Evm.Memory.newArray_correct hm ha hb .uint (.lit 0 rfl) rfl ⟨0,Evm.W_pos⟩ rfl hspace hcap
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory []⟩).1})
  refine ⟨z,source_uint_default_run y fuel,
    (Evm.Memory.defaultArray_eq_allocate σ .uint).trans ht.1,ht.2.1,?_,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2,rfl⟩
  unfold SourceUintMemoryAt
  have he : MObj.elems .dyn ((σ.allocPush (Evm.Memory.defaultArray .uint ⟨0,Evm.W_pos⟩)).heap.get
      (σ.alloc (Evm.Memory.defaultArray .uint ⟨0,Evm.W_pos⟩)).2)=[] := by
    rw [State.allocPush_get,MObj.elems_wk,MObj.elems_dyn]
    simp only [Evm.Memory.defaultArray,List.replicate_zero,List.map_nil]
  rw [he]
  exact Source.Heap.alloc_get _ _

/-- Insufficient existing interpreter fuel has its real timeout result; it
allocates no object, and is not silently removed from the source profile. -/
theorem source_uint_default_lowfuel {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.zeroVal (E := E) (Γ := Γ) 0 (.array .memory (.int .u256) none)).run y=(.error .timeout,y) ∧
    (Source.zeroVal (E := E) (Γ := Γ) 1 (.array .memory (.int .u256) none)).run y=(.error .timeout,y) := by
  exact ⟨rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.source_uint_default_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_default_run
/-- info: 'Solidity.Backend.MemoryOps.source_uint_default_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_default_intrinsic
/-- info: 'Solidity.Backend.MemoryOps.source_uint_default_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_default_memOK
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.default_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.default_frame
/-- info: 'Solidity.Backend.MemoryOps.source_uint_default_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_default_word
/-- info: 'Solidity.Backend.MemoryOps.source_uint_default_lowfuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_default_lowfuel
end Solidity.Backend.MemoryOps
