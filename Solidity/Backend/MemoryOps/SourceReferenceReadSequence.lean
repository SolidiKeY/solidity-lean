import Solidity.Backend.MemoryOps.SourceReferenceRead
import Solidity.Backend.MemoryOps.SourceReferenceSequence

/-! Computed INITIAL parent-element replacement, then deletion through the
ACTUAL reached pointer. The selected footprint is an initial local sufficient
condition; it is neither global address injection nor a Source exclusion. -/
namespace Solidity.Backend.MemoryOps

def referenceReadStmt {C : Contract} {Γ : Ctx}
    (dst src : Idx Γ (.mem BoolRefsRef)) (i j : Idx Γ (.val .uint)) : Stmt C Γ Γ :=
  .assignMem (.index .dyn (.var dst rfl) (.simple (.local i)))
    (.ref (.loc (.index .dyn (.var src rfl) (.simple (.local j)))))

/-- Both reached executions and their composition are derived from INITIAL
observers, alignments and bounds. The child is computed from src[j], not a
separately supplied child/RHS local or desired reached relation. -/
theorem SourceBoolRefsAt.computed_reference_delete_sequence
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (dst src : HRef σ.H BoolRefsRef) (da sa : Nat) (address : Nat → Nat)
    (hd : SourceBoolRefsAt y da σ.heap dst address) (hs : SourceBoolRefsAt y sa σ.heap src address)
    (droot sroot : Source.Idx Γ SourceBoolRefsTy) (sdi ssi sci : Source.Idx Γ (.int .u256))
    (dl sl : Idx Δ (.mem BoolRefsRef)) (di si ci : Idx Δ (.val .uint)) (i j k : Fin Evm.W)
    (hdr : y.1.get droot=.memRef rfl da) (hsr : y.1.get sroot=.memRef rfl sa)
    (hdi : y.1.get sdi=sourceUint (Evm.Memory.indexValue i))
    (hsi : y.1.get ssi=sourceUint (Evm.Memory.indexValue j))
    (hci : y.1.get sci=sourceUint (Evm.Memory.indexValue k))
    (htd : TEnv.get dl σ.env=some dst) (hts : TEnv.get sl σ.env=some src)
    (hti : TEnv.get di σ.env=Evm.Memory.indexValue i)
    (htj : TEnv.get si σ.env=Evm.Memory.indexValue j)
    (htk : TEnv.get ci σ.env=Evm.Memory.indexValue k)
    (hi : i.val<σ.heap.len dst .dyn) (hj : j.val<σ.heap.len src .dyn)
    (hk : k.val<σ.heap.len ((MObj.elems .dyn (σ.heap.get src))[j.val]'hj) .dyn)
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get dst),
      t.id≠((MObj.elems .dyn (σ.heap.get src))[j.val]'hj).id →
      address t.id≠address ((MObj.elems .dyn (σ.heap.get src))[j.val]'hj).id)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index dst .dyn (Evm.Memory.indexValue i)) child=some mid ∧
      mid.index dst .dyn (Evm.Memory.indexValue i)=some child ∧
      mid.writeAddr (.index child .dyn (Evm.Memory.indexValue k)) false=some out ∧
      (Source.execS G Fs (fuel+6) Γ.length none
        (.expr (sourceReferenceReadAssign droot sroot sdi ssi) : Source.RStmt E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fs (fuel+5) Γ.length none
        (.expr (sourceNestedDelete droot sdi sci) : Source.RStmt E [] false .body Γ Γ)
        ym.1).run (.nil,ym.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fs (fuel+7) Γ.length none
        (.stmt (.expr (sourceReferenceReadAssign droot sroot sdi ssi))
          (.stmt (.expr (sourceNestedDelete droot sdi sci)) .nil) : Source.RItems E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (referenceReadStmt dl sl di si) (.cons (nestedDeleteStmt dl di ci) .nil))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (referenceReadWriteCode (C := C) b dl sl di si) m=.ok mm 0 ∧
      Evm.run (nestedDeleteCode (C := C) b dl di ci) mm=.ok target 0 ∧
      Evm.run (referenceReadWriteCode (C := C) b dl sl di si ++ nestedDeleteCode (C := C) b dl di ci) m=.ok target 0 ∧
      SourceBoolRefsAt ym da mid dst address ∧ SourceBoolRefsAt z da out dst address ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base target ∧
      ym.1=y.1 ∧ z.1=y.1 ∧
      MObj.elems .dyn (out.get dst)=(MObj.elems .dyn (σ.heap.get dst)).set i.val child ∧
      MObj.elems .dyn (out.get child)=(MObj.elems .dyn (σ.heap.get child)).set k.val false ∧
      (∀ q : HRef σ.H (.array (.prim .bool)), q.id≠child.id → out.get q=σ.heap.get q) ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fs (fuel+3)
        (.mem (τ := .bool) (address child.id) k.val) (.bool false)).run ym=(.ok (),z) ∧
      (∀ a,a≠da → a≠address child.id → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.heap.next=y.2.heap.next ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
      target.stack=m.stack ∧
      (∀ cursor,0<b → Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m →
        (base dst.id).val+1+σ.heap.len dst .dyn≤cursor.val →
        Evm.Memory.StructAllocatorRepr out base frame cursor target) ∧
      mm=Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id)) ∧
      target=Evm.Memory.writeMachine mm ((base child.id).val+1+k.val) (.val (Evm.bword false)) ∧
      (∀ a,a≠da → ym.2.heap.get a=y.2.heap.get a) := by
  first
  | solve | rfl | simp only [referenceReadStmt] | omega
  | let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    obtain ⟨mid,ym,hit,hchild,hw₁,read,expr,stmt,hi₁,code₁,hr₁,mok₁,hm₁,locals,elems,children,sourceChildren,other,addrs,next,effects,alloc₁⟩ :=
      hd.computed_reference_assign_word G Fs (fuel+1) Γ.length y σ dst src da sa address hs
        droot sroot sdi ssi dl sl di si i j hdr hsr hdi hsi htd hts hti htj hi hj SH memOK hm
    let mm := Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id))
    have selected : mid.index dst .dyn (Evm.Memory.indexValue i)=some child := by
      change (MObj.elems .dyn (mid.get dst))[(Evm.Memory.indexValue i).1.toNat]?=some child
      rw [elems]
      simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using List.getElem?_set_self hi (a := child)
    have capacity : k.val<mid.len child .dyn := by
      change k.val<(MObj.elems .dyn (mid.get child)).length
      rw [children child]
      exact hk
    have sep : ∀ t∈MObj.elems .dyn (mid.get dst),t.id≠child.id → address t.id≠address child.id := by
      rw [elems]
      intro t ht hn
      rcases List.mem_or_eq_of_mem_set ht with ht | ht
      · exact hsep t ht hn
      · subst t;exact (hn rfl).elim
    obtain ⟨out,z,hw₂,write₂,expr₂,stmt₂,hi₂,code₂,hr₂,mok₂,hm₂,locals₂,parent₂,alloc₂⟩ :=
      SourceBoolRefsAt.resolved_nested_delete_word G Fs fuel droot sdi sci (σ.withHeap mid) dl di ci dst child i k address hr₁
        (by rw [locals];exact hdr) (by rw [locals];exact hdi) (by rw [locals];exact hci)
        htd hti htk selected capacity sep SH mok₁ hm₁
    let target := Evm.Memory.writeMachine mm ((base child.id).val+1+k.val) (.val (Evm.bword false))
    have firstStmt : (Source.execS G Fs (fuel+6) Γ.length none
        (.expr (sourceReferenceReadAssign droot sroot sdi ssi) : Source.RStmt E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal ym.1),(.nil,ym.2)) := by rw [locals];exact stmt
    have atChild : SourceBoolMemoryAt ym (address child.id) mid child .dyn := sourceChildren child hchild
    obtain ⟨ht,known⟩ := source_bool_write ym (address child.id) (MObj.elems .dyn (mid.get child)) atChild k.val capacity false
    have reached : z=(ym.1,{ym.2 with heap := (ym.2.heap.write (address child.id) (sourceBoolMemory ((MObj.elems .dyn (mid.get child)).set k.val false)) ht)}) :=
      congrArg Prod.snd (write₂.symm.trans known)
    refine ⟨mid,out,ym,z,mm,target,hw₁,selected,hw₂,firstStmt,stmt₂,?_,?_,code₁,code₂,?_,
      hr₁,hr₂,mok₁,mok₂,hm₁,hm₂,locals,locals₂.trans locals,?_,?_,?_,write₂,?_,?_,?_,rfl,?_,rfl,rfl,addrs⟩
    · exact source_items_pair_run G Fs (fuel+1) Γ.length _ _ y ym z firstStmt stmt₂
    · exact intrinsic_heap_pair_run σ _ _ mid out hi₁ hi₂
    · rw [Evm.run_append_ok code₁];exact code₂
    · rw [parent₂];exact elems
    · rw [indexedWrite_elems mid out child .dyn (Evm.Memory.indexValue k) false hw₂,children child]
      rfl
    · intro q hn
      rw [indexedWrite_frame mid out child .dyn (Evm.Memory.indexValue k) false hw₂ q (Ne.symm hn),children q]
    · intro a hda hchild
      rw [reached,Source.Heap.write_other ym.2.heap hchild _ ht]
      exact addrs a hda
    · rw [reached]
      exact next
    · rw [reached]
      exact effects
    · intro cursor hb ha live
      exact alloc₂ cursor hb (alloc₁ cursor ha live)

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_reference_delete_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.computed_reference_delete_sequence
end Solidity.Backend.MemoryOps
