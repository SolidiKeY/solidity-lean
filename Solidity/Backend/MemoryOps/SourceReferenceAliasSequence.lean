import Solidity.Backend.MemoryOps.SourceReferenceReadSequence
import Solidity.Backend.MemoryOps.SourceNestedSelect

/-! Computed parent-element replacement followed by local alias selection from
its ACTUAL reached slot. Existing Source/native/word operations only; no copy,
allocator, graph model or desired reached-representation premise is introduced. -/
namespace Solidity.Backend.MemoryOps

theorem SourceBoolRefsAt.computed_reference_alias_sequence
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (dst src : HRef σ.H BoolRefsRef) (da sa : Nat) (address : Nat → Nat)
    (hd : SourceBoolRefsAt y da σ.heap dst address) (hs : SourceBoolRefsAt y sa σ.heap src address)
    (droot sroot : Source.Idx Γ SourceBoolRefsTy) (sdi ssi : Source.Idx Γ (.int .u256))
    (salias : Source.Idx Γ (.array .memory .bool none))
    (dl sl : Idx Δ (.mem BoolRefsRef)) (di si : Idx Δ (.val .uint))
    (alias : Idx Δ (.mem (.array (.prim .bool)))) (i j : Fin Evm.W)
    (hdr : y.1.get droot=.memRef rfl da) (hsr : y.1.get sroot=.memRef rfl sa)
    (hdi : y.1.get sdi=sourceUint (Evm.Memory.indexValue i))
    (hsi : y.1.get ssi=sourceUint (Evm.Memory.indexValue j))
    (htd : TEnv.get dl σ.env=some dst) (hts : TEnv.get sl σ.env=some src)
    (hti : TEnv.get di σ.env=Evm.Memory.indexValue i) (htj : TEnv.get si σ.env=Evm.Memory.indexValue j)
    (hi : i.val<σ.heap.len dst .dyn) (hj : j.val<σ.heap.len src .dyn)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ),
    let z : Source.EMState E Γ := (ym.1.set salias (.memRef rfl (address child.id)),ym.2);
    let final := (σ.withHeap mid).setLocal alias (some child);
    let mm := Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id));
    let target := Evm.Memory.writeMachine mm (Evm.cellOf b alias) (.val (base child.id));
      σ.heap.writeAddr (.index dst .dyn (Evm.Memory.indexValue i)) child=some mid ∧
      mid.index dst .dyn (Evm.Memory.indexValue i)=some child ∧
      (Source.execS G Fs (fuel+5) Γ.length none
        (.expr (sourceReferenceReadAssign droot sroot sdi ssi) : Source.RStmt E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE G Fs (fuel+3) (sourceSelectedAlias salias droot sdi)).run ym=
        (.ok (.val (.memRef rfl (address child.id))),z) ∧
      (Source.execS G Fs (fuel+4) Γ.length none
        (.expr (sourceSelectedAlias salias droot sdi) : Source.RStmt E [] false .body Γ Γ)
        ym.1).run (.nil,ym.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fs (fuel+6) Γ.length none
        (.stmt (.expr (sourceReferenceReadAssign droot sroot sdi ssi))
          (.stmt (.expr (sourceSelectedAlias salias droot sdi)) .nil) : Source.RItems E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (referenceReadStmt dl sl di si)=.ok ⟨σ.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (σ.withHeap mid) (.rebindMem alias
        (.alias (.loc (.index .dyn (.var dl rfl) (.simple (.local di))))))=
          .ok ⟨final,List.prefix_refl _⟩ ∧
      Prog.run σ (.cons (referenceReadStmt dl sl di si)
        (.cons (.rebindMem alias (.alias (.loc (.index .dyn (.var dl rfl) (.simple (.local di)))))) .nil))=
          .ok ⟨final,List.prefix_refl _⟩ ∧
      Evm.run (referenceReadWriteCode (C := C) b dl sl di si) m=.ok mm 0 ∧
      Evm.run (selectedAliasCode (C := C) b alias dl di) mm=.ok target 0 ∧
      Evm.run (referenceReadWriteCode (C := C) b dl sl di si ++ selectedAliasCode (C := C) b alias dl di) m=
        .ok target 0 ∧
      SourceBoolRefsAt ym da mid dst address ∧ SourceBoolRefsAt z da final.heap dst address ∧
      SourceBoolMemoryAt z (address child.id) final.heap child .dyn ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.RefArrayStateRepr L b frame F final base target ∧
      ym.1=y.1 ∧ z.1=y.1.set salias (.memRef rfl (address child.id)) ∧
      z.1.get salias=.memRef rfl (address child.id) ∧ TEnv.get alias final.env=some child ∧
      final.heap=mid ∧ z.2=ym.2 ∧
      MObj.elems .dyn (final.heap.get dst)=(MObj.elems .dyn (σ.heap.get dst)).set i.val child ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),final.heap.get q=σ.heap.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt z (address q.id) final.heap q .dyn) ∧
      (∀ a,a≠da → z.2.heap.get a=y.2.heap.get a) ∧ z.2.heap.next=y.2.heap.next ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
      target.stack=m.stack ∧
      (∀ cursor,0<b → Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m →
        (base dst.id).val+1+σ.heap.len dst .dyn≤cursor.val →
        Evm.Memory.StructAllocatorRepr final.heap base frame cursor target) := by
  first
  | solve | rfl | simp only [referenceReadStmt] | omega
  | let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    obtain ⟨mid,ym,hit,hchild,hw,read,expr,stmt,native,word,hr,mok,represented,locals,elems,children,sourceChildren,other,addrs,next,effects,alloc⟩ :=
      hd.computed_reference_assign_word G Fs fuel Γ.length y σ dst src da sa address hs
        droot sroot sdi ssi dl sl di si i j hdr hsr hdi hsi htd hts hti htj hi hj SH memOK hm
    let mm := Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id));
    have selected : mid.index dst .dyn (Evm.Memory.indexValue i)=some child := by
      change (MObj.elems .dyn (mid.get dst))[(Evm.Memory.indexValue i).1.toNat]?=some child
      rw [elems]
      simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using List.getElem?_set_self hi (a := child)
    have second := hr.selected_alias_word G Fs fuel ym salias droot sdi da (Evm.Memory.indexValue i)
      (by rw [locals];exact hdr) (by rw [locals];exact hdi) SH mok
      (σ.withHeap mid) alias dl di dst child htd hti address selected represented rfl
    obtain ⟨expr₂,stmt₂,native₂,word₂,mok₂,child₂,parent₂,sourceAlias,nativeAlias,represented₂,stack₂,alloc₂⟩ := second
    have firstStmt : (Source.execS G Fs (fuel+5) Γ.length none
        (.expr (sourceReferenceReadAssign droot sroot sdi ssi) : Source.RStmt E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal ym.1),(.nil,ym.2)) := by rw [locals];exact stmt
    refine ⟨mid,ym,hw,selected,firstStmt,expr₂,stmt₂,?_,native,native₂,?_,word,word₂,?_,hr,parent₂,child₂,
      mok,mok₂,represented,represented₂,locals,?_,sourceAlias,nativeAlias,rfl,rfl,elems,children,
      sourceChildren,addrs,next,effects,rfl,?_⟩
    · exact source_items_pair_run G Fs fuel Γ.length _ _ y ym _ firstStmt stmt₂
    · simp only [referenceReadStmt]
      rw [Prog.run_cons_ok native,Prog.run_cons_ok native₂,Prog.run_nil]
      rfl
    · rw [Evm.run_append_ok word];exact word₂
    · rw [locals]
    · intro cursor hb ha live
      exact alloc₂ cursor hb (alloc cursor ha live)

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_reference_alias_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.computed_reference_alias_sequence
end Solidity.Backend.MemoryOps
