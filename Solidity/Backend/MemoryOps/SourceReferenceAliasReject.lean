import Solidity.Backend.MemoryOps.SourceReferenceAliasDelete

/-! Late bounds rejection after actual computed replacement AND local rebinding.
The failed suffix has no target machine result; prefix states are explicit. -/
namespace Solidity.Backend.MemoryOps

theorem SourceBoolRefsAt.computed_alias_delete_reject
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (dst src : HRef σ.H BoolRefsRef) (da sa : Nat) (address : Nat → Nat)
    (hd : SourceBoolRefsAt y da σ.heap dst address) (hs : SourceBoolRefsAt y sa σ.heap src address)
    (droot sroot : Source.Idx Γ SourceBoolRefsTy) (sdi ssi ski : Source.Idx Γ (.int .u256))
    (salias : Source.Idx Γ (.array .memory .bool none))
    (dl sl : Idx Δ (.mem BoolRefsRef)) (di si ki : Idx Δ (.val .uint))
    (alias : Idx Δ (.mem (.array (.prim .bool)))) (i j k : Fin Evm.W)
    (hdr : y.1.get droot=.memRef rfl da) (hsr : y.1.get sroot=.memRef rfl sa)
    (hdi : y.1.get sdi=sourceUint (Evm.Memory.indexValue i))
    (hsi : y.1.get ssi=sourceUint (Evm.Memory.indexValue j))
    (hki : y.1.get ski=sourceUint (Evm.Memory.indexValue k))
    (htd : TEnv.get dl σ.env=some dst) (hts : TEnv.get sl σ.env=some src)
    (hti : TEnv.get di σ.env=Evm.Memory.indexValue i) (htj : TEnv.get si σ.env=Evm.Memory.indexValue j)
    (htk : TEnv.get ki σ.env=Evm.Memory.indexValue k)
    (hi : i.val<σ.heap.len dst .dyn) (hj : j.val<σ.heap.len src .dyn)
    (hk : σ.heap.len ((MObj.elems .dyn (σ.heap.get src))[j.val]'hj) .dyn≤k.val)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ),
    let ya : Source.EMState E Γ := (ym.1.set salias (.memRef rfl (address child.id)),ym.2);
    let τ := (σ.withHeap mid).setLocal alias (some child);
    let mp := Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id));
    let ma := Evm.Memory.writeMachine mp (Evm.cellOf b alias) (.val (base child.id));
      σ.heap.writeAddr (.index dst .dyn (Evm.Memory.indexValue i)) child=some mid ∧
      mid.index dst .dyn (Evm.Memory.indexValue i)=some child ∧
      (Source.execS G Fs (fuel+6) Γ.length none
        (.expr (sourceReferenceReadAssign droot sroot sdi ssi) : Source.RStmt E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fs (fuel+5) Γ.length none
        (.expr (sourceSelectedAlias salias droot sdi) : Source.RStmt E [] false .body Γ Γ)
        ym.1).run (.nil,ym.2)=(.ok (.normal ya.1),(.nil,ya.2)) ∧
      (Source.evalE G Fs (fuel+3) (sourceIndexedDelete salias ski)).run ya=
        (.error (.revert (Source.panicData .index)),ya) ∧
      (Source.execS G Fs (fuel+4) Γ.length none
        (.expr (sourceIndexedDelete salias ski) : Source.RStmt E [] false .body Γ Γ)
        ya.1).run (.nil,ya.2)=(.error (.revert (Source.panicData .index)),(.nil,ya.2)) ∧
      (Source.execItems G Fs (fuel+7) Γ.length none
        (.stmt (.expr (sourceReferenceReadAssign droot sroot sdi ssi))
          (.stmt (.expr (sourceSelectedAlias salias droot sdi))
            (.stmt (.expr (sourceIndexedDelete salias ski)) .nil)) : Source.RItems E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.error (.revert (Source.panicData .index)),(.nil,ya.2)) ∧
      Prog.run σ (.cons (referenceReadStmt dl sl di si)
        (.cons (.rebindMem alias (.alias (.loc (.index .dyn (.var dl rfl) (.simple (.local di)))))) .nil))=
          .ok ⟨τ,List.prefix_refl _⟩ ∧
      Stmt.run τ (.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) rfl)=.error .revert ∧
      Prog.run σ (.cons (referenceReadStmt dl sl di si)
        (.cons (.rebindMem alias (.alias (.loc (.index .dyn (.var dl rfl) (.simple (.local di))))))
          (.cons (.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) rfl) .nil)))=.error .revert ∧
      Evm.run (referenceReadWriteCode (C := C) b dl sl di si) m=.ok mp 0 ∧
      Evm.run (selectedAliasCode (C := C) b alias dl di) mp=.ok ma 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b alias (Evm.compileVal b (.simple (.local ki) : Val C Δ .uint))) ma=.revert ∧
      Evm.run ((referenceReadWriteCode (C := C) b dl sl di si ++ selectedAliasCode (C := C) b alias dl di) ++
        Evm.Memory.deleteLocalCode b alias (Evm.compileVal b (.simple (.local ki) : Val C Δ .uint))) m=.revert ∧
      SourceBoolRefsAt ya da mid dst address ∧ SourceBoolMemoryAt ya (address child.id) mid child .dyn ∧
      Source.MemOK E SH ya ∧ Evm.Memory.RefArrayStateRepr L b frame F τ base ma ∧
      ym.1=y.1 ∧ ya.1=y.1.set salias (.memRef rfl (address child.id)) ∧
      ya.1.get salias=.memRef rfl (address child.id) ∧ TEnv.get alias τ.env=some child ∧
      MObj.elems .dyn (mid.get dst)=(MObj.elems .dyn (σ.heap.get dst)).set i.val child ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),mid.get q=σ.heap.get q) ∧
      (∀ a,a≠da → ya.2.heap.get a=y.2.heap.get a) ∧ ya.2.heap.next=y.2.heap.next ∧
      (ya.2.ex=y.2.ex ∧ ya.2.events=y.2.events ∧ ya.2.logs=y.2.logs ∧ ya.2.fnLocals=y.2.fnLocals) ∧
      ma.stack=m.stack ∧
      (∀ cursor,0<b → Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m →
        (base dst.id).val+1+σ.heap.len dst .dyn≤cursor.val →
        Evm.Memory.StructAllocatorRepr mid base frame cursor ma) := by
  first
  | solve | rfl | simp only [referenceReadStmt] | omega
  | let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    obtain ⟨mid,ym,hw,selected,stmt₁,expr₂,stmt₂,prefixItems,native₁,native₂,prefixNative,word₁,word₂,prefixWord,
      hr₁,hr₂,child₂,mok₁,mok₂,repr₁,repr₂,locals₁,locals₂,sourceAlias,nativeAlias,heap,globals,parentElems,
      children,sourceChildren,addrs,next,effects,stack,alloc⟩ :=
      hd.computed_reference_alias_sequence G Fs (fuel+1) y σ dst src da sa address hs droot sroot sdi ssi salias
        dl sl di si alias i j hdr hsr hdi hsi htd hts hti htj hi hj SH memOK hm
    let ya : Source.EMState E Γ := (ym.1.set salias (.memRef rfl (address child.id)),ym.2)
    let τ := (σ.withHeap mid).setLocal alias (some child)
    have hscalar : ya.1.get ski=sourceUint (Evm.Memory.indexValue k) := by
      change (ym.1.set salias (.memRef rfl (address child.id))).get ski=_
      rw [source_bool_alias_uint_frame,locals₁]
      exact hki
    have hne : alias.toNat≠ki.toNat := by
      intro h
      have ht := alias.getElem?_toNat
      rw [h,ki.getElem?_toNat] at ht
      cases ht
    have tscalar : TEnv.get ki τ.env=Evm.Memory.indexValue k :=
      (TEnv.get_set_ne alias ki (some child) (σ.withHeap mid).env hne).trans htk
    change ∀ q : HRef σ.H (.array (.prim .bool)),mid.get q=σ.heap.get q at children
    have bound : τ.heap.len child .dyn≤(Evm.Memory.indexValue k).1.toNat := by
      change (MObj.elems .dyn (mid.get child)).length≤(Evm.Memory.indexValue k).1.toNat
      rw [children child]
      simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hk
    obtain ⟨expr₃,word₃⟩ := resolved_delete_word_bounds G Fs fuel τ child child₂ salias ski alias ki
      (Evm.Memory.indexValue k) sourceAlias hscalar nativeAlias tscalar bound repr₂.state
    have stmt₃ := source_expr_statement_error G Fs (fuel+3) Γ.length _ ya ya _ expr₃
    have noWrite := (child₂.delete_bounds Fs fuel (Evm.Memory.indexValue k) bound).2
    change τ.heap.writeAddr (.index child .dyn (Evm.Memory.indexValue k)) (PrimTy.dflt .bool)=none at noWrite
    have talias : TEnv.get alias τ.env=some child := nativeAlias
    have native₃ : Stmt.run τ (.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) rfl)=.error .revert := by
      change TRun.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) τ=_
      simp only [TRun.deleteMem,TRun.clearT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,talias,tscalar,
        noWrite,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have tail := source_items_pair_error G Fs fuel Γ.length
      (.expr (sourceSelectedAlias salias droot sdi)) (.expr (sourceIndexedDelete salias ski)) ym ya ya _ stmt₂ stmt₃
    have items : (Source.execItems G Fs (fuel+7) Γ.length none
        (.stmt (.expr (sourceReferenceReadAssign droot sroot sdi ssi))
          (.stmt (.expr (sourceSelectedAlias salias droot sdi))
            (.stmt (.expr (sourceIndexedDelete salias ski)) .nil)) : Source.RItems E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.error (.revert (Source.panicData .index)),(.nil,ya.2)) := by
      rw [Source.execItems,Source.Hoare.run_bind,stmt₁]
      change (Source.execItems G Fs (fuel+6) Γ.length none
        (.stmt (.expr (sourceSelectedAlias salias droot sdi))
          (.stmt (.expr (sourceIndexedDelete salias ski)) .nil) : Source.RItems E [] false .body Γ Γ)
        ym.1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,ym.2)=_
      rw [Source.Hoare.run_bind,tail]
    refine ⟨mid,ym,hw,selected,stmt₁,stmt₂,expr₃,stmt₃,items,prefixNative,native₃,?_,word₁,word₂,word₃,?_,
      hr₂,child₂,mok₂,repr₂,locals₁,locals₂,sourceAlias,nativeAlias,parentElems,children,addrs,next,effects,stack,alloc⟩
    · have stop : Prog.run τ (.cons (.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) rfl) .nil)=.error .revert := by
        change TRun.seq _ _ τ=_
        simp only [TRun.seq]
        rw [show TRun.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) τ=.error .revert from native₃]
      rw [Prog.run_cons_ok native₁,Prog.run_cons_ok native₂,stop]
      rfl
    · rw [Evm.run_append_ok prefixWord];exact word₃

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_alias_delete_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.computed_alias_delete_reject
end Solidity.Backend.MemoryOps
