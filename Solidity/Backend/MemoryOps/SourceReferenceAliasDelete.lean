import Solidity.Backend.MemoryOps.SourceReferenceAliasSequence
import Solidity.Backend.MemoryOps.SourceIndexedDelete
import Solidity.Backend.MemoryOps.SourceCalldataBinding

/-! Actual computed reference replacement, local selection and delete through
that reached local. Existing Source, intrinsic and word operations only. -/
namespace Solidity.Backend.MemoryOps

/-- Intrinsic Source type separation frames scalar operands when a Boolean
array reference local is rebound. No positional/address-injection premise. -/
theorem source_bool_alias_uint_frame {D : Source.Layout} : {Γ : Source.RCtx} →
    (l : Source.Locals D Γ) → (dst : Source.Idx Γ (.array .memory .bool none)) →
    (idx : Source.Idx Γ (.int .u256)) → (v : Source.Val D (.array .memory .bool none)) →
      (l.set dst v).get idx=l.get idx
  | _,.cons _ l,.here,.there _,_ => rfl
  | _,.cons _ l,.there _,.here,_ => rfl
  | _,.cons _ l,.there dst,.there idx,v => source_bool_alias_uint_frame l dst idx v

/-- Bridge the published local/default/index code to the actual primitive clear
certificate; it does not define a pointer compiler or memory operation. -/
private theorem delete_local_of_clear {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Evm.Frag Γ}
    {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m)
    (root : Idx Γ (.mem (.array (.prim .bool)))) (idx : Idx Γ (.val .uint))
    (q : HRef σ.H (.array (.prim .bool))) (k : Fin Evm.W)
    (hroot : TEnv.get root σ.env=some q) (hindex : TEnv.get idx σ.env=Evm.Memory.indexValue k)
    {out : Evm.Out}
    (clear : Evm.run (Evm.Memory.writeArrayCode (base q.id)) ((m.push (.val (Evm.bword false))).push (.val k))=out) :
    Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local idx) : Val C Γ .uint))) m=out := by
  first
  | solve | rfl | simp only [Evm.Memory.deleteLocalCode] | omega
  | have pointer := (Evm.Memory.RefPtrFrag.local (C := C) (b := b) (F := F) root rfl).run_of_eval
      (r := q) (hm.push (.val (Evm.bword false))) (by simp only [MPath.mvalT,hroot])
    have indexRun : Evm.run (Evm.compileVal b (.simple (.local idx) : Val C Γ .uint))
        ((m.push (.val (Evm.bword false))).push (.val (base q.id)))=
          .ok (((m.push (.val (Evm.bword false))).push (.val (base q.id))).push (.val k)) 0 := by
      obtain ⟨w,rep,code⟩ := Evm.simple_sim ((hm.push (.val (Evm.bword false))).push (.val (base q.id))).state.core (.local idx) rfl
      change Evm.ReprV .uint (TEnv.get idx σ.env) w at rep
      rw [hindex] at rep
      obtain ⟨n,hn,eq,rfl⟩ := rep.uint_inv
      have same : n=k.val := by
        have h := congrArg Int.toNat eq
        simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using h.symm
      subst n
      exact code
    change Evm.run ([.push (.val (Evm.bword false))] ++ ([.mload (Evm.cellOf b root)] ++
      (Evm.compileVal b (.simple (.local idx) : Val C Γ .uint) ++ Evm.Memory.writeArrayStackCode))) m=out
    rw [Evm.run_append_ok (show Evm.run [.push (.val (Evm.bword false))] m=.ok (m.push (.val (Evm.bword false))) 0 from rfl),
      Evm.run_append_ok pointer,Evm.run_append_ok indexRun]
    rw [Evm.Memory.writeArrayStackCode,Evm.Memory.arrayStack_append_eq (m.push (.val (Evm.bword false))) (base q.id) k _
      (σ.heap.len_dyn_lt q) (hm.state.heap.arrays q).length,←Evm.Memory.writeArrayCode]
    exact clear

/-- THREE actual Source statements/typed native statements/whole word append.
INITIAL src[j] computes the child; real replacement and local rebinding derive
all third-stage prerequisites. The footprint is a local sufficient initial
condition, not global injection or a source admission restriction. -/
theorem SourceBoolRefsAt.computed_alias_delete_program
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
    (hk : k.val<σ.heap.len ((MObj.elems .dyn (σ.heap.get src))[j.val]'hj) .dyn)
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get dst),
      t.id≠((MObj.elems .dyn (σ.heap.get src))[j.val]'hj).id →
      address t.id≠address ((MObj.elems .dyn (σ.heap.get src))[j.val]'hj).id)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ),
    let ya : Source.EMState E Γ := (ym.1.set salias (.memRef rfl (address child.id)),ym.2);
    let τ := (σ.withHeap mid).setLocal alias (some child);
    let mp := Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id));
    let ma := Evm.Memory.writeMachine mp (Evm.cellOf b alias) (.val (base child.id));
    let target := Evm.Memory.writeMachine ma ((base child.id).val+1+k.val) (.val (Evm.bword false));
      σ.heap.writeAddr (.index dst .dyn (Evm.Memory.indexValue i)) child=some mid ∧
      mid.index dst .dyn (Evm.Memory.indexValue i)=some child ∧
      mid.writeAddr (.index child .dyn (Evm.Memory.indexValue k)) false=some out ∧
      (Source.execS G Fs (fuel+6) Γ.length none
        (.expr (sourceReferenceReadAssign droot sroot sdi ssi) : Source.RStmt E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fs (fuel+5) Γ.length none
        (.expr (sourceSelectedAlias salias droot sdi) : Source.RStmt E [] false .body Γ Γ)
        ym.1).run (.nil,ym.2)=(.ok (.normal ya.1),(.nil,ya.2)) ∧
      (Source.execS G Fs (fuel+4) Γ.length none
        (.expr (sourceIndexedDelete salias ski) : Source.RStmt E [] false .body Γ Γ)
        ya.1).run (.nil,ya.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fs (fuel+7) Γ.length none
        (.stmt (.expr (sourceReferenceReadAssign droot sroot sdi ssi))
          (.stmt (.expr (sourceSelectedAlias salias droot sdi))
            (.stmt (.expr (sourceIndexedDelete salias ski)) .nil)) : Source.RItems E [] false .body Γ Γ)
        y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (referenceReadStmt dl sl di si)
        (.cons (.rebindMem alias (.alias (.loc (.index .dyn (.var dl rfl) (.simple (.local di))))))
          (.cons (.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) rfl) .nil)))=
            .ok ⟨τ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (referenceReadWriteCode (C := C) b dl sl di si) m=.ok mp 0 ∧
      Evm.run (selectedAliasCode (C := C) b alias dl di) mp=.ok ma 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b alias (Evm.compileVal b (.simple (.local ki) : Val C Δ .uint))) ma=.ok target 0 ∧
      Evm.run ((referenceReadWriteCode (C := C) b dl sl di si ++ selectedAliasCode (C := C) b alias dl di) ++
        Evm.Memory.deleteLocalCode b alias (Evm.compileVal b (.simple (.local ki) : Val C Δ .uint))) m=.ok target 0 ∧
      SourceBoolRefsAt ya da mid dst address ∧ SourceBoolRefsAt z da out dst address ∧
      SourceBoolMemoryAt ya (address child.id) mid child .dyn ∧
      Source.MemOK E SH ya ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F τ base ma ∧
      Evm.Memory.RefArrayStateRepr L b frame F (τ.withHeap out) base target ∧
      ym.1=y.1 ∧ z.1=y.1.set salias (.memRef rfl (address child.id)) ∧
      TEnv.get alias τ.env=some child ∧
      MObj.elems .dyn (out.get dst)=(MObj.elems .dyn (σ.heap.get dst)).set i.val child ∧
      MObj.elems .dyn (out.get child)=(MObj.elems .dyn (σ.heap.get child)).set k.val false ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),q.id≠child.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠da → a≠address child.id → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.heap.next=y.2.heap.next ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
      target.stack=m.stack ∧
      (∀ cursor,0<b → Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m →
        (base dst.id).val+1+σ.heap.len dst .dyn≤cursor.val →
        Evm.Memory.StructAllocatorRepr out base frame cursor target) ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap mid) base mp ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),mid.get q=σ.heap.get q) ∧
      (∀ a,a≠da → ya.2.heap.get a=y.2.heap.get a) ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fs (fuel+2)
        (.mem (τ := .bool) (address child.id) k.val) (.bool false)).run ya=(.ok (),z) := by
  first
  | solve | rfl | simp only [referenceReadStmt] | omega
  | let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    obtain ⟨mid,ym,hw₁,selected,stmt₁,expr₂,stmt₂,prefixItems,native₁,native₂,prefixNative,word₁,word₂,prefixWord,
      hr₁,hr₂,child₂,mok₁,mok₂,repr₁,repr₂,locals₁,locals₂,sourceAlias,nativeAlias,heap,globals,parentElems,
      children,sourceChildren,addrs,next,effects,stack,alloc⟩ :=
      hd.computed_reference_alias_sequence G Fs (fuel+1) y σ dst src da sa address hs droot sroot sdi ssi salias
        dl sl di si alias i j hdr hsr hdi hsi htd hts hti htj hi hj SH memOK hm
    let ya : Source.EMState E Γ := (ym.1.set salias (.memRef rfl (address child.id)),ym.2)
    let τ := (σ.withHeap mid).setLocal alias (some child)
    let mp := Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id))
    let ma := Evm.Memory.writeMachine mp (Evm.cellOf b alias) (.val (base child.id))
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
    have capacity : k.val<τ.heap.len child .dyn := by
      change k.val<(MObj.elems .dyn (mid.get child)).length
      rw [children child]
      exact hk
    have member : child∈MObj.elems .dyn (τ.heap.get dst) := by
      rw [parentElems]
      exact List.mem_set hi child
    have sep : ∀ t∈MObj.elems .dyn (τ.heap.get dst),t.id≠child.id → address t.id≠address child.id := by
      rw [parentElems]
      intro t ht hn
      rcases List.mem_or_eq_of_mem_set ht with ht|ht
      · exact hsep t ht hn
      · subst t;exact (hn rfl).elim
    obtain ⟨out,z,hw₃,write₃,raw₃,hr₃,mok₃,repr₃,locals₃,parent₃⟩ :=
      hr₂.write_child_word τ dst address child member sep Fs (fuel+2) k false capacity SH mok₂ repr₂
    have expr₃ := child₂.eval_delete_of_run G Fs fuel salias ski (Evm.Memory.indexValue k) sourceAlias hscalar
      (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using capacity) write₃
    have stmt₃ := source_expr_statement_run G Fs (fuel+3) Γ.length _ ya z Source.RVal.unit expr₃
    have code₃ := delete_local_of_clear repr₂ alias ki child k nativeAlias tscalar raw₃
    have talias : TEnv.get alias τ.env=some child := nativeAlias
    have native₃ : Stmt.run τ (.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) rfl)=
        .ok ⟨τ.withHeap out,List.prefix_refl _⟩ := by
      change TRun.deleteMem (.loc (.index .dyn (.var alias rfl) (.simple (.local ki)))) τ=_
      simp only [TRun.deleteMem,TRun.clearT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,talias,tscalar,
        hw₃,TRes.ofOpt,bind,Except.bind,pure,Except.pure,PrimTy.dflt]
    have tail := source_items_cons_run G Fs (fuel+4) Γ.length
      (.expr (sourceIndexedDelete salias ski)) .nil ya z z stmt₃ (by rfl)
    have middle := source_items_cons_run G Fs (fuel+5) Γ.length
      (.expr (sourceSelectedAlias salias droot sdi)) (.stmt (.expr (sourceIndexedDelete salias ski)) .nil)
      ym ya z stmt₂ tail
    have items := source_items_cons_run G Fs (fuel+6) Γ.length
      (.expr (sourceReferenceReadAssign droot sroot sdi ssi))
      (.stmt (.expr (sourceSelectedAlias salias droot sdi)) (.stmt (.expr (sourceIndexedDelete salias ski)) .nil))
      y ym z stmt₁ middle
    have outEq : out=τ.heap.set child (MObj.setElem .dyn (τ.heap.get child) k.val false) := by
      have known : τ.heap.writeAddr (.index child .dyn (Evm.Memory.indexValue k)) false=
          some (τ.heap.set child (MObj.setElem .dyn (τ.heap.get child) k.val false)) := by
        simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast]
        exact if_pos capacity
      exact Option.some.inj (hw₃.symm.trans known)
    obtain ⟨ht,known⟩ := source_bool_write ya (address child.id) (MObj.elems .dyn (τ.heap.get child)) child₂ k.val capacity false
    have reached : z=(ya.1,{ya.2 with heap := (ya.2.heap.write (address child.id)
        (sourceBoolMemory ((MObj.elems .dyn (τ.heap.get child)).set k.val false)) ht)}) :=
      congrArg Prod.snd (write₃.symm.trans known)
    refine ⟨mid,out,ym,z,hw₁,selected,hw₃,stmt₁,stmt₂,stmt₃,items,?_,word₁,word₂,code₃,?_,hr₂,hr₃,child₂,
      mok₂,mok₃,repr₂,repr₃,locals₁,locals₃.trans locals₂,nativeAlias,?_,?_,?_,?_,?_,?_,rfl,?_,repr₁,children,addrs,write₃⟩
    · rw [Prog.run_cons_ok native₁,Prog.run_cons_ok native₂,Prog.run_cons_ok native₃,Prog.run_nil]
      rfl
    · rw [Evm.run_append_ok prefixWord];exact code₃
    · rw [parent₃];exact parentElems
    · have original : τ.heap.get child=σ.heap.get child := children child
      rw [indexedWrite_elems τ.heap out child .dyn (Evm.Memory.indexValue k) false hw₃,original]
      rfl
    · intro q hn
      rw [indexedWrite_frame τ.heap out child .dyn (Evm.Memory.indexValue k) false hw₃ q (Ne.symm hn)]
      exact children q
    · intro a hda hchild
      rw [reached,Source.Heap.write_other ya.2.heap hchild _ ht]
      exact addrs a hda
    · rw [reached];exact next
    · rw [reached];exact effects
    · intro cursor hb ha live
      rw [outEq]
      exact (alloc cursor hb ha live).setArray child k capacity false (.val (Evm.bword false)) rfl

/-- info: 'Solidity.Backend.MemoryOps.source_bool_alias_uint_frame' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_alias_uint_frame
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_alias_delete_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.computed_alias_delete_program
end Solidity.Backend.MemoryOps
