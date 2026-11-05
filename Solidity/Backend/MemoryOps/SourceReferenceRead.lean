import Solidity.Backend.MemoryOps.SourceReferenceAssignment
import Solidity.Evm.MemoryRefArrayStatements

/-! Computed reference-element RHS, using the INITIAL parent table and actual
Source/native/published pointer code. Assignment reuses an existing child;
there is no allocation, deep copy or alternative graph semantics. -/
namespace Solidity.Backend.MemoryOps

def sourceReferenceReadAssign {E : Source.Env} {Γ : Source.RCtx}
    (dst src : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256)) :
    Source.RExpr E Γ (.array .memory .bool none) :=
  .assign (.indexArray (.local dst) (by decide) (.local i) rfl)
    (.indexArray (.local src) (.local j) rfl)

def referenceReadWriteCode {C : Contract} {Δ : Ctx} (b : Nat)
    (dst src : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint)) : List Evm.Instr :=
  ([.mload (Evm.cellOf b src)] ++ Evm.compileVal b (.simple (.local j) : Val C Δ .uint) ++ Evm.Memory.readArrayStackCode) ++
    [.mload (Evm.cellOf b dst)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.writeArrayStackCode

/-- INITIAL source-parent contents determine the selected child and its Source
representation. No child/RHS local, selected identity, successful run or desired
post-observer is a premise. Repeated/shared children and parent aliases remain
admitted. This is pointer replacement, not a fresh/deep copy. -/
theorem SourceBoolRefsAt.computed_reference_assign_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel nps : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (dst src : HRef σ.H BoolRefsRef) (da sa : Nat) (address : Nat → Nat)
    (hd : SourceBoolRefsAt y da σ.heap dst address) (hs : SourceBoolRefsAt y sa σ.heap src address)
    (droot sroot : Source.Idx Γ SourceBoolRefsTy) (sdi ssi : Source.Idx Γ (.int .u256))
    (dl sl : Idx Δ (.mem BoolRefsRef)) (di si : Idx Δ (.val .uint)) (i j : Fin Evm.W)
    (hdr : y.1.get droot=.memRef rfl da) (hsr : y.1.get sroot=.memRef rfl sa)
    (hdi : y.1.get sdi=sourceUint (Evm.Memory.indexValue i)) (hsi : y.1.get ssi=sourceUint (Evm.Memory.indexValue j))
    (htd : TEnv.get dl σ.env=some dst) (hts : TEnv.get sl σ.env=some src)
    (hti : TEnv.get di σ.env=Evm.Memory.indexValue i) (htj : TEnv.get si σ.env=Evm.Memory.indexValue j)
    (hi : i.val<σ.heap.len dst .dyn) (hj : j.val<σ.heap.len src .dyn)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.index src .dyn (Evm.Memory.indexValue j)=some child ∧
      SourceBoolMemoryAt y (address child.id) σ.heap child .dyn ∧
      σ.heap.writeAddr (.index dst .dyn (Evm.Memory.indexValue i)) child=some out ∧
      (Source.evalE G Fs (fuel+3) (.indexArray (.local sroot) (.local ssi) rfl)).run y=
        (.ok (.val (.memRef rfl (address child.id))),y) ∧
      (Source.evalE G Fs (fuel+4) (sourceReferenceReadAssign droot sroot sdi ssi)).run y=
        (.ok (.val (.memRef rfl (address child.id))),z) ∧
      (Source.execS G Fs (fuel+5) nps none (.expr (sourceReferenceReadAssign droot sroot sdi ssi) :
        Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var dl rfl) (.simple (.local di)))
        (.ref (.loc (.index .dyn (.var sl rfl) (.simple (.local si))))))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (referenceReadWriteCode (C := C) b dl sl di si) m=
        .ok (Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id))) 0 ∧
      SourceBoolRefsAt z da out dst address ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base
        (Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id))) ∧
      z.1=y.1 ∧ MObj.elems .dyn (out.get dst)=(MObj.elems .dyn (σ.heap.get dst)).set i.val child ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),out.get q=σ.heap.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),dst.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠da → z.2.heap.get a=y.2.heap.get a) ∧ z.2.heap.next=y.2.heap.next ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
      (∀ cursor : Fin Evm.W,Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m →
        (base dst.id).val+1+σ.heap.len dst .dyn≤cursor.val →
        Evm.Memory.StructAllocatorRepr out base frame cursor
          (Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id)))) := by
  first
  | solve | rfl | simp only [sourceReferenceReadAssign] | omega
  | let child := (MObj.elems .dyn (σ.heap.get src))[j.val]'hj
    have hit : σ.heap.index src .dyn (Evm.Memory.indexValue j)=some child := by
      simpa only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast] using List.getElem?_eq_getElem hj
    have hv : SourceBoolMemoryAt y (address child.id) σ.heap child .dyn := hs.children child (List.getElem_mem hj)
    obtain ⟨out,z,ho,write,raw,hr',mok,_oldTarget,locals,elems,children,sourceChildren,effects⟩ :=
      hd.write_reference_word σ dst address child hv Fs (fuel+3) i hi SH memOK hm
    have read := hs.eval_parent_read G Fs (fuel+1) sroot ssi (Evm.Memory.indexValue j) child hsr hsi hit
    have loc := hd.eval_reference_loc G Fs (fuel+1) droot sdi (Evm.Memory.indexValue i) hdr hdi
      (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hi)
    have expr : (Source.evalE G Fs (fuel+4) (sourceReferenceReadAssign droot sroot sdi ssi)).run y=
        (.ok (.val (.memRef rfl (address child.id))),z) := by
      rw [sourceReferenceReadAssign,Source.evalE,Source.Hoare.run_bind,read]
      change ((Source.evalLoc G Fs (fuel+3) (.indexArray (.local droot) (by decide) (.local sdi) rfl)) >>=
        fun l => Source.writeLoc Fs (fuel+3) l (.memRef rfl (address child.id)) >>= fun _ =>
          pure (Source.RVal.val (.memRef rfl (address child.id)))).run y=_
      rw [Source.Hoare.run_bind,loc]
      change ((Source.writeLoc Fs (fuel+3) (.mem (τ := .array .memory .bool none) da i.val)
        (.memRef rfl (address child.id))) >>= fun _ => pure (Source.RVal.val (.memRef rfl (address child.id)))).run y=_
      rw [Source.Hoare.run_bind,write]
      rfl
    have statement := source_expr_statement_run G Fs (fuel+4) nps _ y z (.val (.memRef rfl (address child.id))) expr
    have pathEval : (MPath.loc (.index .dyn (.var sl rfl) (.simple (.local si))) : MPath C Δ (.ref (.array (.prim .bool)))).mvalT σ=.ok child := by
      simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,hts,htj,Heap.readAddr,hit,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have native : Stmt.run σ (.assignMem (.index .dyn (.var dl rfl) (.simple (.local di)))
        (.ref (.loc (.index .dyn (.var sl rfl) (.simple (.local si))))))=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
      change TRun.assignMem _ _ σ=_
      simp only [TRun.assignMem,MSrc.mvalT]
      rw [pathEval]
      simp only [MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htd,hti,ho,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have rhs : Evm.Memory.RefPtrFrag (C := C) b F (.loc (.index .dyn (.var sl rfl) (.simple (.local si))))
        ([.mload (Evm.cellOf b sl)] ++ Evm.compileVal b (.simple (.local si) : Val C Δ .uint) ++ Evm.Memory.readArrayStackCode) :=
      .index (.var sl rfl) _ (.local sl rfl) _ rfl
    have rhsRun := rhs.run_of_eval hm pathEval
    have dstRun := (Evm.Memory.RefPtrFrag.local (C := C) (b := b) (F := F) dl rfl).run_of_eval (r := dst)
      (hm.push (.val (base child.id))) (by simp only [MPath.mvalT,htd])
    have indexRun : Evm.run (Evm.compileVal b (.simple (.local di) : Val C Δ .uint))
        ((m.push (.val (base child.id))).push (.val (base dst.id)))=
          .ok (((m.push (.val (base child.id))).push (.val (base dst.id))).push (.val i)) 0 := by
      obtain ⟨w,hw,hc⟩ := Evm.simple_sim ((hm.push (.val (base child.id))).push (.val (base dst.id))).state.core (.local di) rfl
      change Evm.ReprV .uint (TEnv.get di σ.env) w at hw
      rw [hti] at hw
      obtain ⟨a,ha,heq,rfl⟩ := hw.uint_inv
      have hie : a=i.val := by
        have hh := congrArg Int.toNat heq
        simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hh.symm
      subst a
      exact hc
    have code : Evm.run (referenceReadWriteCode (C := C) b dl sl di si) m=
        .ok (Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id))) 0 := by
      change Evm.run (([.mload (Evm.cellOf b sl)] ++ Evm.compileVal b (.simple (.local si) : Val C Δ .uint) ++ Evm.Memory.readArrayStackCode) ++
        ([.mload (Evm.cellOf b dl)] ++ (Evm.compileVal b (.simple (.local di) : Val C Δ .uint) ++ Evm.Memory.writeArrayStackCode))) m=_
      rw [Evm.run_append_ok rhsRun,Evm.run_append_ok dstRun,Evm.run_append_ok indexRun]
      rw [Evm.Memory.writeArrayStackCode,Evm.Memory.arrayStack_append_eq (m.push (.val (base child.id)))
        (base dst.id) i _ (σ.heap.len_dyn_lt dst) (hm.arrays.arrays dst).length,←Evm.Memory.writeArrayCode]
      exact raw
    have represented : Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base
        (Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id))) := by
      have whole := Evm.Memory.RefPtrFrag.writeReference hm (Evm.Memory.RefPtrFrag.local dl rfl) rhs
        (.simple (.local di)) rfl
      rw [show TRun.assignMem (.index .dyn (.var dl rfl) (.simple (.local di)))
          (.ref (.loc (.index .dyn (.var sl rfl) (.simple (.local si))))) σ=
            .ok ⟨σ.withHeap out,List.prefix_refl _⟩ from native] at whole
      rcases whole with ⟨o,t,eq,run,post,stack⟩ | ⟨bad,_⟩
      · cases Except.ok.inj eq
        have same : t=Evm.Memory.writeMachine m ((base dst.id).val+1+i.val) (.val (base child.id)) :=
          (Evm.Out.ok.inj (run.symm.trans code)).1
        subst t
        exact post
      · cases bad
    have otherSource : ∀ a,a≠da → z.2.heap.get a=y.2.heap.get a := by
      obtain ⟨ht,known⟩ := source_refs_write y da address _ hd.parent i.val hi child
      have equal := congrArg Prod.snd (write.symm.trans known)
      dsimp only at equal
      intro a hn
      rw [equal]
      exact Source.Heap.write_other y.2.heap hn _ ht
    have next : z.2.heap.next=y.2.heap.next := by
      obtain ⟨ht,known⟩ := source_refs_write y da address _ hd.parent i.val hi child
      have equal := congrArg Prod.snd (write.symm.trans known)
      dsimp only at equal
      rw [equal]
      rfl
    have outEq : out=σ.heap.set dst (MObj.setElem .dyn (σ.heap.get dst) i.val child) := by
      simpa only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,show i.val<(MObj.elems .dyn (σ.heap.get dst)).length from hi,↓reduceIte,Option.some.injEq] using ho.symm
    refine ⟨out,z,hit,hv,ho,read,expr,?_,native,code,hr',mok,represented,locals,elems,children,sourceChildren,
      (fun q hn => by rw [outEq,Heap.get_set_ne _ _ _ hn]),otherSource,next,effects,?_⟩
    · simpa only [locals] using statement
    · intro cursor ha live
      rw [outEq]
      exact reference_slot_allocator hm dst i.val hi child cursor ha live

/-- A rejected RHS index stops the actual assignment BEFORE destination
location evaluation, even when no destination validity premise is available.
This is Source panic/state retention, not target rollback or a suffix state. -/
theorem SourceBoolRefsAt.computed_reference_rhs_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {src : HRef H BoolRefsRef} {address : Nat → Nat}
    (hs : SourceBoolRefsAt y a hp src address) (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (dst root : Source.Idx Γ SourceBoolRefsTy) (di si : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl a) (hindex : y.1.get si=sourceUint k)
    (hk : hp.len src .dyn≤k.1.toNat) :
    (Source.evalE G F (fuel+3) (sourceReferenceReadAssign dst root di si)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [sourceReferenceReadAssign,Source.evalE,Source.Hoare.run_bind,
    hs.eval_parent_bounds G F fuel root si k hroot hindex hk]

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_reference_rhs_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.computed_reference_rhs_bounds

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_reference_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.computed_reference_assign_word
end Solidity.Backend.MemoryOps
