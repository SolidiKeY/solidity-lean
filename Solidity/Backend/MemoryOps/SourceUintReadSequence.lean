import Solidity.Backend.MemoryOps.SourceUintReadAssignment

/-! Reached-memory RHS composition. Both statements are existing Source/native
syntax and published Objects code; the second value is derived from the first
actual write. No new interpreter or supplied intermediate observer/run. -/
namespace Solidity.Backend.MemoryOps

/-- Copy an INITIAL runtime source cell into a destination, then propagate the
ACTUALLY reached destination cell to another index. Original bounds suffice
because the first successful write preserves the destination length. -/
theorem source_uint_read_assign_chain_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel nps : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (dst src : HRef σ.H (.array (.prim .uint))) (da sa : Nat)
    (hd : SourceUintMemoryAt y da σ.heap dst .dyn) (hs : SourceUintMemoryAt y sa σ.heap src .dyn)
    (droot sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (sdi ssi sdk : Source.Idx Γ (.int .u256))
    (dlocal slocal : Idx Δ (.mem (.array (.prim .uint)))) (di si dk : Idx Δ (.val .uint))
    (i j k : PrimTy.uint.Denote)
    (hdr : y.1.get droot=.memRef rfl da) (hsr : y.1.get sroot=.memRef rfl sa)
    (hdi : y.1.get sdi=sourceUint i) (hsi : y.1.get ssi=sourceUint j) (hdk : y.1.get sdk=sourceUint k)
    (htd : TEnv.get dlocal σ.env=some dst) (hts : TEnv.get slocal σ.env=some src)
    (hti : TEnv.get di σ.env=i) (htj : TEnv.get si σ.env=j) (htk : TEnv.get dk σ.env=k)
    (hi : i.1.toNat<σ.heap.len dst .dyn) (hj : j.1.toNat<σ.heap.len src .dyn)
    (hk : k.1.toNat<σ.heap.len dst .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (din : Evm.valIn F (.simple (.local di) : Val C Δ .uint)=true)
    (sin : Evm.valIn F (.simple (.local si) : Val C Δ .uint)=true)
    (kin : Evm.valIn F (.simple (.local dk) : Val C Δ .uint)=true)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    let value := (MObj.elems .dyn (σ.heap.get src))[j.1.toNat]'hj
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index dst .dyn i) value=some mid ∧
      mid.index dst .dyn i=some value ∧
      mid.writeAddr (.index dst .dyn k) value=some out ∧
      (Source.execS G Fs (fuel+6) nps none (.expr (sourceUintReadAssign droot sroot sdi ssi) :
        Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal y.1),(.nil,ym.2)) ∧
      (Source.execS G Fs (fuel+5) nps none (.expr (sourceUintReadAssign droot droot sdk sdi) :
        Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=(.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems G Fs (fuel+7) nps none
        (.stmt (.expr (sourceUintReadAssign droot sroot sdi ssi))
          (.stmt (.expr (sourceUintReadAssign droot droot sdk sdi)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
            (.ok (.normal y.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var dlocal rfl) (.simple (.local di)))
        (.val (.readMem (.index .dyn (.var slocal rfl) (.simple (.local si))))))
        (.cons (.assignMem (.index .dyn (.var dlocal rfl) (.simple (.local dk)))
          (.val (.readMem (.index .dyn (.var dlocal rfl) (.simple (.local di)))))) .nil))=
            .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintReadAssignCode (C := C) b dlocal slocal di si) m=.ok mm 0 ∧
      Evm.run (uintReadAssignCode (C := C) b dlocal dlocal dk di) mm=.ok target 0 ∧
      Evm.run (uintReadAssignCode (C := C) b dlocal slocal di si ++ uintReadAssignCode (C := C) b dlocal dlocal dk di) m=.ok target 0 ∧
      SourceUintMemoryAt ym da mid dst .dyn ∧ SourceUintMemoryAt z da out dst .dyn ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      MObj.elems .dyn (mid.get dst)=(MObj.elems .dyn (σ.heap.get dst)).set i.1.toNat value ∧
      MObj.elems .dyn (out.get dst)=((MObj.elems .dyn (σ.heap.get dst)).set i.1.toNat value).set k.1.toNat value ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),dst.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠da → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | rfl | simp only [sourceUintReadAssign] | omega
  | let value := (MObj.elems .dyn (σ.heap.get src))[j.1.toNat]'hj
    obtain ⟨mid,ym,mm,hw1,he1,hs1,hn1,hc1,hr1,hmk1,hm1,hstack1,ha1,hy1,hother1,haddr1,hex1,hev1,hlog1,hfn1⟩ :=
      source_uint_read_assign_word G Fs (fuel+1) nps y σ dst src da sa hd hs droot sroot sdi ssi
        dlocal slocal di si i j hdr hsr hdi hsi htd hts hti htj hi hj hm din sin SH memOK
    have elems1 := indexedWrite_elems σ.heap mid dst .dyn i value hw1
    have hlen : mid.len dst .dyn=σ.heap.len dst .dyn := by
      change (MObj.elems .dyn (mid.get dst)).length=_
      rw [elems1,List.length_set]
      rfl
    have hi' : i.1.toNat<mid.len dst .dyn := by rw [hlen];exact hi
    have hk' : k.1.toNat<mid.len dst .dyn := by rw [hlen];exact hk
    have hit : mid.index dst .dyn i=some value := by
      change (MObj.elems .dyn (mid.get dst))[i.1.toNat]?=some value
      rw [elems1,List.getElem?_set_self hi]
    have reached : (MObj.elems .dyn (mid.get dst))[i.1.toNat]'hi'=value := by
      have known := List.getElem?_eq_getElem hi'
      exact Option.some.inj (known.symm.trans hit)
    obtain ⟨out,z,target,hw2,he2,hs2,hn2,hc2,hr2,hmk2,hm2,hstack2,ha2,hy2,hother2,haddr2,hex2,hev2,hlog2,hfn2⟩ :=
      source_uint_read_assign_word G Fs fuel nps ym (σ.withHeap mid) dst dst da da hr1 hr1 droot droot sdk sdi
        dlocal dlocal dk di k i (by rw [hy1];exact hdr) (by rw [hy1];exact hdr)
        (by rw [hy1];exact hdk) (by rw [hy1];exact hdi) htd htd htk hti hk' hi' hm1 kin din SH hmk1
    simp only [State.withHeap,reached] at hw2
    have hs1' : (Source.execS G Fs (fuel+6) nps none (.expr (sourceUintReadAssign droot sroot sdi ssi) :
        Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal ym.1),(.nil,ym.2)) := by
      simpa only [hy1] using hs1
    have hs2' : (Source.execS G Fs (fuel+5) nps none (.expr (sourceUintReadAssign droot droot sdk sdi) :
        Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=(.ok (.normal z.1),(.nil,z.2)) := by
      simpa only [hy2] using hs2
    have sourceItems := source_items_pair_run G Fs (fuel+1) nps _ _ y ym z hs1' hs2'
    have elems2 := indexedWrite_elems mid out dst .dyn k value hw2
    refine ⟨mid,out,ym,z,mm,target,hw1,hit,hw2,hs1,hs2,?_,intrinsic_heap_pair_run σ _ _ mid out hn1 hn2,hc1,hc2,?_,hr1,hr2,hm1,hm2,hmk1,hmk2,hy1,hy2.trans hy1,hstack2.trans hstack1,?_,elems1,?_,?_,?_,hex2.trans hex1,hev2.trans hev1,hlog2.trans hlog1,hfn2.trans hfn1⟩
    · simpa only [hy2,hy1] using sourceItems
    · rw [Evm.run_append_ok hc1];exact hc2
    · intro cursor hb ha
      exact ha2 cursor hb (ha1 cursor hb ha)
    · rw [elems2,elems1]
    · intro Q q hn
      exact (hother2 q hn).trans (hother1 q hn)
    · intro a hn
      exact (haddr2 a hn).trans (haddr1 a hn)

/-- info: 'Solidity.Backend.MemoryOps.source_uint_read_assign_chain_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_read_assign_chain_word
end Solidity.Backend.MemoryOps
