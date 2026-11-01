import Solidity.Backend.MemoryOps.SourceUintFixedCompoundSource
import Solidity.Evm.MemoryObjectStatements

/-! Whole existing read/binary/write code over genuine fixed Source arrays and
full Objects heap/allocator representation. No weaker postrepresentation is used. -/
namespace Solidity.Backend.MemoryOps

def fixedUintAddCode {C : Contract} {Γ : Ctx} {N : Nat} (b : Nat)
    (root : Idx Γ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Γ (.val .uint)) : List Evm.Instr :=
  Evm.Memory.binaryCode .uint .add
    ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Γ .uint) ++
      Evm.Memory.Objects.readCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint)))
    (Evm.compileVal b (.simple (.local rhs) : Val C Γ .uint)) ++
    [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Γ .uint) ++
      Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint))

theorem fixed_uint_add_certificate {C : Contract} {Γ : Ctx} {N : Nat}
    {L b frame : Nat} {F : Evm.Frag Γ} {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (root : Idx Γ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Γ (.val .uint)) :
    Evm.Memory.Objects.ResultRepr L b frame F σ base m
      (TRun.opAssign .add (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)) σ)
      (Evm.run (fixedUintAddCode (C := C) b root index rhs) m) := by
  let iv : Val C Γ .uint := .simple (.local index)
  let rv : Val C Γ .uint := .simple (.local rhs)
  let read : Val C Γ .uint := .readMem (.index .fixed (.var root rfl) iv)
  let cv := Evm.Memory.compoundValue .add rfl rfl read rv
  have hv : Evm.Memory.Objects.ValFrag b F cv
      (Evm.Memory.binaryCode .uint .add
        ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b iv ++ Evm.Memory.Objects.readCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint)))
        (Evm.compileVal b rv)) :=
    .binary .add rfl rfl read rv _ _ (.read .fixed (.var root rfl) _ (.local root rfl) iv rfl) (.core rv rfl)
  rw [Evm.Memory.compoundAssign_eq_write σ .add rfl rfl .fixed (.var root rfl) (.local index) rv]
  exact Evm.Memory.Objects.PtrFrag.write hm .fixed (.local root rfl) (.val cv _ hv) iv rfl

theorem resolved_uint_fixed_add_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hadd : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1)=true)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .fixed k) ⟨(MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1,hadd⟩=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem address k.1.toNat)
        (sourceUint ⟨(MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1,hadd⟩)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedAdd sroot si srhs)).run y=
        (.ok (.val (sourceUint ⟨(MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1,hadd⟩)),z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintFixedIndexedAdd sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.opAssign .add rfl rfl (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (fixedUintAddCode (C := C) b root index rhs) m=.ok target 0 ∧
      SourceUintFixedAt z address out r ∧ Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have hkn : k.1.toNat<N := by simpa only [Heap.len,MObj.elems_fixed,(σ.heap.get r).2] using hk
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  let new : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
  obtain ⟨out,z,hw,hs,he,hr',hl⟩ := hr.compound_add G Fsrc n sroot si srhs k value hsroot hsi hsrhs hk hadd
  have hread : σ.heap.readAddr (.index r .fixed k)=some old := List.getElem?_eq_getElem hk
  have hsum := (source_uint_add (D := E.layout) Fsrc.checked old value hadd).2
  change σ.heap.writeAddr (.index r .fixed k) ⟨old.1+value.1,hadd⟩=some out at hw
  have hi : TRun.opAssign .add (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)) σ=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htrhs,htroot,
      opMemT,hread,hsum,PrimTy.key,TRes.ofOpt,hw,bind,Except.bind,pure,Except.pure]
  have cert := fixed_uint_add_certificate hm root index rhs
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [hi] at cert
  rcases cert with ⟨o,target,ho,hcode,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (n+2)
      (.mem (τ := .int .u256) address k.1.toNat) (sourceUint new) y ⟨hmem,trivial⟩
    rw [hs] at hmk
    have hf := hr.write_frames Fsrc (n+2) k new hkn hw hs
    refine ⟨out,z,target,hw,hs,he,?_,hi,hcode,hr',hstate,hmk,hl,hstack,halloc,hf.2⟩
    simpa only [hl] using source_expr_statement_run G Fsrc (n+3) Γ.length _ y z (.val (sourceUint new)) he
  · cases hbad

theorem resolved_uint_fixed_add_overflow_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (checked : Fsrc.checked=true) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hbad : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+value.1)≠true)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedAdd sroot si srhs)).run y=
      (.error (.revert (Source.panicData .arithmetic)),y) ∧
    (Source.execS G Fsrc (n+4) Γ.length none
      (.expr (sourceUintFixedIndexedAdd sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,y.2)) ∧
    Stmt.run σ (.opAssign .add rfl rfl (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)))=.error .revert ∧
    Evm.run (fixedUintAddCode (C := C) b root index rhs) m=.revert := by
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  have he := hr.compound_add_overflow G Fsrc n checked sroot si srhs k value hsroot hsi hsrhs hk hbad
  have hread : σ.heap.readAddr (.index r .fixed k)=some old := List.getElem?_eq_getElem hk
  have hsum := (source_uint_add_overflow (D := E.layout) old value hbad).2
  have hi : TRun.opAssign .add (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)) σ=.error .revert := by
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htrhs,htroot,
      opMemT,hread,hsum,PrimTy.key,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert := fixed_uint_add_certificate hm root index rhs
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [hi] at cert
  rcases cert with ⟨o,target,hno,_⟩ | ⟨_,hc⟩
  · cases hno
  · exact ⟨he,source_expr_statement_error G Fsrc (n+3) Γ.length _ y y _ he,hi,hc⟩

/-- info: 'Solidity.Backend.MemoryOps.fixed_uint_add_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_uint_add_certificate
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_add_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_add_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_add_overflow_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_add_overflow_word
end Solidity.Backend.MemoryOps
