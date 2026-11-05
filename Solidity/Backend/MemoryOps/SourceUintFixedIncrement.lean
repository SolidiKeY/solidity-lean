import Solidity.Backend.MemoryOps.SourceUintFixedCompound

/-! Existing prefix/postfix fixed uint increment. The independent Source result
is old versus new; standalone intrinsic/word statements discard that result.
Only in-range success agrees with the checked target for unchecked Source mode. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedIncrement {E : Source.Env} {Γ : Source.RCtx} {N : Nat}
    (pre : Bool) (root : Source.Idx Γ (.array .memory (.int .u256) (some N)))
    (index : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.int .u256) :=
  .incDec true pre (.indexArray (.local root) (by decide) (.local index) rfl)

def fixedUintIncrementOp (pre : Bool) : IncDec := if pre then .preInc else .postInc

def fixedUintIncrementCode {C : Contract} {Γ : Ctx} {N : Nat} (b : Nat)
    (root : Idx Γ (.mem (.fixed (.prim .uint) N))) (index : Idx Γ (.val .uint)) : List Evm.Instr :=
  Evm.Memory.binaryCode .uint .add
    ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Γ .uint) ++
      Evm.Memory.Objects.readCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint)))
    (Evm.compileVal b (Evm.Memory.incrementOne (p := .uint) rfl : Val C Γ .uint)) ++
    [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Γ .uint) ++
      Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint))

/-- Published read/binary/write and increment-as-compound producers preserve the
FULL Objects representation; no weaker legacy postcondition is substituted. -/
theorem fixed_uint_increment_certificate {C : Contract} {Γ : Ctx} {N : Nat}
    {L b frame : Nat} {F : Evm.Frag Γ} {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) (pre : Bool)
    (root : Idx Γ (.mem (.fixed (.prim .uint) N))) (index : Idx Γ (.val .uint)) :
    Evm.Memory.Objects.ResultRepr L b frame F σ base m
      (TRun.incDec (fixedUintIncrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ)
      (Evm.run (fixedUintIncrementCode (C := C) b root index) m) := by
  let iv : Val C Γ .uint := .simple (.local index)
  let rv : Val C Γ .uint := Evm.Memory.incrementOne rfl
  let read : Val C Γ .uint := .readMem (.index .fixed (.var root rfl) iv)
  let cv := Evm.Memory.compoundValue .add rfl rfl read rv
  have hv : Evm.Memory.Objects.ValFrag b F cv
      (Evm.Memory.binaryCode .uint .add
        ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b iv ++ Evm.Memory.Objects.readCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint)))
        (Evm.compileVal b rv)) :=
    .binary .add rfl rfl read rv _ _ (.read .fixed (.var root rfl) _ (.local root rfl) iv rfl) (.core rv rfl)
  rw [Evm.Memory.incrementMemory_eq_compound σ (fixedUintIncrementOp pre) rfl .fixed (.var root rfl) (.local index)]
  have hop : (fixedUintIncrementOp pre).binOp=.add := by cases pre <;> rfl
  rw [hop]
  rw [Evm.Memory.compoundAssign_eq_write σ .add rfl rfl .fixed (.var root rfl) (.local index) rv]
  exact Evm.Memory.Objects.PtrFrag.write hm .fixed (.local root rfl) (.val cv _ hv) iv rfl

/-- INITIAL represented cell and bounds derive actual prefix/postfix Source
results, the same actual typed write and whole word statement, with all frames.
No desired old value or reached observer is a caller premise. -/
theorem resolved_uint_fixed_increment_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (pre : Bool) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hadd : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+1)=true)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
    let new : PrimTy.uint.Denote := ⟨old.1+1,hadd⟩
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .fixed k) new=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem address k.1.toNat) (sourceUint new)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintFixedIncrement pre sroot si)).run y=
        (.ok (.val (sourceUint (if pre then new else old))),z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintFixedIncrement pre sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,z.2)) ∧
      TRun.incDec (fixedUintIncrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (fixedUintIncrementCode (C := C) b root index) m=.ok target 0 ∧
      SourceUintFixedAt z address out r ∧ Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  let new : PrimTy.uint.Denote := ⟨old.1+1,hadd⟩
  have hkn : k.1.toNat<N := by simpa only [Heap.len,MObj.elems_fixed,(σ.heap.get r).2] using hk
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr Fsrc (n+2) k new hkn
  have hold : (Source.readLoc (E := E) (Γ := Γ) Fsrc (.mem address k.1.toNat)).run y=(.ok (sourceUint old),y) := by
    simpa only [Source.readLoc,old,MObj.elems_fixed] using hr.read k.1.toNat hkn
  have hinc : Source.incDecVal (D := E.layout) Fsrc.checked true (sourceUint old)=.ok (sourceUint new) := by
    have h := (source_uint_add (D := E.layout) Fsrc.checked old (⟨1,by rfl⟩ : PrimTy.uint.Denote) hadd).1
    change Source.intRes .u256 Fsrc.checked (old.1+1)=_ at h ⊢
    exact h
  have he : (Source.evalE G Fsrc (n+3) (sourceUintFixedIncrement pre sroot si)).run y=(.ok (.val (sourceUint (if pre then new else old))),z) := by
    rw [sourceUintFixedIncrement,Source.evalE,Source.Hoare.run_bind,hr.eval_index_loc G Fsrc n sroot si k hsroot hsi hkn]
    simp only [Source.Hoare.run_bind]
    rw [hold]
    simp only [Source.Hoare.run_bind]
    rw [hinc]
    rw [show (Source.EM.lift (E := E) (Γ := Γ) (.ok (sourceUint new))).run y=(.ok (sourceUint new),y) from rfl]
    cases pre <;> simp only [Bool.false_eq_true,↓reduceIte] <;> rw [hs] <;> rfl
  have hread : σ.heap.readAddr (.index r .fixed k)=some old := List.getElem?_eq_getElem hk
  have hsum := (source_uint_add (D := E.layout) Fsrc.checked old (⟨1,by rfl⟩ : PrimTy.uint.Denote) hadd).2
  have hi : TRun.incDec (fixedUintIncrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    rw [Evm.Memory.incrementMemory_eq_compound σ (fixedUintIncrementOp pre) rfl .fixed (.var root rfl) (.local index)]
    have hop : (fixedUintIncrementOp pre).binOp=.add := by cases pre <;> rfl
    rw [hop]
    dsimp only [new] at hw
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htroot,
      Evm.Memory.incrementOne,PrimTy.ofLit,opMemT,hread,hsum,PrimTy.key,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rw [hw]
  have cert := fixed_uint_increment_certificate hm pre root index
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [hi] at cert
  rcases cert with ⟨o,target,ho,hcode,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (n+2)
      (.mem (τ := .int .u256) address k.1.toNat) (sourceUint new) y ⟨hmem,trivial⟩
    rw [hs] at hmk
    have hf := hr.write_frames Fsrc (n+2) k new hkn hw hs
    have hstmt := source_expr_statement_run G Fsrc (n+3) Γ.length _ y z (.val (sourceUint (if pre then new else old))) he
    exact ⟨out,z,target,hw,hs,he,by simpa only [hf.1] using hstmt,hi,hcode,hr',hstate,hmk,hf.1,hstack,halloc,hf.2⟩
  · cases hbad

/-- info: 'Solidity.Backend.MemoryOps.fixed_uint_increment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_uint_increment_certificate
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_increment_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_increment_word

/-- Checked increment overflow reads the actual represented reached cell, then
halts before writing. A target revert has no returned machine or panic bytes. -/
theorem resolved_uint_fixed_increment_overflow_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (pre : Bool) (checked : Fsrc.checked=true) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hbad : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1+1)≠true)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (n+3) (sourceUintFixedIncrement pre sroot si)).run y=
      (.error (.revert (Source.panicData .arithmetic)),y) ∧
    (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintFixedIncrement pre sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .arithmetic)),(.nil,y.2)) ∧
    TRun.incDec (fixedUintIncrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ=.error .revert ∧
    Evm.run (fixedUintIncrementCode (C := C) b root index) m=.revert := by
  let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
  have hkn : k.1.toNat<N := by simpa only [Heap.len,MObj.elems_fixed,(σ.heap.get r).2] using hk
  have hold : (Source.readLoc (E := E) (Γ := Γ) Fsrc (.mem address k.1.toNat)).run y=(.ok (sourceUint old),y) := by
    simpa only [Source.readLoc,old,MObj.elems_fixed] using hr.read k.1.toNat hkn
  have hinc : Source.incDecVal (D := E.layout) Fsrc.checked true (sourceUint old)=.error (.revert (Source.panicData .arithmetic)) := by
    rw [checked]
    have h := (source_uint_add_overflow (D := E.layout) old (⟨1,by rfl⟩ : PrimTy.uint.Denote) hbad).1
    change Source.intRes .u256 true (old.1+1)=_ at h ⊢
    exact h
  have he : (Source.evalE G Fsrc (n+3) (sourceUintFixedIncrement pre sroot si)).run y=
      (.error (.revert (Source.panicData .arithmetic)),y) := by
    rw [sourceUintFixedIncrement,Source.evalE,Source.Hoare.run_bind,hr.eval_index_loc G Fsrc n sroot si k hsroot hsi hkn]
    simp only [Source.Hoare.run_bind]
    rw [hold]
    simp only [Source.Hoare.run_bind]
    rw [hinc]
    rfl
  have hread : σ.heap.readAddr (.index r .fixed k)=some old := List.getElem?_eq_getElem hk
  have hsum := (source_uint_add_overflow (D := E.layout) old (⟨1,by rfl⟩ : PrimTy.uint.Denote) hbad).2
  have hi : TRun.incDec (fixedUintIncrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ=.error .revert := by
    rw [Evm.Memory.incrementMemory_eq_compound σ (fixedUintIncrementOp pre) rfl .fixed (.var root rfl) (.local index)]
    have hop : (fixedUintIncrementOp pre).binOp=.add := by cases pre <;> rfl
    rw [hop]
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htroot,
      Evm.Memory.incrementOne,PrimTy.ofLit,opMemT,hread,hsum,PrimTy.key,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert := fixed_uint_increment_certificate hm pre root index
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [hi] at cert
  rcases cert with ⟨o,target,hno,_⟩ | ⟨_,hc⟩
  · cases hno
  · exact ⟨he,source_expr_statement_error G Fsrc (n+3) Γ.length _ y y _ he,hi,hc⟩

/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_increment_overflow_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_increment_overflow_word
end Solidity.Backend.MemoryOps
