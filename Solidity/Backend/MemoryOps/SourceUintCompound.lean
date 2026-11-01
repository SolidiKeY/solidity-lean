import Solidity.Backend.MemoryOps.SourceUintSequence
import Solidity.Evm.MemoryCompound
import Solidity.Evm.MemoryExpr

/-! A checked numeric update reads the actual reached cell. Existing Source,
intrinsic and word operations are reused; this is not another arithmetic evaluator.
In-range addition and checked overflow are separate local cases, not admissions. -/
namespace Solidity.Backend.MemoryOps

theorem source_uint_add {D : Source.Layout} (checked : Bool) (x y : PrimTy.uint.Denote)
    (h : PrimTy.uint.inRange (x.1+y.1)=true) :
    Source.binVal (D := D) checked .add (sourceUint x) (sourceUint y)=
      .ok (sourceUint ⟨x.1+y.1,h⟩) ∧
    compoundT .add .uint x.1 y.1=some ⟨x.1+y.1,h⟩ := by
  have hb : Source.IntTy.u256.lo≤x.1+y.1 ∧ x.1+y.1≤Source.IntTy.u256.hi := by
    have hs : 0≤x.1+y.1 ∧ x.1+y.1<((2^256 : Nat) : Int) := of_decide_eq_true h
    have hw : ((2^256-1 : Nat) : Int)+1=((2^256 : Nat) : Int) := by decide
    simp only [Source.IntTy.lo,Source.IntTy.hi,Source.IntTy.u256,Bool.false_eq_true,↓reduceIte]
    omega
  constructor
  · simp only [Source.binVal,sourceUint,Source.intBin,Source.intRes,dif_pos hb]
    rfl
  · simp only [compoundT,BinOp.arithInt,Option.bind_some,PrimTy.ofInt?,dif_pos h]

theorem source_uint_add_overflow {D : Source.Layout} (x y : PrimTy.uint.Denote)
    (h : PrimTy.uint.inRange (x.1+y.1)≠true) :
    Source.binVal (D := D) true .add (sourceUint x) (sourceUint y)=
      .error (.revert (Source.panicData .arithmetic)) ∧
    compoundT .add .uint x.1 y.1=none := by
  have hn : ¬(Source.IntTy.u256.lo≤x.1+y.1 ∧ x.1+y.1≤Source.IntTy.u256.hi) := by
    intro hs
    apply h
    have hw : ((2^256-1 : Nat) : Int)+1=((2^256 : Nat) : Int) := by decide
    simp only [Source.IntTy.lo,Source.IntTy.hi,Source.IntTy.u256,Bool.false_eq_true,↓reduceIte] at hs
    change decide (0≤x.1+y.1 ∧ x.1+y.1<((2^256 : Nat) : Int))=true
    exact decide_eq_true (by omega)
  constructor
  · simp only [Source.binVal,sourceUint,Source.intBin,Source.intRes,dif_neg hn]
    rfl
  · simp only [compoundT,BinOp.arithInt,Option.bind_some,PrimTy.ofInt?,dif_neg h]

def sourceUintIndexedAdd {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (index rhs : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.int .u256) :=
  .compound .add (.indexArray (.local root) (by decide) (.local index) rfl) (.local rhs) (by rfl)

/-- The old value is read from INITIAL represented contents, not supplied as an
arithmetic/output oracle; every write and postrelation follows from that read. -/
theorem SourceUintMemoryAt.compound_add {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (index rhs : Source.Idx Γ (.int .u256)) (k value : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=sourceUint value) (hk : k.1.toNat<hp.len r a)
    (hadd : PrimTy.uint.inRange ((MObj.elems a (hp.get r))[k.1.toNat].1+value.1)=true) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a k) ⟨(MObj.elems a (hp.get r))[k.1.toNat].1+value.1,hadd⟩=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F (n+2) (.mem address k.1.toNat)
        (sourceUint ⟨(MObj.elems a (hp.get r))[k.1.toNat].1+value.1,hadd⟩)).run y=(.ok (),z) ∧
      (Source.evalE G F (n+3) (sourceUintIndexedAdd root index rhs)).run y=
        (.ok (.val (sourceUint ⟨(MObj.elems a (hp.get r))[k.1.toNat].1+value.1,hadd⟩)),z) ∧
      SourceUintMemoryAt z address out r a ∧ z.1=y.1 := by
  let old := (MObj.elems a (hp.get r))[k.1.toNat]
  let new : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr F (n+2) k new hk
  have hold := (hr.read_nat_iff F k.1.toNat old).mpr (List.getElem?_eq_getElem hk)
  have hbin := (source_uint_add (D := E.layout) F.checked old value hadd).1
  have he : (Source.evalE G F (n+3) (sourceUintIndexedAdd root index rhs)).run y=(.ok (.val (sourceUint new)),z) := by
    rw [sourceUintIndexedAdd,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (n+1) y rhs _ hrhs]
    simp only [Source.Hoare.run_bind]
    rw [hr.eval_index_loc G F n root index k hroot hindex hk]
    simp only [Source.Hoare.run_bind]
    rw [hold]
    simp only [Source.Hoare.run_bind]
    simp only [Source.AssignOp.kind?]
    change ((Source.convRV F (n+2) (.int .u256) (.val (sourceUint value))) >>= fun v =>
      Source.EM.lift (Source.binVal F.checked .add (sourceUint old) (sourceUint value)) >>= fun new =>
      Source.writeLoc F (n+2) (.mem address k.1.toNat) new >>= fun _ => pure (Source.RVal.val new)).run y=_
    simp only [Source.convRV,↓reduceDIte]
    rw [Source.Hoare.run_bind]
    change ((Source.EM.lift (Source.binVal F.checked .add (sourceUint old) (sourceUint value))) >>= fun new =>
      Source.writeLoc F (n+2) (.mem address k.1.toNat) new >>= fun _ => pure (Source.RVal.val new)).run y=_
    rw [hbin]
    change ((Source.writeLoc F (n+2) (.mem address k.1.toNat) (sourceUint new)) >>= fun _ => pure (Source.RVal.val (sourceUint new))).run y=_
    rw [Source.Hoare.run_bind,hs]
    rfl
  exact ⟨out,z,hw,hs,he,hr',(hr.write_frames F (n+2) k new hk hw hs).1⟩

/-- Checked overflow executes the actual resolved Source expression and stops
before the write. This is separate from unchecked wrapping and target outcomes. -/
theorem SourceUintMemoryAt.compound_add_overflow {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (hc : F.checked=true)
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (index rhs : Source.Idx Γ (.int .u256)) (k value : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=sourceUint value) (hk : k.1.toNat<hp.len r a)
    (hbad : PrimTy.uint.inRange ((MObj.elems a (hp.get r))[k.1.toNat].1+value.1)≠true) :
    (Source.evalE G F (n+3) (sourceUintIndexedAdd root index rhs)).run y=
      (.error (.revert (Source.panicData .arithmetic)),y) := by
  let old := (MObj.elems a (hp.get r))[k.1.toNat]
  have hold := (hr.read_nat_iff F k.1.toNat old).mpr (List.getElem?_eq_getElem hk)
  have hbin := (source_uint_add_overflow (D := E.layout) old value hbad).1
  rw [sourceUintIndexedAdd,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (n+1) y rhs _ hrhs]
  simp only [Source.Hoare.run_bind]
  rw [hr.eval_index_loc G F n root index k hroot hindex hk]
  simp only [Source.Hoare.run_bind]
  rw [hold]
  simp only [Source.Hoare.run_bind,Source.AssignOp.kind?]
  have hconv : (Source.convRV (E := E) (Γ := Γ) F (n+2) (.int .u256) (.val (sourceUint value))).run y=
      (.ok (.val (sourceUint value)),y) := by rfl
  have hget : (Source.getV (E := E) (Γ := Γ) (.val (sourceUint value) : Source.RVal E.layout (.int .u256))).run y=
      (.ok (sourceUint value),y) := rfl
  simp only [hconv,hget,Source.AssignOp.binOp]
  rw [hc,hbin]
  rfl

/-- Existing numeric binary/read/write code is composed read-only. It observes
actual old contents, not a supplied successful arithmetic/compiler result. -/
def uintAddLocalCode {C : Contract} {Γ : Ctx} (b : Nat)
    (root : Idx Γ (.mem (.array (.prim .uint)))) (index rhs : Idx Γ (.val .uint)) : List Evm.Instr :=
  Evm.Memory.writeLocalValueCode b root (Evm.compileVal b (.simple (.local index) : Val C Γ .uint))
    (Evm.Memory.binaryCode .uint .add
      (Evm.Memory.readLocalCode (C := C) b root (.simple (.local index)))
      (Evm.compileVal b (.simple (.local rhs) : Val C Γ .uint)))

theorem resolved_uint_add_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (si srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index rhs : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn)
    (hadd : PrimTy.uint.inRange ((MObj.elems .dyn (σ.heap.get r))[k.1.toNat].1+value.1)=true)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) ⟨(MObj.elems .dyn (σ.heap.get r))[k.1.toNat].1+value.1,hadd⟩=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem address k.1.toNat)
        (sourceUint ⟨(MObj.elems .dyn (σ.heap.get r))[k.1.toNat].1+value.1,hadd⟩)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintIndexedAdd sroot si srhs)).run y=
        (.ok (.val (sourceUint ⟨(MObj.elems .dyn (σ.heap.get r))[k.1.toNat].1+value.1,hadd⟩)),z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintIndexedAdd sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.opAssign .add rfl rfl (.mindex .dyn (.var root rfl) (.local index)) (.simple (.local rhs)))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintAddLocalCode (C := C) b root index rhs) m=.ok target 0 ∧
      SourceUintMemoryAt z address out r .dyn ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  let old := (MObj.elems .dyn (σ.heap.get r))[k.1.toNat]
  let new : PrimTy.uint.Denote := ⟨old.1+value.1,hadd⟩
  obtain ⟨out,z,hw,hs,he,hr',hl⟩ := hr.compound_add G Fsrc n sroot si srhs k value hsroot hsi hsrhs hk hadd
  have hread : σ.heap.readAddr (.index r .dyn k)=some old := List.getElem?_eq_getElem hk
  have hsum := (source_uint_add (D := E.layout) Fsrc.checked old value hadd).2
  change σ.heap.writeAddr (.index r .dyn k) ⟨old.1+value.1,hadd⟩=some out at hw
  have hi : TRun.opAssign .add (.mindex .dyn (.var root rfl) (.local index)) (.simple (.local rhs)) σ=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htrhs,htroot,
      opMemT,hread,hsum,PrimTy.key,TRes.ofOpt,hw,bind,Except.bind,pure,Except.pure]
  let iv : Val C Δ .uint := .simple (.local index)
  let rv : Val C Δ .uint := .simple (.local rhs)
  let loc : MLoc C Δ (.prim .uint) := .index .dyn (.var root rfl) iv
  let cv := Evm.Memory.compoundValue .add rfl rfl (.readMem loc) rv
  have hv : Evm.ValOutT .uint (cv.evalT σ)
      (Evm.run (Evm.Memory.binaryCode .uint .add (Evm.Memory.readLocalCode b root iv) (Evm.compileVal b rv)) m) m :=
    Evm.Memory.binaryValue_correct .add rfl rfl (.readMem loc) rv _ _
      (fun h => Evm.Memory.readLocal_correct h root iv rfl)
      (fun h => Evm.val_sim rv h.core rfl) hm
  have cert := Evm.Memory.writeLocalValue_correct hm root iv cv (Evm.compileVal b iv)
    (Evm.Memory.binaryCode .uint .add (Evm.Memory.readLocalCode b root iv) (Evm.compileVal b rv))
    (fun h => Evm.val_sim iv h.core rfl) hv
  have hassign := hi
  rw [Evm.Memory.compoundAssign_eq_write σ .add rfl rfl .dyn (.var root rfl) (.local index) rv] at hassign
  rw [hassign] at cert
  rcases cert with ⟨o,target,ho,hcode,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (n+2)
      (.mem (τ := .int .u256) address k.1.toNat) (sourceUint new) y ⟨hmem,trivial⟩
    rw [hs] at hmk
    refine ⟨out,z,target,hw,hs,he,?_,hi,hcode,hr',hstate,hmk,hl,hstack,halloc⟩
    simpa only [hl] using source_expr_statement_run G Fsrc (n+3) Γ.length _ y z (.val (sourceUint new)) he
  · cases hbad

/-- info: 'Solidity.Backend.MemoryOps.source_uint_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_add
/-- info: 'Solidity.Backend.MemoryOps.source_uint_add_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_add_overflow
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.compound_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.compound_add
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_add_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_add_word
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.compound_add_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.compound_add_overflow
end Solidity.Backend.MemoryOps
