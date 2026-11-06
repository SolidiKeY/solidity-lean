import Solidity.Backend.MemoryOps.SourceUintAssignment
import Solidity.Evm.MemoryObjectStatements

/-! A resolved memory-element RHS is actually read BEFORE computing the
memory-element destination. Existing Source, intrinsic and Objects compiler
certificates execute; no new evaluator, value/heap or compiler is defined. -/
namespace Solidity.Backend.MemoryOps

/-- Existing Source syntax for `dst[i] = src[j]`. -/
def sourceUintReadAssign {E : Source.Env} {Γ : Source.RCtx}
    (dst src : Source.Idx Γ (.array .memory (.int .u256) none))
    (i j : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.int .u256) :=
  .assign (.indexArray (.local dst) (by decide) (.local i) rfl)
    (.indexArray (.local src) (.local j) rfl)

/-- Initial observers and bounds DERIVE the RHS value, both actual Source
stages, native write, reached observer and old-object/world frames. No scalar
RHS value or desired successful execution is supplied as input. -/
theorem source_uint_read_assign {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (y : Source.EMState E Γ)
    (hp : Heap H) (dst src : HRef H (.array (.prim .uint))) (da sa : Nat)
    (hd : SourceUintMemoryAt y da hp dst .dyn) (hs : SourceUintMemoryAt y sa hp src .dyn)
    (droot sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (di si : Source.Idx Γ (.int .u256)) (i j : PrimTy.uint.Denote)
    (hdr : y.1.get droot=.memRef rfl da) (hsr : y.1.get sroot=.memRef rfl sa)
    (hdi : y.1.get di=sourceUint i) (hsi : y.1.get si=sourceUint j)
    (hi : i.1.toNat<hp.len dst .dyn) (hj : j.1.toNat<hp.len src .dyn)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    let value := (MObj.elems .dyn (hp.get src))[j.1.toNat]'hj
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      (Source.evalE G F (fuel+3) (.indexArray (.local sroot) (.local si) rfl)).run y=
        (.ok (.val (sourceUint value)),y) ∧
      hp.writeAddr (.index dst .dyn i) value=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F (fuel+3) (.mem da i.1.toNat) (sourceUint value)).run y=(.ok (),z) ∧
      (Source.evalE G F (fuel+4) (sourceUintReadAssign droot sroot di si)).run y=
        (.ok (.val (sourceUint value)),z) ∧
      (Source.execS G F (fuel+5) nps none (.expr (sourceUintReadAssign droot sroot di si) :
        Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal y.1),(.nil,z.2)) ∧
      SourceUintMemoryAt z da out dst .dyn ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧
      (∀ {Q : RefTy} (q : HRef H Q),dst.id≠q.id → out.get q=hp.get q) ∧
      (∀ b,b≠da → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve
    | rfl
    | simp only [sourceUintReadAssign,Source.evalE]
    | omega
  | let value := (MObj.elems .dyn (hp.get src))[j.1.toNat]'hj
    have read : (Source.evalE G F (fuel+3) (.indexArray (.local sroot) (.local si) rfl)).run y=
        (.ok (.val (sourceUint value)),y) := hs.eval_index G F (fuel+1) sroot si j hsr hsi hj
    obtain ⟨out,z,native,write,new⟩ := hd.write_addr F (fuel+3) i value hi
    have assign : (Source.evalE G F (fuel+4) (sourceUintReadAssign droot sroot di si)).run y=
        (.ok (.val (sourceUint value)),z) := by
      rw [sourceUintReadAssign,Source.evalE,Source.Hoare.run_bind,read]
      change ((Source.evalLoc G F (fuel+3) (.indexArray (.local droot) (by decide) (.local di) rfl)) >>=
        fun loc => Source.writeLoc F (fuel+3) loc (sourceUint value) >>= fun _ => pure (Source.RVal.val (sourceUint value))).run y=_
      rw [Source.Hoare.run_bind,hd.eval_index_loc G F (fuel+1) droot di i hdr hdi hi]
      change ((Source.writeLoc (E := E) (Γ := Γ) F (fuel+3) (.mem da i.1.toNat) (sourceUint value)) >>=
        fun _ => pure (Source.RVal.val (sourceUint value))).run y=_
      rw [Source.Hoare.run_bind,write]
      rfl
    obtain ⟨locals,old,other,observers,ex,events,logs,fn⟩ := hd.write_frames F (fuel+3) i value hi native write
    have memOK := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F (fuel+3)
      (.mem (τ := .int .u256) da i.1.toNat) (sourceUint value) y ⟨hm,trivial⟩
    rw [write] at memOK
    have statement := source_expr_statement_run G F (fuel+4) nps _ y z (.val (sourceUint value)) assign
    refine ⟨out,z,read,native,write,assign,?_,new,memOK,locals,old,other,ex,events,logs,fn⟩
    simpa only [locals] using statement

/-- Literal append of the existing typed pointer/read/value/write code. -/
def uintReadAssignCode {C : Contract} {Δ : Ctx} (b : Nat)
    (dst src : Idx Δ (.mem (.array (.prim .uint)))) (di si : Idx Δ (.val .uint)) : List Evm.Instr :=
  ([.mload (Evm.cellOf b src)] ++ Evm.compileVal b (.simple (.local si) : Val C Δ .uint) ++
    Evm.Memory.Objects.readCode (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint))) ++
  [.mload (Evm.cellOf b dst)] ++ Evm.compileVal b (.simple (.local di) : Val C Δ .uint) ++
    Evm.Memory.Objects.writeCode (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint))

/-- Both intrinsic and word executions consume the actual RHS read. Strong
Objects representations, saved stack and allocator frames come from the
published read/value/write certificates, including aliased source/destination. -/
theorem source_uint_read_assign_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (fuel nps : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (dst src : HRef σ.H (.array (.prim .uint))) (da sa : Nat)
    (hd : SourceUintMemoryAt y da σ.heap dst .dyn) (hs : SourceUintMemoryAt y sa σ.heap src .dyn)
    (droot sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (sdi ssi : Source.Idx Γ (.int .u256))
    (dlocal slocal : Idx Δ (.mem (.array (.prim .uint)))) (di si : Idx Δ (.val .uint))
    (i j : PrimTy.uint.Denote)
    (hdr : y.1.get droot=.memRef rfl da) (hsr : y.1.get sroot=.memRef rfl sa)
    (hdi : y.1.get sdi=sourceUint i) (hsi : y.1.get ssi=sourceUint j)
    (htd : TEnv.get dlocal σ.env=some dst) (hts : TEnv.get slocal σ.env=some src)
    (hti : TEnv.get di σ.env=i) (htj : TEnv.get si σ.env=j)
    (hi : i.1.toNat<σ.heap.len dst .dyn) (hj : j.1.toNat<σ.heap.len src .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (din : Evm.valIn F (.simple (.local di) : Val C Δ .uint)=true)
    (sin : Evm.valIn F (.simple (.local si) : Val C Δ .uint)=true)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    let value := (MObj.elems .dyn (σ.heap.get src))[j.1.toNat]'hj
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index dst .dyn i) value=some out ∧
      (Source.evalE G Fsrc (fuel+4) (sourceUintReadAssign droot sroot sdi ssi)).run y=
        (.ok (.val (sourceUint value)),z) ∧
      (Source.execS G Fsrc (fuel+5) nps none (.expr (sourceUintReadAssign droot sroot sdi ssi) :
        Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var dlocal rfl) (.simple (.local di)))
        (.val (.readMem (.index .dyn (.var slocal rfl) (.simple (.local si))))))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintReadAssignCode (C := C) b dlocal slocal di si) m=.ok target 0 ∧
      SourceUintMemoryAt z da out dst .dyn ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      target.stack=m.stack ∧ Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      z.1=y.1 ∧ (∀ {Q : RefTy} (q : HRef σ.H Q),dst.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ b,b≠da → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  let value := (MObj.elems .dyn (σ.heap.get src))[j.1.toNat]'hj
  obtain ⟨out,z,read,native,write,assign,statement,new,mok,locals,old,other,ex,events,logs,fn⟩ :=
    source_uint_read_assign G Fsrc fuel nps y σ.heap dst src da sa hd hs droot sroot sdi ssi i j hdr hsr hdi hsi hi hj SH memOK
  have srcHit : σ.heap.index src .dyn j=some value := List.getElem?_eq_getElem hj
  have intrinsic : TRun.assignMem (.index .dyn (.var dlocal rfl) (.simple (.local di)))
      (.val (.readMem (.index .dyn (.var slocal rfl) (.simple (.local si))))) σ=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htd,hts,hti,htj,
      Heap.readAddr,srcHit,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rw [show σ.heap.writeAddr (.index dst .dyn i) value=some out from native]
  have pointer : Evm.Memory.Objects.PtrFrag (C := C) b F (.var dlocal rfl) [.mload (Evm.cellOf b dlocal)] :=
    .local dlocal rfl
  have valueCode : Evm.Memory.Objects.ValFrag (C := C) b F
      (.readMem (.index .dyn (.var slocal rfl) (.simple (.local si))))
      ([.mload (Evm.cellOf b slocal)] ++ Evm.compileVal b (.simple (.local si) : Val C Δ .uint) ++
        Evm.Memory.Objects.readCode (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint))) :=
    .read .dyn (.var slocal rfl) _ (.local slocal rfl) _ sin
  have targetResult := Evm.Memory.Objects.PtrFrag.write hm .dyn pointer (.val _ _ valueCode)
    (.simple (.local di)) din
  rw [intrinsic] at targetResult
  rcases targetResult with ⟨o,target,equal,run,represented,stack,allocator⟩ | ⟨impossible,_⟩
  · cases Except.ok.inj equal
    exact ⟨out,z,target,native,assign,statement,intrinsic,run,new,mok,represented,stack,allocator,locals,old,other,ex,events,logs,fn⟩
  · cases impossible

/-- info: 'Solidity.Backend.MemoryOps.source_uint_read_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_read_assign
/-- info: 'Solidity.Backend.MemoryOps.source_uint_read_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_read_assign_word
end Solidity.Backend.MemoryOps
