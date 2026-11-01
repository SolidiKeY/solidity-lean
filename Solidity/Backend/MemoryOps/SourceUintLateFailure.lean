import Solidity.Backend.MemoryOps.SourceUintCompound

/-! Actual late arithmetic failure after a successful numeric memory write.
All Source/intrinsic/word operations are existing operations. Error results carry
no invented suffix heap/machine and do not assert transaction rollback. -/
namespace Solidity.Backend.MemoryOps

/-- Published read/binary/write certificates compose for every outcome, not only
the successful range case. No compiler-result or preservation oracle is input. -/
theorem uint_add_local_correct {C : Contract} {Δ : Ctx} {L b frame : Nat} {F : Evm.Frag Δ}
    {σ : State C Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index rhs : Idx Δ (.val .uint)) :
    Evm.Memory.ResultRepr L b frame F σ base m
      (TRun.opAssign .add (.mindex .dyn (.var root rfl) (.local index)) (.simple (.local rhs)) σ)
      (Evm.run (uintAddLocalCode (C := C) b root index rhs) m) := by
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
  rw [Evm.Memory.compoundAssign_eq_write σ .add rfl rfl .dyn (.var root rfl) (.local index) rv]
  exact cert

/-- Actual checked Source panic and existing intrinsic/whole-word rejection from
INITIAL aligned inputs. No successful suffix state or panic-payload identity. -/
theorem resolved_uint_add_overflow_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (hchecked : Fsrc.checked=true) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (si srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index rhs : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn)
    (hbad : PrimTy.uint.inRange ((MObj.elems .dyn (σ.heap.get r))[k.1.toNat].1+value.1)≠true)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (n+3) (sourceUintIndexedAdd sroot si srhs)).run y=
      (.error (.revert (Source.panicData .arithmetic)),y) ∧
    (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintIndexedAdd sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .arithmetic)),(.nil,y.2)) ∧
    Stmt.run σ (.opAssign .add rfl rfl (.mindex .dyn (.var root rfl) (.local index)) (.simple (.local rhs)))=.error .revert ∧
    Evm.run (uintAddLocalCode (C := C) b root index rhs) m=.revert := by
  have he := hr.compound_add_overflow G Fsrc n hchecked sroot si srhs k value hsroot hsi hsrhs hk hbad
  let old := (MObj.elems .dyn (σ.heap.get r))[k.1.toNat]
  have hread : σ.heap.readAddr (.index r .dyn k)=some old := List.getElem?_eq_getElem hk
  have hsum := (source_uint_add_overflow (D := E.layout) old value hbad).2
  have hi : TRun.opAssign .add (.mindex .dyn (.var root rfl) (.local index)) (.simple (.local rhs)) σ=.error .revert := by
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htrhs,htroot,
      opMemT,hread,PrimTy.key,hsum,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert := uint_add_local_correct hm root index rhs
  rw [hi] at cert
  rcases cert with ⟨o,target,ho,_⟩ | ⟨_,hcode⟩
  · cases ho
  · exact ⟨he,source_expr_statement_error G Fsrc (n+3) Γ.length _ y y _ he,hi,hcode⟩

/-- INITIAL operands and the arithmetic case value+delta out of range suffice.
The second operation's actual old value, bounds and representations are derived
from the first reached write. Runtime array lengths and valid indices are general. -/
theorem resolved_uint_assign_add_reject {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (hchecked : Fsrc.checked=true) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (si sv sd : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index rv rd : Idx Δ (.val .uint))
    (k value delta : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value) (hsd : y.1.get sd=sourceUint delta)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (htv : TEnv.get rv σ.env=value) (htd : TEnv.get rd σ.env=delta)
    (hk : k.1.toNat<σ.heap.len r .dyn) (hbad : PrimTy.uint.inRange (value.1+delta.1)≠true)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+3) (.mem address k.1.toNat) (sourceUint value)).run y=(.ok (),ym) ∧
      (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceUintIndexedAssign sroot si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,ym.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rv))))=
        .ok ⟨σ.withHeap mid,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rv))) m=.ok mm 0 ∧
      (Source.evalE G Fsrc (n+3) (sourceUintIndexedAdd sroot si sd)).run ym=
        (.error (.revert (Source.panicData .arithmetic)),ym) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintIndexedAdd sroot si sd) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,ym.2)) ∧
      Stmt.run (σ.withHeap mid) (.opAssign .add rfl rfl (.mindex .dyn (.var root rfl) (.local index)) (.simple (.local rd)))=.error .revert ∧
      Evm.run (uintAddLocalCode (C := C) b root index rd) mm=.revert ∧
      (Source.execItems G Fsrc (n+6) Γ.length none
        (.stmt (.expr (sourceUintIndexedAssign sroot si sv)) (.stmt (.expr (sourceUintIndexedAdd sroot si sd)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .arithmetic)),(.nil,ym.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rv))))
        (.cons (.opAssign .add rfl rfl (.mindex .dyn (.var root rfl) (.local index)) (.simple (.local rd))) .nil))=.error .revert ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rv)) ++
        uintAddLocalCode (C := C) b root index rd) m=.revert ∧
      SourceUintMemoryAt ym address mid r .dyn ∧ Source.MemOK E SH ym ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ ym.1=y.1 ∧ mm.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap mid) mm ∧
      mid.len r .dyn=σ.heap.len r .dyn ∧
      MObj.elems .dyn (mid.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.1.toNat value ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → mid.get q=σ.heap.get q) ∧
      (∀ b,b≠address → ym.2.heap.get b=y.2.heap.get b) ∧
      ym.2.ex=y.2.ex ∧ ym.2.events=y.2.events ∧ ym.2.logs=y.2.logs ∧ ym.2.fnLocals=y.2.fnLocals := by
  obtain ⟨mid,ym,mm,hw,hsw,_,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack,halloc⟩ :=
    resolved_uint_assign_word G Fsrc (n+1) σ r hr sroot si sv root index rv k value
      hsroot hsi hsv htroot hti htv hk hm SH hmem
  have hel := indexedWrite_elems σ.heap mid r .dyn k value hw
  have hlen : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [hel,List.length_set]
    rfl
  have hk' : k.1.toNat<mid.len r .dyn := by rw [hlen];exact hk
  have hget : (MObj.elems .dyn (mid.get r))[k.1.toNat]?=some value := by
    rw [hel]
    exact List.getElem?_set_self hk
  have hold : (MObj.elems .dyn (mid.get r))[k.1.toNat]=value :=
    Option.some.inj ((List.getElem?_eq_getElem hk').symm.trans hget)
  have hb : PrimTy.uint.inRange ((MObj.elems .dyn (mid.get r))[k.1.toNat].1+delta.1)≠true := by rw [hold];exact hbad
  have hfail := resolved_uint_add_overflow_word G Fsrc n hchecked (σ.withHeap mid) r hr1 sroot si sd root index rd k delta
    (by rw [hy1];exact hsroot) (by rw [hy1];exact hsi) (by rw [hy1];exact hsd)
    htroot hti htd hk' hb hm1
  have hs1' : (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceUintIndexedAssign sroot si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy1] using hs1
  have hitems := source_items_pair_error G Fsrc n Γ.length _ _ y ym ym _ hs1' hfail.2.1
  have frames := hr.write_frames Fsrc (n+3) k value hk hw hsw
  refine ⟨mid,ym,mm,hw,hsw,hs1,hi1,hc1,hfail.1,hfail.2.1,hfail.2.2.1,hfail.2.2.2,hitems,
    intrinsic_heap_pair_error σ _ _ mid .revert hi1 hfail.2.2.1,?_,hr1,hmem1,hm1,hy1,hstack,halloc,hlen,hel,
    frames.2.1,frames.2.2.1,frames.2.2.2.2.1,frames.2.2.2.2.2.1,frames.2.2.2.2.2.2.1,frames.2.2.2.2.2.2.2⟩
  rw [Evm.run_append_ok hc1]
  exact hfail.2.2.2

/-- A lower execution horizon is an exact timeout observation, not a public
length/depth cutoff or a claim that the reached prefix is rolled back. -/
theorem source_uint_add_horizon_two {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (index rhs : Source.Idx Γ (.int .u256)) :
    (Source.evalE G F 2 (sourceUintIndexedAdd root index rhs)).run y=(.error .timeout,y) := by
  rfl

/-- info: 'Solidity.Backend.MemoryOps.uint_add_local_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uint_add_local_correct
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_add_overflow_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_add_overflow_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_assign_add_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_assign_add_reject
/-- info: 'Solidity.Backend.MemoryOps.source_uint_add_horizon_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_add_horizon_two
end Solidity.Backend.MemoryOps
