import Solidity.Backend.MemoryOps.PhysicalLocalDeleteGoal
import Solidity.Backend.MemoryOps.SourceUintSequence

/-! Concrete Source/typed/whole-word assignment-delete sequences retain their
physical byte relation at BOTH actual reached states. Existing operations and
code are reused; byte stores remain explicitly scaled component executions,
not a complete byte-prefix compiler or transactional rollback model. -/
namespace Solidity.Backend.MemoryOps.Physical
/-- Certificate glue: the real write's unique heap/Source outputs and its
returned word representation determine the physical postrelation. The actual
multi-operation application below derives all these certificates from input. -/
theorem UintArrayAt.write_result {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y z : Source.EMState E Γ} {address : Nat} {hp out : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m target : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr) (fuel : Nat)
    (i w : Fin Evm.W) (hi : i.val<hp.len r .dyn)
    (ht : hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=some out)
    (hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.val)
      (sourceUint (Evm.Memory.indexValue w))).run y=(.ok (),z))
    (words : Evm.Memory.ArrayRepr out r base target) :
    let nextBytes := Environment.writeBytes bytes (32*(base.val+1+i.val)) (Semantics.wordBytes w.val)
    ∃ offset : Fin Evm.W,offset.val=32*(base.val+1+i.val) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,bytes⟩=some ⟨tail,nextBytes⟩) ∧
      UintArrayAt z address out r base target nextBytes ∧
      (∀ a,a<32*(base.val+1+i.val) ∨ 32*(base.val+1+i.val)+32≤a → nextBytes a=bytes a) := by
  dsimp only
  obtain ⟨actual,reached,typed,source,_word,byte,represented,_locals,_state,_other,_frame,exterior⟩ :=
    h.write_cell F fuel i w hi
  have sameHeap : actual=out := Option.some.inj (typed.symm.trans ht)
  subst actual
  have sameSource : reached=z := congrArg Prod.snd (source.symm.trans hs)
  subst reached
  obtain ⟨offset,hoff,run⟩ := byte
  exact ⟨offset,hoff,run,uint_array_reframe z address out r base _ target _ represented words,exterior⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.UintArrayAt.write_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UintArrayAt.write_result
/-- An actual full Source/typed/word assignment-delete sequence derives BOTH
reached physical relations and actual scaled stores. Original nps is preserved;
second capacity and source-local alignment follow from the real first output.
Overlap is permitted: the second store has the existing last-write precedence. -/
theorem resolved_uint_assign_delete_physical {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon nps : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (si sj srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (i j rhs : Idx Δ (.val .uint))
    (k l value : Fin Evm.W)
    (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (hsrhs : y.1.get srhs=sourceUint (Evm.Memory.indexValue value))
    (htroot : TEnv.get root σ.env=some r)
    (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (htrhs : TEnv.get rhs σ.env=Evm.Memory.indexValue value)
    (hk : k.val<σ.heap.len r .dyn) (hl : l.val<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (initial : UintArrayAt y address σ.heap r (base r.id) m bytes)
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    let first := Environment.writeBytes bytes (32*((base r.id).val+1+k.val)) (Semantics.wordBytes value.val)
    let final := Environment.writeBytes first (32*((base r.id).val+1+l.val)) (Semantics.wordBytes 0)
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine)
      (offset1 offset2 : Fin Evm.W),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) (Evm.Memory.indexValue value)=some mid ∧
      mid.writeAddr (.index r .dyn (Evm.Memory.indexValue l)) (PrimTy.dflt .uint)=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem address k.val)
        (sourceUint (Evm.Memory.indexValue value))).run y=(.ok (),ym) ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (τ := .int .u256) (.mem address l.val)).run ym=(.ok (),z) ∧
      (Source.execS G Fsrc (horizon+5) nps none
        (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+4) nps none
        (.expr (sourceUintIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (horizon+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) (.stmt (.expr (sourceUintIndexedDelete sroot sj)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
        Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok target 0 ∧
      UintArrayAt ym address mid r (base r.id) mm first ∧ UintArrayAt z address out r (base r.id) target final ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      offset1.val=32*((base r.id).val+1+k.val) ∧ offset2.val=32*((base r.id).val+1+l.val) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset1.val offset1.isLt::lenU value.val value.isLt::tail,bytes⟩=some ⟨tail,first⟩) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset2.val offset2.isLt::lenU 0 (by decide)::tail,first⟩=some ⟨tail,final⟩) ∧
      (∀ a,(a<32*((base r.id).val+1+k.val) ∨ 32*((base r.id).val+1+k.val)+32≤a) →
        (a<32*((base r.id).val+1+l.val) ∨ 32*((base r.id).val+1+l.val)+32≤a) → final a=bytes a) := by
  dsimp only
  obtain ⟨mid,out,ym,z,mm,target,ht1,ht2,sw1,sw2,_oldStmt1,_oldStmt2,_oldItems,
    typed,code1,code2,append,source1,source2,words1,words2,mem1,mem2,locals1,locals2,stack,alloc⟩ :=
    resolved_uint_assign_delete_word G Fsrc horizon σ r initial.source sroot si sj srhs root i j rhs
      (Evm.Memory.indexValue k) (Evm.Memory.indexValue l) (Evm.Memory.indexValue value)
      hsroot hsi hsj hsrhs htroot hti htj htrhs hk hl hm SH hmem
  have length : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn (Evm.Memory.indexValue k) (Evm.Memory.indexValue value) ht1,
      List.length_set]
    rfl
  have secondBound : l.val<mid.len r .dyn := by rw [length];exact hl
  have expression1 := initial.source.eval_assign_of_run G Fsrc (horizon+1) sroot si srhs
    (Evm.Memory.indexValue k) (Evm.Memory.indexValue value) hsroot hsi hsrhs hk sw1
  have expression2 := source1.eval_delete_of_run G Fsrc horizon sroot sj (Evm.Memory.indexValue l)
    (by rw [locals1];exact hsroot) (by rw [locals1];exact hsj) secondBound sw2
  have statement1 := source_expr_statement_run G Fsrc (horizon+4) nps _ y ym _ expression1
  have statement2 := source_expr_statement_run G Fsrc (horizon+3) nps _ ym z _ expression2
  have items := source_items_pair_run G Fsrc horizon nps _ _ y ym z statement1 statement2
  obtain ⟨offset1,hoff1,byte1,physical1,exterior1⟩ := initial.write_result Fsrc (horizon+3)
    k value hk ht1 sw1 (words1.heap.arrays r)
  have zeroTyped : mid.writeAddr (.index r .dyn (Evm.Memory.indexValue l))
      (Evm.Memory.indexValue (Evm.wmod 0))=some out := ht2
  have zeroSource : (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (.mem address l.val)
      (sourceUint (Evm.Memory.indexValue (Evm.wmod 0)))).run ym=(.ok (),z) := sw2
  obtain ⟨offset2,hoff2,byte2,physical2,exterior2⟩ := physical1.write_result Fsrc (horizon+2)
    l (Evm.wmod 0) secondBound zeroTyped zeroSource (words2.heap.arrays r)
  refine ⟨mid,out,ym,z,mm,target,offset1,offset2,ht1,ht2,sw1,sw2,statement1,statement2,items,
    typed,code1,code2,append,physical1,physical2,words1,words2,mem1,mem2,locals1,locals2,stack,alloc,
    hoff1,hoff2,byte1,byte2,?_⟩
  intro a firstOutside secondOutside
  exact (exterior2 a secondOutside).trans (exterior1 a firstOutside)

/-- info: 'Solidity.Backend.MemoryOps.Physical.resolved_uint_assign_delete_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_assign_delete_physical

/-- A real successful first write retains its physical prefix when the reached
second deletion is out of bounds. The Source error retains the actual reached
Source state; intrinsic/word error outcomes expose no invented suffix heap or
post-revert machine. Byte evidence is only the executed successful prefix. -/
theorem resolved_uint_assign_delete_physical_reject {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon nps : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (si sj srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (i j rhs : Idx Δ (.val .uint))
    (k l value : Fin Evm.W)
    (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (hsrhs : y.1.get srhs=sourceUint (Evm.Memory.indexValue value))
    (htroot : TEnv.get root σ.env=some r)
    (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (htrhs : TEnv.get rhs σ.env=Evm.Memory.indexValue value)
    (hk : k.val<σ.heap.len r .dyn) (hl : σ.heap.len r .dyn≤l.val)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (initial : UintArrayAt y address σ.heap r (base r.id) m bytes)
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    let first := Environment.writeBytes bytes (32*((base r.id).val+1+k.val)) (Semantics.wordBytes value.val)
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine) (offset : Fin Evm.W),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) (Evm.Memory.indexValue value)=some mid ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem address k.val)
        (sourceUint (Evm.Memory.indexValue value))).run y=(.ok (),ym) ∧
      (Source.execS G Fsrc (horizon+5) nps none
        (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok mm 0 ∧
      UintArrayAt ym address mid r (base r.id) mm first ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Source.MemOK E SH ym ∧ ym.1=y.1 ∧ mm.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap mid) mm ∧
      (Source.evalE G Fsrc (horizon+3) (sourceUintIndexedDelete sroot sj)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execS G Fsrc (horizon+4) nps none
        (.expr (sourceUintIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      (Source.execItems G Fsrc (horizon+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) (.stmt (.expr (sourceUintIndexedDelete sroot sj)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      mid.writeAddr (.index r .dyn (Evm.Memory.indexValue l)) (PrimTy.dflt .uint)=none ∧
      Stmt.run (σ.withHeap mid) (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)=.error .revert ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl) .nil))=.error .revert ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) mm=.revert ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
        Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.revert ∧
      offset.val=32*((base r.id).val+1+k.val) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU value.val value.isLt::tail,bytes⟩=some ⟨tail,first⟩) ∧
      (∀ a,a<32*((base r.id).val+1+k.val) ∨ 32*((base r.id).val+1+k.val)+32≤a → first a=bytes a) ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → mid.get q=σ.heap.get q) ∧
      (∀ a,a≠address → ym.2.heap.get a=y.2.heap.get a) ∧
      ym.2.ex=y.2.ex ∧ ym.2.events=y.2.events ∧ ym.2.logs=y.2.logs ∧ ym.2.fnLocals=y.2.fnLocals := by
  dsimp only
  obtain ⟨mid,ym,mm,hw1,sw1,_oldExpression,_oldStatement,typed1,code1,source1,words1,mem1,locals1,stack1,alloc1⟩ :=
    resolved_uint_assign_word G Fsrc (horizon+1) σ r initial.source sroot si srhs root i rhs
      (Evm.Memory.indexValue k) (Evm.Memory.indexValue value)
      hsroot hsi hsrhs htroot hti htrhs hk hm SH hmem
  have length : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn (Evm.Memory.indexValue k) (Evm.Memory.indexValue value) hw1,
      List.length_set]
    rfl
  have secondBound : mid.len r .dyn≤l.val := by rw [length];exact hl
  have expression1 := initial.source.eval_assign_of_run G Fsrc (horizon+1) sroot si srhs
    (Evm.Memory.indexValue k) (Evm.Memory.indexValue value) hsroot hsi hsrhs hk sw1
  have statement1 := source_expr_statement_run G Fsrc (horizon+4) nps _ y ym _ expression1
  have bounds := resolved_uint_delete_word_bounds G Fsrc horizon (σ.withHeap mid) r source1 sroot sj root j
    (Evm.Memory.indexValue l) (by rw [locals1];exact hsroot) (by rw [locals1];exact hsj)
    htroot htj secondBound words1
  have statement2 := source_expr_statement_error G Fsrc (horizon+3) nps _ ym ym _ bounds.1
  have items := source_items_pair_error G Fsrc horizon nps _ _ y ym ym _ statement1 statement2
  have noWrite := (source1.delete_bounds Fsrc horizon (Evm.Memory.indexValue l) secondBound).2
  have typed2 : Stmt.run (σ.withHeap mid)
      (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)=.error .revert := by
    change TRun.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) (σ.withHeap mid)=_
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,State.withHeap,htroot,htj,
      bind,Except.bind,pure,Except.pure,TRun.clearT,noWrite,TRes.ofOpt]
  have typed := intrinsic_heap_pair_error σ _ _ mid .revert typed1 typed2
  have append : Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
      Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.revert := by
    rw [Evm.run_append_ok code1]
    exact bounds.2
  obtain ⟨offset,hoff,byte,physical,exterior⟩ := initial.write_result Fsrc (horizon+3)
    k value hk hw1 sw1 (words1.heap.arrays r)
  obtain ⟨_sameLocals,otherTyped,otherSource,_otherCorrespondence,world,events,logs,fnLocals⟩ :=
    initial.source.write_frames Fsrc (horizon+3) (Evm.Memory.indexValue k) (Evm.Memory.indexValue value)
      hk hw1 sw1
  exact ⟨mid,ym,mm,offset,hw1,sw1,statement1,code1,physical,words1,mem1,locals1,stack1,alloc1,
    bounds.1,statement2,items,noWrite,typed2,typed,bounds.2,append,hoff,byte,exterior,
    otherTyped,otherSource,world,events,logs,fnLocals⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.resolved_uint_assign_delete_physical_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_assign_delete_physical_reject

/-- Existing deletion then assignment execute at their actual reached states.
The second capacity comes from the first successful length-preserving write;
original Source nps and both physical stores are retained. Arbitrary overlap
is allowed: the later assignment supplies the final selected value. -/
theorem resolved_uint_delete_assign_physical {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon nps : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (si sj srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (i j rhs : Idx Δ (.val .uint))
    (k l value : Fin Evm.W)
    (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (hsrhs : y.1.get srhs=sourceUint (Evm.Memory.indexValue value))
    (htroot : TEnv.get root σ.env=some r)
    (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (htrhs : TEnv.get rhs σ.env=Evm.Memory.indexValue value)
    (hk : k.val<σ.heap.len r .dyn) (hl : l.val<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (initial : UintArrayAt y address σ.heap r (base r.id) m bytes)
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    let first := Environment.writeBytes bytes (32*((base r.id).val+1+l.val)) (Semantics.wordBytes 0)
    let final := Environment.writeBytes first (32*((base r.id).val+1+k.val)) (Semantics.wordBytes value.val)
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine)
      (offset1 offset2 : Fin Evm.W),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue l)) (PrimTy.dflt .uint)=some mid ∧
      mid.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) (Evm.Memory.indexValue value)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (τ := .int .u256) (.mem address l.val)).run y=(.ok (),ym) ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (.mem address k.val)
        (sourceUint (Evm.Memory.indexValue value))).run ym=(.ok (),z) ∧
      (Source.execS G Fsrc (horizon+5) nps none
        (.expr (sourceUintIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+4) nps none
        (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (horizon+6) nps none
        (.stmt (.expr (sourceUintIndexedDelete sroot sj)) (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)
        (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs)))) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint)) ++
        Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok target 0 ∧
      UintArrayAt ym address mid r (base r.id) mm first ∧ UintArrayAt z address out r (base r.id) target final ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      offset1.val=32*((base r.id).val+1+l.val) ∧ offset2.val=32*((base r.id).val+1+k.val) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset1.val offset1.isLt::lenU 0 (by decide)::tail,bytes⟩=some ⟨tail,first⟩) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset2.val offset2.isLt::lenU value.val value.isLt::tail,first⟩=some ⟨tail,final⟩) ∧
      (∀ a,(a<32*((base r.id).val+1+l.val) ∨ 32*((base r.id).val+1+l.val)+32≤a) →
        (a<32*((base r.id).val+1+k.val) ∨ 32*((base r.id).val+1+k.val)+32≤a) → final a=bytes a) := by
  dsimp only
  obtain ⟨mid,ym,mm,ht1,sw1,expression1,_oldStatement1,typed1,code1,source1,words1,mem1,locals1,stack1,alloc1⟩ :=
    resolved_uint_delete_word G Fsrc (horizon+1) σ r initial.source sroot sj root j (Evm.Memory.indexValue l)
      hsroot hsj htroot htj hl hm SH hmem
  have length : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn (Evm.Memory.indexValue l) (PrimTy.dflt .uint) ht1,List.length_set]
    rfl
  have secondBound : k.val<mid.len r .dyn := by rw [length];exact hk
  obtain ⟨out,z,target,ht2,sw2,expression2,_oldStatement2,typed2,code2,source2,words2,mem2,locals2,stack2,alloc2⟩ :=
    resolved_uint_assign_word G Fsrc horizon (σ.withHeap mid) r source1 sroot si srhs root i rhs
      (Evm.Memory.indexValue k) (Evm.Memory.indexValue value)
      (by rw [locals1];exact hsroot) (by rw [locals1];exact hsi) (by rw [locals1];exact hsrhs)
      htroot hti htrhs secondBound words1 SH mem1
  have statement1 := source_expr_statement_run G Fsrc (horizon+4) nps _ y ym _ expression1
  have statement2 := source_expr_statement_run G Fsrc (horizon+3) nps _ ym z _ expression2
  have items := source_items_pair_run G Fsrc horizon nps _ _ y ym z statement1 statement2
  have typed := intrinsic_heap_pair_run σ _ _ mid out typed1 typed2
  have append : Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint)) ++
      Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok target 0 := by
    rw [Evm.run_append_ok code1]
    exact code2
  have firstTyped : σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue l))
      (Evm.Memory.indexValue (Evm.wmod 0))=some mid := ht1
  have firstSource : (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem address l.val)
      (sourceUint (Evm.Memory.indexValue (Evm.wmod 0)))).run y=(.ok (),ym) := sw1
  obtain ⟨offset1,hoff1,byte1,physical1,exterior1⟩ := initial.write_result Fsrc (horizon+3)
    l (Evm.wmod 0) hl firstTyped firstSource (words1.heap.arrays r)
  obtain ⟨offset2,hoff2,byte2,physical2,exterior2⟩ := physical1.write_result Fsrc (horizon+2)
    k value secondBound ht2 sw2 (words2.heap.arrays r)
  refine ⟨mid,out,ym,z,mm,target,offset1,offset2,ht1,ht2,sw1,sw2,statement1,statement2,items,
    typed,code1,code2,append,physical1,physical2,words1,words2,mem1,mem2,locals1,locals2.trans locals1,
    stack2.trans stack1,?_,hoff1,hoff2,byte1,byte2,?_⟩
  · intro cursor positive initialAllocator
    exact alloc2 cursor positive (alloc1 cursor positive initialAllocator)
  · intro a outside1 outside2
    exact (exterior2 a outside2).trans (exterior1 a outside1)

/-- info: 'Solidity.Backend.MemoryOps.Physical.resolved_uint_delete_assign_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_delete_assign_physical

/-- Distinct numeric word cells have disjoint32-byte spans, so their actual
byte stores commute. This is component memory algebra; executable MSTORE fits
still come from the operation certificates, not from this equality. -/
theorem word_stores_commute (bytes : Environment.Memory) (c d : Nat) (v w : Fin Evm.W)
    (distinct : c≠d) :
    Environment.writeBytes (Environment.writeBytes bytes (32*c) (Semantics.wordBytes v.val))
      (32*d) (Semantics.wordBytes w.val)=
    Environment.writeBytes (Environment.writeBytes bytes (32*d) (Semantics.wordBytes w.val))
      (32*c) (Semantics.wordBytes v.val) := by
  funext a
  have insideEq (x y : Environment.Memory) (dst : Nat) (word : Fin Evm.W)
      (h : dst≤a ∧ a<dst+32) :
      Environment.writeBytes x dst (Semantics.wordBytes word.val) a=
      Environment.writeBytes y dst (Semantics.wordBytes word.val) a := by
    let j := a-dst
    have hj : j<(Semantics.wordBytes word.val).length := by
      rw [Environment.wordBytes_length]
      dsimp only [j]
      omega
    have position : dst+j=a := by dsimp only [j];omega
    have left := Environment.writeBytes_at (Semantics.wordBytes word.val) dst j x hj
    have right := Environment.writeBytes_at (Semantics.wordBytes word.val) dst j y hj
    rw [position] at left right
    exact left.trans right.symm
  by_cases hc : 32*c≤a ∧ a<32*c+32
  · have hd : a<32*d ∨ 32*d+(Semantics.wordBytes w.val).length≤a := by
      rw [Environment.wordBytes_length]
      omega
    rw [Environment.writeBytes_frame (Semantics.wordBytes w.val) (32*d) a _ hd]
    exact insideEq _ _ (32*c) v hc
  · have outsideC : a<32*c ∨ 32*c+(Semantics.wordBytes v.val).length≤a := by
      rw [Environment.wordBytes_length]
      omega
    by_cases hd : 32*d≤a ∧ a<32*d+32
    · rw [Environment.writeBytes_frame (Semantics.wordBytes v.val) (32*c) a _ outsideC]
      exact insideEq _ _ (32*d) w hd
    · have outsideD : a<32*d ∨ 32*d+(Semantics.wordBytes w.val).length≤a := by
        rw [Environment.wordBytes_length]
        omega
      rw [Environment.writeBytes_frame (Semantics.wordBytes w.val) (32*d) a _ outsideD,
        Environment.writeBytes_frame (Semantics.wordBytes v.val) (32*c) a _ outsideC,
        Environment.writeBytes_frame (Semantics.wordBytes v.val) (32*c) a _ outsideC,
        Environment.writeBytes_frame (Semantics.wordBytes w.val) (32*d) a _ outsideD]

/-- info: 'Solidity.Backend.MemoryOps.Physical.word_stores_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_stores_commute

/-- Two REAL orderings from one initial representation reach a common
physical byte buffer when their typed indices differ. Both Source/Prog/whole
word executions and actual intermediate states are retained. No whole Source
state/word-machine equality or byte decoding injectivity is asserted. -/
theorem resolved_uint_disjoint_orders {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon nps : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (si sj srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (i j rhs : Idx Δ (.val .uint))
    (k l value : Fin Evm.W)
    (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (hsrhs : y.1.get srhs=sourceUint (Evm.Memory.indexValue value))
    (htroot : TEnv.get root σ.env=some r)
    (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (htrhs : TEnv.get rhs σ.env=Evm.Memory.indexValue value)
    (hk : k.val<σ.heap.len r .dyn) (hl : l.val<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (initial : UintArrayAt y address σ.heap r (base r.id) m bytes)
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) (distinct : k≠l) :
    let firstF := Environment.writeBytes bytes (32*((base r.id).val+1+k.val)) (Semantics.wordBytes value.val)
    let firstR := Environment.writeBytes bytes (32*((base r.id).val+1+l.val)) (Semantics.wordBytes 0)
    let common := Environment.writeBytes firstF (32*((base r.id).val+1+l.val)) (Semantics.wordBytes 0)
    ∃ (midF outF midR outR : Heap σ.H) (ymF zF ymR zR : Source.EMState E Γ)
      (mmF targetF mmR targetR : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) (Evm.Memory.indexValue value)=some midF ∧
      midF.writeAddr (.index r .dyn (Evm.Memory.indexValue l)) (PrimTy.dflt .uint)=some outF ∧
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue l)) (PrimTy.dflt .uint)=some midR ∧
      midR.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) (Evm.Memory.indexValue value)=some outR ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem address k.val)
        (sourceUint (Evm.Memory.indexValue value))).run y=(.ok (),ymF) ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (τ := .int .u256) (.mem address l.val)).run ymF=(.ok (),zF) ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (τ := .int .u256) (.mem address l.val)).run y=(.ok (),ymR) ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (.mem address k.val)
        (sourceUint (Evm.Memory.indexValue value))).run ymR=(.ok (),zR) ∧
      (Source.execItems G Fsrc (horizon+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) (.stmt (.expr (sourceUintIndexedDelete sroot sj)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal zF.1),(.nil,zF.2)) ∧
      (Source.execItems G Fsrc (horizon+6) nps none
        (.stmt (.expr (sourceUintIndexedDelete sroot sj)) (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal zR.1),(.nil,zR.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl) .nil))=
          .ok ⟨σ.withHeap outF,List.prefix_refl _⟩ ∧
      Prog.run σ (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)
        (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs)))) .nil))=
          .ok ⟨σ.withHeap outR,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok mmF 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) mmF=.ok targetF 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok mmR 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) mmR=.ok targetR 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
        Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok targetF 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint)) ++
        Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok targetR 0 ∧
      UintArrayAt ymF address midF r (base r.id) mmF firstF ∧
      UintArrayAt zF address outF r (base r.id) targetF common ∧
      UintArrayAt ymR address midR r (base r.id) mmR firstR ∧
      UintArrayAt zR address outR r (base r.id) targetR common ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap midF) base mmF ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap outF) base targetF ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap midR) base mmR ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap outR) base targetR ∧
      Source.MemOK E SH ymF ∧ Source.MemOK E SH zF ∧ Source.MemOK E SH ymR ∧ Source.MemOK E SH zR ∧
      ymF.1=y.1 ∧ zF.1=y.1 ∧ ymR.1=y.1 ∧ zR.1=y.1 ∧ targetF.stack=m.stack ∧ targetR.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap outF) targetF ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap outR) targetR := by
  dsimp only
  obtain ⟨midF,outF,ymF,zF,mmF,targetF,offF1,offF2,fw1,fw2,swF1,swF2,stmtF1,stmtF2,itemsF,
    typedF,codeF1,codeF2,appendF,physicalF1,physicalF2,wordsF1,wordsF2,memF1,memF2,locF1,locF2,stackF,allocF,
    offsetF1,offsetF2,byteF1,byteF2,exteriorF⟩ :=
    resolved_uint_assign_delete_physical G Fsrc horizon nps σ r sroot si sj srhs root i j rhs k l value
      hsroot hsi hsj hsrhs htroot hti htj htrhs hk hl initial hm SH hmem
  obtain ⟨midR,outR,ymR,zR,mmR,targetR,offR1,offR2,rw1,rw2,swR1,swR2,stmtR1,stmtR2,itemsR,
    typedR,codeR1,codeR2,appendR,physicalR1,physicalR2,wordsR1,wordsR2,memR1,memR2,locR1,locR2,stackR,allocR,
    offsetR1,offsetR2,byteR1,byteR2,exteriorR⟩ :=
    resolved_uint_delete_assign_physical G Fsrc horizon nps σ r sroot si sj srhs root i j rhs k l value
      hsroot hsi hsj hsrhs htroot hti htj htrhs hk hl initial hm SH hmem
  have cellsDistinct : (base r.id).val+1+k.val≠(base r.id).val+1+l.val := by
    intro same
    apply distinct
    apply Fin.ext
    omega
  have common : Environment.writeBytes
      (Environment.writeBytes bytes (32*((base r.id).val+1+k.val)) (Semantics.wordBytes value.val))
      (32*((base r.id).val+1+l.val)) (Semantics.wordBytes 0)=
    Environment.writeBytes
      (Environment.writeBytes bytes (32*((base r.id).val+1+l.val)) (Semantics.wordBytes 0))
      (32*((base r.id).val+1+k.val)) (Semantics.wordBytes value.val) :=
    word_stores_commute bytes ((base r.id).val+1+k.val) ((base r.id).val+1+l.val) value (Evm.wmod 0) cellsDistinct
  have reverseCommon : UintArrayAt zR address outR r (base r.id) targetR
      (Environment.writeBytes
        (Environment.writeBytes bytes (32*((base r.id).val+1+k.val)) (Semantics.wordBytes value.val))
        (32*((base r.id).val+1+l.val)) (Semantics.wordBytes 0)) := by
    rw [common]
    exact physicalR2
  exact ⟨midF,outF,midR,outR,ymF,zF,ymR,zR,mmF,targetF,mmR,targetR,
    fw1,fw2,rw1,rw2,swF1,swF2,swR1,swR2,itemsF,itemsR,typedF,typedR,
    codeF1,codeF2,codeR1,codeR2,appendF,appendR,physicalF1,physicalF2,physicalR1,reverseCommon,
    wordsF1,wordsF2,wordsR1,wordsR2,memF1,memF2,memR1,memR2,locF1,locF2,locR1,locR2,stackF,stackR,allocF,allocR⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.resolved_uint_disjoint_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_disjoint_orders

end Solidity.Backend.MemoryOps.Physical
