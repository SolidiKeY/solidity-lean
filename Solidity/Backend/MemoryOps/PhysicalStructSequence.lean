import Solidity.Backend.MemoryOps.PhysicalStructReference
import Solidity.Backend.MemoryOps.PhysicalStructChild

/-! Actual named reference redirection followed by a reached selected-child
write in the existing Source RItems, intrinsic Prog and word append. Initial
locals and replacement-child bounds suffice; the second observer, capacity
and physical frame are derived from the first real execution. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Local scalar operands survive reference redirection; the replacement
child's original contents/length determine the reached indexed write. -/
theorem assign_struct_reference_child_physical
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n nps : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (v : HRef σ.H (.array (.prim .bool)))
    (address : Nat → Nat) (initial : SourceBoolStructAt y a σ.heap r address layout)
    (replacement : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sroot : Source.Idx Γ (.struct .memory dn)) (srhs : Source.Idx Γ SourceBoolArrayTy)
    (si : Source.Idx Γ (.int .u256)) (sv : Source.Idx Γ .bool)
    (root : Idx Δ (.mem (.struct s))) (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (index : Idx Δ (.val .uint)) (boolRhs : Idx Δ (.val .bool))
    (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=.bool value)
    (htroot : TEnv.get root σ.env=some r) (htrhs : TEnv.get rhs σ.env=some v)
    (htindex : TEnv.get index σ.env=k) (htvalue : TEnv.get boolRhs σ.env=value)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (bound : k.1.toNat<σ.heap.len v .dyn)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (words : Evm.Memory.StateRepr L b frame F σ base m)
    (indexIn : Evm.valIn (C := C) F (.simple (.local index))=true)
    (valueIn : Evm.valIn (C := C) F (.simple (.local boolRhs))=true)
    (bytes : Environment.Memory) (pointerLive : Nat → Prop)
    (pointers : PointerFrame m bytes pointerLive)
    (slotLive : pointerLive ((base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child))
    (pointerFits : 32*(base v.id).val<2^256)
    (numbers : WordFrame m bytes (fun c => (base v.id).val≤c ∧ c<(base v.id).val+1+σ.heap.len v .dyn))
    (separate : ∀ c,(base v.id).val≤c ∧ c<(base v.id).val+1+σ.heap.len v .dyn →
      c≠(base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child) :
    let mid := σ.heap.setField r layout.child_type v
    let parentCell := (base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child
    let childCell := (base v.id).val+1+k.1.toNat
    let firstBytes := Environment.writeBytes bytes (32*parentCell) (Semantics.wordBytes (32*(base v.id).val))
    let finalBytes := Environment.writeBytes firstBytes (32*childCell) (Semantics.wordBytes (Evm.bword value).val)
    ∃ (ym z : Source.EMState E Γ) (out : Heap σ.H) (mm target : Evm.Machine)
      (offset1 offset2 : Fin Evm.W),
      (Source.execS G Fsrc (n+6) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (n+5) nps none
        (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (n+7) nps none
        (.stmt (.expr (sourceStructAssign layout sroot srhs)) (.stmt (.expr (sourceStructChildAssign layout sroot si sv)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      mid.writeAddr (.index v .dyn k) value=some out ∧
      Stmt.run σ (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))=
        .ok ⟨σ.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (σ.withHeap mid) (.assignMem (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) (.simple (.local index))) (.val (.simple (.local boolRhs))))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Prog.run σ (.cons (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))
        (.cons (.assignMem (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) (.simple (.local index))) (.val (.simple (.local boolRhs)))) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      mm=Evm.Memory.writeMachine m parentCell (.val (base v.id)) ∧
      Evm.run (structReferenceWriteCode b root rhs child) m=.ok mm 0 ∧
      Evm.run (structChildWriteCode (C := C) b root child (.simple (.local index)) (.simple (.local boolRhs))) mm=.ok target 0 ∧
      Evm.run (structReferenceWriteCode b root rhs child ++ structChildWriteCode (C := C) b root child (.simple (.local index)) (.simple (.local boolRhs))) m=.ok target 0 ∧
      SourceBoolStructAt ym a mid r address layout ∧ SourceBoolStructAt z a out r address layout ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      WordFrame target finalBytes (fun c => (base v.id).val≤c ∧ c<(base v.id).val+1+out.len v .dyn) ∧
      PointerFrame target finalBytes (fun c => c=parentCell) ∧
      offset1.val=32*parentCell ∧ offset2.val=32*childCell ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset1.val offset1.isLt::lenU (32*(base v.id).val) pointerFits::tail,bytes⟩=some ⟨tail,firstBytes⟩) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset2.val offset2.isLt::lenU (Evm.bword value).val (Evm.bword value).isLt::tail,firstBytes⟩=some ⟨tail,finalBytes⟩) ∧
      (∀ j,(j<32*parentCell ∨ 32*parentCell+32≤j) →
        (j<32*childCell ∨ 32*childCell+32≤j) → finalBytes j=bytes j) ∧
      out.field r layout.child_type=v ∧ out.field r layout.tag_type=σ.heap.field r layout.tag_type ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),v.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt ym (address q.id) mid q .dyn) ∧
      (∀ d,d≠address v.id → z.2.heap.get d=ym.2.heap.get d) ∧
      ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) := by
  dsimp only
  let mid := σ.heap.setField r layout.child_type v
  let parentCell := (base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child
  let childCell := (base v.id).val+1+k.1.toNat
  let firstBytes := Environment.writeBytes bytes (32*parentCell) (Semantics.wordBytes (32*(base v.id).val))
  let finalBytes := Environment.writeBytes firstBytes (32*childCell) (Semantics.wordBytes (Evm.bword value).val)
  obtain ⟨_,ym,mm,offset1,_,_,stmt1,typed1,code1,source1,mem1,words1,word1Eq,_,numbers1,off1,byte1,read1,exterior1,
    locals1,stack1,alloc1,tag1,child1,children1,sourceChildren1,effects1⟩ :=
    assign_struct_reference_physical layout G Fsrc (n+2) nps σ r v address initial replacement
      sroot srhs root rhs hsroot hsrhs htroot htrhs hmf SH memOK words bytes pointerLive
      (fun c => (base v.id).val≤c ∧ c<(base v.id).val+1+σ.heap.len v .dyn)
      pointers numbers slotLive pointerFits separate
  have length : mid.len v .dyn=σ.heap.len v .dyn := by
    change (MObj.elems .dyn (mid.get v)).length=_
    rw [children1]
    rfl
  have selected : (σ.withHeap mid).heap.field r layout.child_type=v := child1
  have reachedBound : k.1.toNat<(σ.withHeap mid).heap.len ((σ.withHeap mid).heap.field r layout.child_type) .dyn := by
    rw [selected]
    change k.1.toNat<mid.len v .dyn
    rw [length];exact bound
  have reachedNumbers : WordFrame mm firstBytes
      (fun c => (base ((σ.withHeap mid).heap.field r layout.child_type).id).val≤c ∧
        c<(base ((σ.withHeap mid).heap.field r layout.child_type).id).val+1+
          (σ.withHeap mid).heap.len ((σ.withHeap mid).heap.field r layout.child_type) .dyn) := by
    rw [selected]
    change WordFrame mm firstBytes (fun c => (base v.id).val≤c ∧ c<(base v.id).val+1+mid.len v .dyn)
    rw [length]
    exact numbers1
  have reachedIndex : (Val.simple (.local index) : Val C Δ .uint).evalT (σ.withHeap mid)=.ok k := by
    change Except.ok (TEnv.get index σ.env)=Except.ok k
    rw [htindex]
  have reachedValue : (Val.simple (.local boolRhs) : Val C Δ .bool).evalT (σ.withHeap mid)=.ok value := by
    change Except.ok (TEnv.get boolRhs σ.env)=Except.ok value
    rw [htvalue]
  obtain ⟨out,z,target,offset2,write2,_,_,stmt2,typed2,code2,source2,mem2,words2,physical2,off2,byte2,_,exterior2,
    _,child2,tag2,_,locals2,stack2,alloc2,other2,sourceOther2,ex2,ev2,logs2,fn2⟩ :=
    assign_struct_child_physical layout G Fsrc n nps (σ.withHeap mid) r address source1
      sroot si sv root (.simple (.local index)) (.simple (.local boolRhs)) k value
      (by rw [locals1];exact hsroot) (by rw [locals1];exact hsi) (by rw [locals1];exact hsv)
      htroot reachedIndex reachedValue hmf reachedBound SH mem1 words1 indexIn valueIn firstBytes reachedNumbers
  simp only [selected] at write2 physical2 off2 byte2 exterior2 child2 other2 sourceOther2
  have pair := source_items_pair_run G Fsrc (n+1) nps _ _ y ym z stmt1 stmt2
  have typedPair := intrinsic_heap_pair_run σ _ _ mid out typed1 typed2
  have whole : Evm.run (structReferenceWriteCode b root rhs child ++
      structChildWriteCode (C := C) b root child (.simple (.local index)) (.simple (.local boolRhs))) m=.ok target 0 := by
    rw [Evm.run_append_ok code1];exact code2
  have childDifferent : childCell≠parentCell := by
    apply separate childCell
    dsimp only [childCell]
    constructor <;> omega
  have parentWord : target.mem parentCell=.val (base v.id) := by
    have h := words2.refs r layout.child_type
    change target.mem parentCell=.val (base (out.field r layout.child_type).id) at h
    rw [child2] at h
    exact h
  have parentBytes : Environment.readMemory finalBytes (32*parentCell) 32=Semantics.wordBytes (32*(base v.id).val) := by
    rw [readMemory_write_frame]
    · exact read1
    · simp only [Environment.wordBytes_length];omega
  refine ⟨ym,z,out,mm,target,offset1,offset2,stmt1,stmt2,pair,write2,typed1,typed2,typedPair,word1Eq,code1,code2,whole,
    source1,source2,mem1,mem2,words1,words2,physical2,?_,off1,off2,byte1,byte2,?_,child2,tag2.trans tag1,
    ?_,sourceChildren1,sourceOther2,locals1,locals2.trans locals1,stack2.trans stack1,?_,?_,?_,?_,?_⟩
  · constructor
    · intro c hc;subst c;exact pointers.fits parentCell slotLive
    · intro c hc;subst c;exact ⟨base v.id,parentWord,pointerFits,parentBytes⟩
  · intro j hp hc
    exact (exterior2 j hc).trans (exterior1 j hp)
  · intro q hq
    exact (other2 q hq).trans (children1 q)
  · intro cursor positive allocator
    exact alloc2 cursor positive (alloc1 cursor positive allocator)
  · exact ex2.trans effects1.1
  · exact ev2.trans effects1.2.1
  · exact logs2.trans effects1.2.2.1
  · exact fn2.trans effects1.2.2.2

/-- info: 'Solidity.Backend.MemoryOps.Physical.assign_struct_reference_child_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assign_struct_reference_child_physical

/-- A real reference rebind survives a reached invalid child write in Source.
Intrinsic/word failures expose no invented suffix heap or returned machine;
physical evidence is exactly the successfully executed pointer-store prefix. -/
theorem assign_struct_reference_child_reject
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n nps : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (v : HRef σ.H (.array (.prim .bool)))
    (address : Nat → Nat) (initial : SourceBoolStructAt y a σ.heap r address layout)
    (replacement : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sroot : Source.Idx Γ (.struct .memory dn)) (srhs : Source.Idx Γ SourceBoolArrayTy)
    (si : Source.Idx Γ (.int .u256)) (sv : Source.Idx Γ .bool)
    (root : Idx Δ (.mem (.struct s))) (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (index : Idx Δ (.val .uint)) (boolRhs : Idx Δ (.val .bool))
    (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=.bool value)
    (htroot : TEnv.get root σ.env=some r) (htrhs : TEnv.get rhs σ.env=some v)
    (htindex : TEnv.get index σ.env=k) (htvalue : TEnv.get boolRhs σ.env=value)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (bound : σ.heap.len v .dyn≤k.1.toNat)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (words : Evm.Memory.StateRepr L b frame F σ base m)
    (indexIn : Evm.valIn (C := C) F (.simple (.local index))=true)
    (valueIn : Evm.valIn (C := C) F (.simple (.local boolRhs))=true)
    (bytes : Environment.Memory) (pointerLive : Nat → Prop)
    (pointers : PointerFrame m bytes pointerLive)
    (slotLive : pointerLive ((base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child))
    (pointerFits : 32*(base v.id).val<2^256)
 :
    let mid := σ.heap.setField r layout.child_type v
    let parentCell := (base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child
    let firstBytes := Environment.writeBytes bytes (32*parentCell) (Semantics.wordBytes (32*(base v.id).val))
    ∃ (ym : Source.EMState E Γ) (mm : Evm.Machine) (offset : Fin Evm.W),
      (Source.execS G Fsrc (n+6) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalLoc G Fsrc (n+3) (sourceStructChildLoc layout sroot si)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.evalE G Fsrc (n+4) (sourceStructChildAssign layout sroot si sv)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems G Fsrc (n+7) nps none
        (.stmt (.expr (sourceStructAssign layout sroot srhs)) (.stmt (.expr (sourceStructChildAssign layout sroot si sv)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Stmt.run σ (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))=
        .ok ⟨σ.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (σ.withHeap mid) (.assignMem (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) (.simple (.local index))) (.val (.simple (.local boolRhs))))=.error .revert ∧
      Prog.run σ (.cons (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))
        (.cons (.assignMem (.index .dyn (.loc (.field (.var root hmf) child layout.child_type)) (.simple (.local index))) (.val (.simple (.local boolRhs)))) .nil))=.error .revert ∧
      Evm.run (structReferenceWriteCode b root rhs child) m=.ok mm 0 ∧
      Evm.run (structChildWriteCode (C := C) b root child (.simple (.local index)) (.simple (.local boolRhs))) mm=.revert ∧
      Evm.run (structReferenceWriteCode b root rhs child ++ structChildWriteCode (C := C) b root child (.simple (.local index)) (.simple (.local boolRhs))) m=.revert ∧
      SourceBoolStructAt ym a mid r address layout ∧ Source.MemOK E SH ym ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      mm=Evm.Memory.writeMachine m parentCell (.val (base v.id)) ∧
      PointerFrame mm firstBytes (fun c => pointerLive c ∨ c=parentCell) ∧
      offset.val=32*parentCell ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU (32*(base v.id).val) pointerFits::tail,bytes⟩=some ⟨tail,firstBytes⟩) ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),mid.get q=σ.heap.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt ym (address q.id) mid q .dyn) ∧
      ym.1=y.1 ∧ mm.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap mid) mm ∧
      (ym.2.ex=y.2.ex ∧ ym.2.events=y.2.events ∧ ym.2.logs=y.2.logs ∧ ym.2.fnLocals=y.2.fnLocals) := by
  dsimp only
  let mid := σ.heap.setField r layout.child_type v
  let path : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.field (.var root hmf) child layout.child_type)
  let pointer : List Evm.Instr := [.mload (Evm.cellOf b root)] ++ Evm.Memory.readFieldCode (Evm.Memory.fieldOffset (Semantics.structDef s) child)
  have emptyNumbers : WordFrame m bytes (fun _ => False) := ⟨fun _ h => h.elim,fun _ h => h.elim⟩
  obtain ⟨_,ym,mm,offset,_,_,stmt1,typed1,code1,source1,mem1,words1,middle,ptr,_,off,byte,_,_,locals1,stack1,alloc1,_,selected,children,sourceChildren,effects⟩ :=
    assign_struct_reference_physical layout G Fsrc (n+2) nps σ r v address initial replacement
      sroot srhs root rhs hsroot hsrhs htroot htrhs hmf SH memOK words bytes pointerLive (fun _ => False)
      pointers emptyNumbers slotLive pointerFits (fun _ h => h.elim)
  have length : mid.len v .dyn=σ.heap.len v .dyn := by
    change (MObj.elems .dyn (mid.get v)).length=_
    rw [children];rfl
  have reachedBound : (σ.withHeap mid).heap.len ((σ.withHeap mid).heap.field r layout.child_type) .dyn≤k.1.toNat := by
    change mid.len (mid.field r layout.child_type) .dyn≤k.1.toNat
    rw [selected,length];exact bound
  have sourceError := source1.child_bounds G Fsrc n sroot si sv k value
    (by rw [locals1];exact hsroot) (by rw [locals1];exact hsi) (by rw [locals1];exact hsv) reachedBound
  have stmt2 := source_expr_statement_error G Fsrc (n+4) nps _ ym ym (.revert (Source.panicData .index)) sourceError.2
  have items := source_items_pair_error G Fsrc (n+1) nps _ _ y ym ym (.revert (Source.panicData .index)) stmt1 stmt2
  have reachedRoot : TEnv.get root (σ.withHeap mid).env=some r := htroot
  have pathRun : path.mvalT (σ.withHeap mid)=.ok v := by
    simp only [path,MPath.mvalT,MLoc.addrT,reachedRoot,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    change Except.ok (mid.field r layout.child_type)=Except.ok v
    rw [selected]
  have evalIndex : (Val.simple (.local index) : Val C Δ .uint).evalT (σ.withHeap mid)=.ok k := by
    change Except.ok (TEnv.get index σ.env)=Except.ok k
    rw [htindex]
  have evalValue : (Val.simple (.local boolRhs) : Val C Δ .bool).evalT (σ.withHeap mid)=.ok value := by
    change Except.ok (TEnv.get boolRhs σ.env)=Except.ok value
    rw [htvalue]
  have noWrite : (σ.withHeap mid).heap.writeAddr (.index v .dyn k) value=none := by
    change (if k.1.toNat<mid.len v .dyn then some _ else none)=none
    rw [length]
    exact if_neg (Nat.not_lt.mpr bound)
  have typed2 : TRun.assignMem (.index .dyn path (.simple (.local index))) (.val (.simple (.local boolRhs))) (σ.withHeap mid)=.error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,pathRun,evalIndex,evalValue,noWrite,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have fragment : Evm.Memory.PtrFrag b path pointer := .field _ _ _ (.local root hmf)
  have cert := fragment.writeArray words1 (.simple (.local index)) (.simple (.local boolRhs))
    (Evm.compileVal b (.simple (.local index))) (Evm.compileVal b (.simple (.local boolRhs)))
    (fun h' => Evm.val_sim (.simple (.local index)) h'.core indexIn)
    (Evm.val_sim (.simple (.local boolRhs)) words1.core valueIn)
  rw [typed2] at cert
  have code2 : Evm.run (structChildWriteCode (C := C) b root child (.simple (.local index)) (.simple (.local boolRhs))) mm=.revert := by
    rcases cert with ⟨_,_,bad,_⟩ | ⟨_,good⟩
    · cases bad
    · exact good
  refine ⟨ym,mm,offset,stmt1,sourceError.1,sourceError.2,items,typed1,typed2,
    intrinsic_heap_pair_error σ _ _ mid .revert typed1 typed2,code1,code2,?_,source1,mem1,words1,middle,ptr,off,byte,children,sourceChildren,locals1,stack1,alloc1,effects⟩
  rw [Evm.run_append_ok code1];exact code2

/-- info: 'Solidity.Backend.MemoryOps.Physical.assign_struct_reference_child_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assign_struct_reference_child_reject

end Solidity.Backend.MemoryOps.Physical
