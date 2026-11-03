import Solidity.Backend.MemoryOps.PhysicalPointerFrame
import Solidity.Backend.MemoryOps.SourceStructAssignment

/-! Named reference-member rebinding connects the ACTUAL published Source,
intrinsic and whole-word operation to the existing scaled pointer-byte store.
Initial selected-pointer and numeric frames are explicit; child identities may
be shared. No allocator, decoder, reference constructor, physical child
liveness or whole pointer-prefix byte execution is introduced. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- The same reached Source/word states supply the pointer update and frames.
The initial named slot image is derived from StateRepr and PointerFrame, while
its physical fit follows from its initial live membership. -/
theorem assign_struct_reference_physical
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n nps : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (v : HRef σ.H (.array (.prim .bool)))
    (address : Nat → Nat) (hr : SourceBoolStructAt y a σ.heap r address layout)
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sroot : Source.Idx Γ (.struct .memory dn)) (srhs : Source.Idx Γ SourceBoolArrayTy)
    (root : Idx Δ (.mem (.struct s))) (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (hsroot : y.1.get sroot=.memRef rfl a) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (htroot : TEnv.get root σ.env=some r) (htrhs : TEnv.get rhs σ.env=some v)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (bytes : Environment.Memory) (pointerLive numericLive : Nat → Prop)
    (pointers : PointerFrame m bytes pointerLive) (numbers : WordFrame m bytes numericLive)
    (slotLive : pointerLive ((base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child))
    (pointerFits : 32*(base v.id).val<2^256)
    (separate : ∀ cell,numericLive cell → cell≠(base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child) :
    let out := σ.heap.setField r layout.child_type v
    let cell := (base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child
    let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes (32*(base v.id).val))
    Environment.readMemory bytes (32*cell) 32=
      Semantics.wordBytes (32*(base (σ.heap.field r layout.child_type).id).val) ∧
    ∃ (z : Source.EMState E Γ) (target : Evm.Machine) (offset : Fin Evm.W),
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem (τ := SourceBoolArrayTy) a 1)
        (.memRef rfl (address v.id))).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceStructAssign layout sroot srhs)).run y=
        (.ok (.val (.memRef rfl (address v.id))),z) ∧
      (Source.execS G Fsrc (n+4) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structReferenceWriteCode b root rhs child) m=.ok target 0 ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      target=Evm.Memory.writeMachine m cell (.val (base v.id)) ∧
      PointerFrame target byteNext (fun c => pointerLive c ∨ c=cell) ∧
      WordFrame target byteNext numericLive ∧
      offset.val=32*cell ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU (32*(base v.id).val) pointerFits::tail,bytes⟩=
          some ⟨tail,byteNext⟩) ∧
      Environment.readMemory byteNext (32*cell) 32=Semantics.wordBytes (32*(base v.id).val) ∧
      (∀ j,j<32*cell ∨ 32*cell+32≤j → byteNext j=bytes j) ∧
      z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      out.field r layout.tag_type=σ.heap.field r layout.tag_type ∧ out.field r layout.child_type=v ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),out.get q=σ.heap.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) := by
  dsimp only
  let cell := (base r.id).val+Evm.Memory.fieldOffset (Semantics.structDef s) child
  have fits : 32*cell+32≤2^256 := pointers.fits cell slotLive
  have hc : cell<Evm.W := by change cell<2^256;omega
  obtain ⟨old,hold,_,hbytes⟩ := pointers.cells cell slotLive
  have sameOld : old=base (σ.heap.field r layout.child_type).id :=
    Evm.Word.val.inj (hold.symm.trans (hm.refs r layout.child_type))
  subst old
  refine ⟨hbytes,?_⟩
  obtain ⟨z,target,hs,he,_,hi,hw,hr',hmk,hstate,hl,hstack,ht,halloc,htag,hchild,hchildren,hsource,heffects⟩ :=
    hr.resolved_assign_word layout G Fsrc n σ r v address hv sroot srhs root rhs
      hsroot hsrhs htroot htrhs hmf SH hmem hm
  have hstmt := source_expr_statement_run G Fsrc (n+3) nps _ y z (.val (.memRef rfl (address v.id))) he
  refine ⟨z,target,⟨32*cell,by change 32*cell<2^256;omega⟩,hs,he,hstmt,hi,hw,hr',hmk,hstate,ht,?_,?_,rfl,?_,?_,?_,hl,hstack,halloc,htag,hchild,hchildren,hsource,heffects⟩
  · rw [ht]
    exact pointers.write cell (base v.id) fits pointerFits
  · rw [ht]
    exact numbers.pointer_write cell (base v.id) separate
  · intro tail
    exact byte_mstore bytes tail ⟨cell,hc⟩ ⟨32*(base v.id).val,pointerFits⟩ fits
  · simpa only [Environment.wordBytes_length] using Environment.read_written
      (Semantics.wordBytes (32*(base v.id).val)) (32*cell) bytes
  · intro j hj
    apply Environment.writeBytes_frame
    simpa only [Environment.wordBytes_length] using hj

/-- info: 'Solidity.Backend.MemoryOps.Physical.assign_struct_reference_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assign_struct_reference_physical

end Solidity.Backend.MemoryOps.Physical
