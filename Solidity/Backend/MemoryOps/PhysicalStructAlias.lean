import Solidity.Backend.MemoryOps.PhysicalPointerFrame
import Solidity.Backend.MemoryOps.SourceStructAlias

/-! Selecting a named member into an existing reference LOCAL. This consumes
published Source/intrinsic/whole-word rebind code, not a pointer compiler or
constructor. Scaled component MSTORE is separate from the whole word path. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- INITIAL named correspondence determines the same selected child at both
layers. Only the destination local/pointer bytes change; heaps are not copied.
The initial pointer footprint supplies nonwrapping bounds for the real store. -/
theorem select_struct_alias_physical
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n nps : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (initial : SourceBoolStructAt y a σ.heap r address layout)
    (sdst : Source.Idx Γ SourceBoolArrayTy) (sroot : Source.Idx Γ (.struct .memory dn))
    (dst : Idx Δ (.mem (.array (.prim .bool)))) (root : Idx Δ (.mem (.struct s)))
    (hsroot : y.1.get sroot=.memRef rfl a) (htroot : TEnv.get root σ.env=some r)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (words : Evm.Memory.StateRepr L b frame F σ base m)
    (bytes : Environment.Memory) (pointerLive numericLive : Nat → Prop)
    (pointers : PointerFrame m bytes pointerLive) (numbers : WordFrame m bytes numericLive)
    (selected : pointerLive (Evm.cellOf b dst))
    (valueFits : 32*(base (σ.heap.field r layout.child_type).id).val<2^256)
    (separate : ∀ c,numericLive c → c≠Evm.cellOf b dst) :
    let q := σ.heap.field r layout.child_type
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl (address q.id)),y.2)
    let st := σ.setLocal dst (some q)
    let target := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base q.id))
    let afterBytes := Environment.writeBytes bytes (32*Evm.cellOf b dst) (Semantics.wordBytes (32*(base q.id).val))
    (Source.evalE G Fsrc (n+3) (sourceStructSelectedAlias layout sdst sroot)).run y=
      (.ok (.val (.memRef rfl (address q.id))),z) ∧
    (Source.execS G Fsrc (n+4) nps none
      (.expr (sourceStructSelectedAlias layout sdst sroot) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.alias (.loc (.field (.var root hmf) child layout.child_type))))=
      .ok ⟨st,List.prefix_refl _⟩ ∧
    Evm.run (structSelectedAliasCode b dst root child) m=.ok target 0 ∧
    SourceBoolStructAt z a st.heap r address layout ∧ SourceBoolMemoryAt z (address q.id) st.heap q .dyn ∧
    Source.MemOK E SH z ∧ Evm.Memory.StateRepr L b frame F st base target ∧
    PointerFrame target afterBytes (fun c => pointerLive c ∨ c=Evm.cellOf b dst) ∧
    WordFrame target afterBytes numericLive ∧
    (∃ offset : Fin Evm.W,offset.val=32*Evm.cellOf b dst ∧
      ∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU (32*(base q.id).val) valueFits::tail,bytes⟩=
          some ⟨tail,afterBytes⟩) ∧
    Environment.readMemory afterBytes (32*Evm.cellOf b dst) 32=Semantics.wordBytes (32*(base q.id).val) ∧
    (∀ j,j<32*Evm.cellOf b dst ∨ 32*Evm.cellOf b dst+32≤j → afterBytes j=bytes j) ∧
    z.2=y.2 ∧ st.heap=σ.heap ∧ z.1.get sdst=.memRef rfl (address q.id) ∧ TEnv.get dst st.env=some q ∧
    target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m st target := by
  dsimp only
  let q := σ.heap.field r layout.child_type
  let cell := Evm.cellOf b dst
  have fit : 32*cell+32≤2^256 := pointers.fits cell selected
  have logicalFit : cell<Evm.W := by change cell<2^256;omega
  obtain ⟨he,_,hi,hw,hr,hchild,hm,hstate,_,_,hl,ht,hstack,halloc⟩ :=
    initial.selected_alias_word layout G Fsrc n σ r address sdst sroot dst root hsroot htroot hmf SH memOK words
  have statement := source_expr_statement_run G Fsrc (n+3) nps _ y _ (.val (.memRef rfl (address q.id))) he
  refine ⟨he,statement,hi,hw,hr,hchild,hm,hstate,pointers.write cell (base q.id) fit valueFits,
    numbers.pointer_write cell (base q.id) separate,⟨⟨32*cell,by change 32*cell<2^256;omega⟩,rfl,?_⟩,?_,?_,rfl,rfl,hl,ht,hstack,halloc⟩
  · intro tail
    exact byte_mstore bytes tail ⟨cell,logicalFit⟩ ⟨32*(base q.id).val,valueFits⟩ fit
  · simpa only [Environment.wordBytes_length] using Environment.read_written
      (Semantics.wordBytes (32*(base q.id).val)) (32*cell) bytes
  · intro j hj
    exact Environment.writeBytes_frame _ _ j _ (by simpa only [Environment.wordBytes_length] using hj)

/-- info: 'Solidity.Backend.MemoryOps.Physical.select_struct_alias_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms select_struct_alias_physical
end Solidity.Backend.MemoryOps.Physical
