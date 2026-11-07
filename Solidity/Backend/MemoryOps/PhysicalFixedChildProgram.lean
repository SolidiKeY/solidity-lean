import Solidity.Backend.MemoryOps.PhysicalFixedChildWrite

/-! Join the actual strong object/word assignment result with initial physical
parent bytes. No final byte correspondence or successful run is assumed. The
whole existing word program is proved; only its terminal byte store is covered,
not a byte-level compilation of its local/index prefix. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Join a typed word representation with preserved initial pointer bytes.
The word certificate is supplied by the actual producer in the application
below; this helper does not pretend to execute a whole byte program. -/
theorem ReferenceArrayAt.join_word_after_store {H : HTy} {R : RefTy}
    {hp out : Heap H} {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W}
    {m target : Evm.Machine} {bytes : Environment.Memory}
    (initial : ReferenceArrayAt hp root base m bytes)
    (word : Evm.Memory.RefArrayRepr out root base target) (same : out.get root=hp.get root)
    (dst : Nat) (w : Fin Evm.W) (headerNe : (base root.id).val≠dst)
    (slotsNe : ∀ c,ReferenceSlots hp root base c → c≠dst) :
    ReferenceArrayAt out root base target
      (Environment.writeBytes bytes (32*dst) (Semantics.wordBytes w.val)) := by
  first
  | solve | simp only [] | omega
  | have len : out.len root .dyn=hp.len root .dyn := by simp only [Heap.len,same]
    refine ⟨word,initial.headerFits,?_,?_,?_⟩
    · obtain ⟨v,old,read⟩ := initial.header
      refine ⟨v,?_,?_⟩
      · rw [word.length,len]
        exact initial.word.length.symm.trans old
      · rw [readMemory_write_frame]
        · exact read
        · simp only [Environment.wordBytes_length]
          omega
    · intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [len] at hi
      exact initial.pointers.fits c ⟨i,hi,eq⟩
    · intro c hc
      obtain ⟨i,hi,eq⟩ := hc
      rw [len] at hi
      have oldSlot : ReferenceSlots hp root base c := ⟨i,hi,eq⟩
      have inside : i<(MObj.elems .dyn (hp.get root)).length := hi
      let q := (MObj.elems .dyn (hp.get root))[i]'inside
      have oldHit : (MObj.elems .dyn (hp.get root))[i]?=some q := List.getElem?_eq_getElem inside
      have newHit : (MObj.elems .dyn (out.get root))[i]?=some q := by rw [same];exact oldHit
      obtain ⟨b,old,fit,read⟩ := initial.pointers.cells c oldSlot
      have oldWord : m.mem c=.val (base q.id) := by rw [eq];exact initial.word.elements i q oldHit
      have newWord : target.mem c=.val (base q.id) := by rw [eq];exact word.elements i q newHit
      have eqb : b=base q.id := Evm.Word.val.inj (old.symm.trans oldWord)
      subst b
      refine ⟨base q.id,newWord,fit,?_⟩
      rw [readMemory_write_frame]
      · exact read
      · have ne := slotsNe c oldSlot
        simp only [Environment.wordBytes_length]
        omega

/-- Consume the actual whole-word fixed assignment producer. Its existing
ownership derives physical parent-slot separation; reached word representation
then joins initial bytes. Allocation certificates are transported only from
explicit initial certificates. No compiled byte-prefix execution is claimed. -/
theorem resolved_fixed_parent_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon nps : Nat)
    (σ : State C Δ) (child : HRef σ.H (.fixed (.prim .uint) n)) (root : HRef σ.H (.array (.ref R)))
    (source : SourceUintFixedAt y address σ.heap child)
    (sr : Source.Idx Γ (.array .memory (.int .u256) (some n))) (si sv : Source.Idx Γ (.int .u256))
    (tr : Idx Δ (.mem (.fixed (.prim .uint) n))) (ti tv : Idx Δ (.val .uint)) (i w : Fin Evm.W)
    (hsr : y.1.get sr=.memRef rfl address)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue i)) (hsv : y.1.get sv=sourceUint (Evm.Memory.indexValue w))
    (htr : TEnv.get tr σ.env=some child) (hti : TEnv.get ti σ.env=Evm.Memory.indexValue i)
    (htv : TEnv.get tv σ.env=Evm.Memory.indexValue w) (hi : i.val<n)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (state : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (bytes : Environment.Memory) (parent : ReferenceArrayAt σ.heap root base m bytes)
    (fits : 32*((base child.id).val+i.val)+32≤2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    (cursor : Fin Evm.W) (hb : 0<b) (allocator : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) :
    let cell := (base child.id).val+i.val
    let byteNext := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes w.val)
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine) (offset : Fin Evm.W),
      offset.val=32*cell ∧
      σ.heap.writeAddr (.index child .fixed (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=some out ∧
      (Source.evalE G Fsrc (horizon+3) (sourceUintFixedIndexedAssign sr si sv)).run y=
        (.ok (.val (sourceUint (Evm.Memory.indexValue w))),z) ∧
      (Source.execS G Fsrc (horizon+4) nps none
        (.expr (sourceUintFixedIndexedAssign sr si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .fixed (.var tr rfl) (.simple (.local ti))) (.val (.simple (.local tv))))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.compileVal b (.simple (.local tv) : Val C Δ .uint) ++ [.mload (Evm.cellOf b tr)] ++
        Evm.compileVal b (.simple (.local ti) : Val C Δ .uint) ++
        Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))) m=.ok target 0 ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Evm.Memory.Objects.AllocatorRepr out base frame cursor target ∧
      ReferenceArrayAt out root base target byteNext ∧ CellAt target byteNext cell ∧
      SourceUintFixedAt z address out child ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,bytes⟩=some ⟨tail,byteNext⟩) ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),child.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | dsimp only
    obtain ⟨out,z,target,typed,run,expr,oldStmt,intrinsic,word,reached,strong,preserved,locals,stack,keep⟩ :=
      resolved_uint_fixed_assign_word G Fsrc horizon σ child source sr si sv tr ti tv
        (Evm.Memory.indexValue i) (Evm.Memory.indexValue w) hsr hsi hsv htr hti htv hi state SH memOK
    have stmt := source_expr_statement_run G Fsrc (horizon+3) nps _ y z (.val (sourceUint (Evm.Memory.indexValue w))) expr
    obtain ⟨_,objects,addresses,world,events,logs,fnLocals⟩ :=
      source.write_frames Fsrc (horizon+2) (Evm.Memory.indexValue i) (Evm.Memory.indexValue w) hi typed run
    have different : child.id≠root.id := by
      intro eq
      cases (HRef.heq_of_id child root eq).1
    have same := objects root different
    have separation := state.heap.owner.separated child root different
    simp only [Evm.Memory.Objects.cells] at separation
    have headerNe : (base root.id).val≠(base child.id).val+i.val := by
      rcases separation with left | right <;> omega
    have slotsNe : ∀ c,ReferenceSlots σ.heap root base c → c≠(base child.id).val+i.val := by
      intro c hc
      obtain ⟨j,hj,eq⟩ := hc
      rcases separation with left | right <;> omega
    have parentWord := (strong.heap.arrays .dyn root).reference
    have physical := parent.join_word_after_store parentWord same ((base child.id).val+i.val) w headerNe slotsNe
    have length : (MObj.elems .fixed (σ.heap.get child)).length=n := by rw [MObj.elems_fixed];exact (σ.heap.get child).2
    have canonical : σ.heap.writeAddr (.index child .fixed (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=
        some (σ.heap.set child (MObj.setElem .fixed (σ.heap.get child) i.val (Evm.Memory.indexValue w))) := by
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,length,hi,↓reduceIte]
    have outEq := Option.some.inj (typed.symm.trans canonical)
    have hit : (MObj.elems .fixed (out.get child))[i.val]?=some (Evm.Memory.indexValue w) := by
      rw [outEq,Heap.get_set_same,MObj.elems_setElem,List.getElem?_set_self (by rw [length];exact hi)]
    have value := (strong.heap.arrays .fixed child).elements i.val (Evm.Memory.indexValue w) hit
    change Evm.ReprV .uint (Evm.Memory.indexValue w) (target.mem ((base child.id).val+0+i.val)) at value
    simp only [Nat.add_zero] at value
    obtain ⟨v,stored,number⟩ := value
    change (w.val : Int)=(v.val : Int) at number
    have eqv : v=w := Fin.ext (Int.ofNat_inj.mp number.symm)
    subst v
    have cell : CellAt target (Environment.writeBytes bytes (32*((base child.id).val+i.val)) (Semantics.wordBytes w.val))
        ((base child.id).val+i.val) := by
      refine ⟨w,stored,?_⟩
      simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes w.val) (32*((base child.id).val+i.val)) bytes
    have bound : (base child.id).val+i.val<Evm.W := by change (base child.id).val+i.val<2^256;omega
    refine ⟨out,z,target,⟨32*((base child.id).val+i.val),by change 32*((base child.id).val+i.val)<2^256;omega⟩,
      rfl,typed,expr,stmt,intrinsic,word,strong,keep cursor hb allocator,physical,cell,reached,preserved,locals,stack,?_,
      objects,addresses,world,events,logs,fnLocals⟩
    intro tail
    exact byte_mstore bytes tail ⟨(base child.id).val+i.val,bound⟩ w fits

/-- info: 'Solidity.Backend.MemoryOps.Physical.resolved_fixed_parent_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_fixed_parent_word

/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.join_word_after_store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.join_word_after_store
end Solidity.Backend.MemoryOps.Physical
