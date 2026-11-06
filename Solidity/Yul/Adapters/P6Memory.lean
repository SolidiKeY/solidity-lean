import Solidity.Backend.MemoryOps.PhysicalUintWrite
import Solidity.Backend.MemoryOps.PhysicalFrameImage
import Solidity.Source.WellTyped

/-! Consumer of the P6 physical memory interface (`Backend/MemoryOps/Physical*`). INITIAL typed Source/
array/word/byte agreement plus actual frame geometry derive the reached frame
image, source result, same-object reads and owner MemOK. FrameMem.st is an
unchanged side carrier; it is NOT identified with the changed Source/intrinsic
heap. This is not an allocator, relocation, transaction or whole-Yul theorem. -/
namespace Solidity.Yul.Adapters.P6Memory
open Solidity.Backend Solidity.Backend.MemoryOps Solidity.Backend.MemoryOps.Physical
open Solidity.Evm.TryByteImage

/-- The offset's physical W-fit comes from the INITIAL concrete WordFrame;
capacity fit is a distinct real geometry premise, never a W-fit substitute. -/
def elementSpan {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    (μ : FrameMem C Δ) (h : UintArrayAt y address hp r base m (frameBytes μ))
    (i : Fin Evm.W) (hi : i.val<hp.len r .dyn)
    (room : 32*(base.val+1+i.val)+32≤μ.capacity) : WordSpan μ.capacity :=
  ⟨lenU (32*(base.val+1+i.val)) (by
    have fits := h.physical.fits (base.val+1+i.val) ⟨by omega,by omega⟩
    change 32*(base.val+1+i.val)<2^256
    omega),room⟩

/-- Real Source write and abstract word target execution commute with the
existing typed frame store. Output relations, full byte equality, alias reads
and every-initial-H MemOK are CONCLUSIONS of the concrete producer bodies. -/
theorem write_frame {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    (μ : FrameMem C Δ) (h : UintArrayAt y address hp r base m (frameBytes μ))
    (F : Source.Fr) (fuel : Nat) (i w : Fin Evm.W) (hi : i.val<hp.len r .dyn)
    (room : 32*(base.val+1+i.val)+32≤μ.capacity) :
    let a := elementSpan μ h i hi room
    let image := store32 μ a (Evm.Memory.indexValue w)
    let next := Evm.Memory.writeMachine m (base.val+1+i.val) (.val w)
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=some out ∧
      (Source.writeLoc (E:=E) (Γ:=Γ) F fuel (.mem address i.val)
        (sourceUint (Evm.Memory.indexValue w))).run y=(.ok (),z) ∧
      Evm.run (Evm.Memory.writeArrayCode base) ((m.push (.val w)).push (.val i))=.ok next 0 ∧
      UintArrayAt z address out r base next (frameBytes image) ∧
      frameBytes image=Environment.writeBytes (frameBytes μ) (32*(base.val+1+i.val)) (Semantics.wordBytes w.val) ∧
      (∀ observer : Source.Fr, (Source.readLoc (E:=E) (Γ:=Γ) observer (τ:=.int .u256)
        (.mem address i.val)).run z=(.ok (sourceUint (Evm.Memory.indexValue w)),z)) ∧
      (∀ initial : Source.HeapTy, Source.MemOK E initial y → Source.MemOK E initial z) ∧
      z.1=y.1 ∧ z.2={y.2 with heap:=z.2.heap} ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ {Q : RefTy} (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
      (∀ k,k<32*(base.val+1+i.val) ∨ 32*(base.val+1+i.val)+32≤k → frameBytes image k=frameBytes μ k) ∧
      image.st=μ.st ∧ image.key=μ.key := by
  dsimp only
  obtain ⟨out,z,hw,hs,ht,hbyte,hnew,hl,hstate,hother,hheap,hexterior⟩ := h.write_cell F fuel i w hi
  have imageEq : frameBytes (store32 μ (elementSpan μ h i hi room) (Evm.Memory.indexValue w))=
      Environment.writeBytes (frameBytes μ) (32*(base.val+1+i.val)) (Semantics.wordBytes w.val) := by
    rw [frameBytes_store32]
    rfl
  have hout : out=hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w)) := by
    have actual : hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=
        some (hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w))) := by
      have bound : i.val<(MObj.elems .dyn (hp.get r)).length := hi
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,bound,↓reduceIte]
    exact Option.some.inj (hw.symm.trans actual)
  have selected : (MObj.elems .dyn (out.get r))[i.val]?=some (Evm.Memory.indexValue w) := by
    rw [hout,Heap.get_set_same,MObj.elems_setElem]
    exact List.getElem?_set_self hi
  refine ⟨out,z,hw,hs,ht,?_,imageEq,?_,?_,hl,hstate,hother,hheap,?_,rfl,rfl⟩
  · rw [imageEq]
    exact hnew
  · intro observer
    exact (hnew.source.read_nat_iff observer i.val (Evm.Memory.indexValue w)).mpr selected
  · intro initial ok
    have preserve := Source.writeLoc_memOK (E:=E) (Γ:=Γ) (H:=initial) F fuel
      (.mem address i.val) (sourceUint (Evm.Memory.indexValue w)) y ⟨ok,by trivial⟩
    rw [hs] at preserve
    exact preserve
  · intro k outside
    rw [imageEq]
    exact hexterior k outside

/-- Actual post-write expression evaluation through ANY retained local alias.
The owner evaluator and its horizon are used, including unchanged local index
conversion. This is not instrumentation of arbitrary recursive intermediates. -/
theorem write_eval_aliases {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    (μ : FrameMem C Δ) (h : UintArrayAt y address hp r base m (frameBytes μ))
    (G : Source.Glob E) (F : Source.Fr) (fuel n : Nat) (i w : Fin Evm.W)
    (hi : i.val<hp.len r .dyn) (room : 32*(base.val+1+i.val)+32≤μ.capacity)
    (index : Source.Idx Γ (.int .u256)) (indexed : y.1.get index=sourceUint (Evm.Memory.indexValue i)) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      (Source.writeLoc (E:=E) (Γ:=Γ) F fuel (.mem address i.val)
        (sourceUint (Evm.Memory.indexValue w))).run y=(.ok (),z) ∧
      UintArrayAt z address out r base (Evm.Memory.writeMachine m (base.val+1+i.val) (.val w))
        (frameBytes (store32 μ (elementSpan μ h i hi room) (Evm.Memory.indexValue w))) ∧
      (∀ alias : Source.Idx Γ (.array .memory (.int .u256) none),
        y.1.get alias=.memRef rfl address →
        (Source.evalE G F (n+2) (.indexArray (.local alias) (.local index) rfl)).run z=
          (.ok (.val (sourceUint (Evm.Memory.indexValue w))),z)) ∧
      (∀ initial : Source.HeapTy, Source.MemOK E initial y → Source.MemOK E initial z) := by
  obtain ⟨out,z,hw,hs,ht,hnew,hbytes,hread,hmem,hl,hstate,hother,hheap,hexterior,hcarry,hkey⟩ :=
    write_frame μ h F fuel i w hi room
  have hout : out=hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w)) := by
    have bound : i.val<(MObj.elems .dyn (hp.get r)).length := hi
    have actual : hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (Evm.Memory.indexValue w)=
        some (hp.set r (MObj.setElem .dyn (hp.get r) i.val (Evm.Memory.indexValue w))) := by
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,bound,↓reduceIte]
    exact Option.some.inj (hw.symm.trans actual)
  have length : out.len r .dyn=hp.len r .dyn := by
    rw [hout]
    simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  have valid : i.val<out.len r .dyn := by rw [length];exact hi
  have selectedOpt : (MObj.elems .dyn (out.get r))[i.val]?=some (Evm.Memory.indexValue w) := by
    rw [hout,Heap.get_set_same,MObj.elems_setElem]
    exact List.getElem?_set_self hi
  have selected : (MObj.elems .dyn (out.get r))[i.val]'valid=Evm.Memory.indexValue w :=
    Option.some.inj ((List.getElem?_eq_getElem valid).symm.trans selectedOpt)
  refine ⟨out,z,hs,hnew,?_,hmem⟩
  intro alias hlocal
  have root : z.1.get alias=.memRef rfl address := by rw [hl];exact hlocal
  have index' : z.1.get index=sourceUint (Evm.Memory.indexValue i) := by rw [hl];exact indexed
  have observed := hnew.source.eval_index G F n alias index (Evm.Memory.indexValue i) root index' valid
  simpa only [Evm.Memory.indexValue,Int.toNat_natCast,selected] using observed

/-- The actual owner out-of-bounds Source write remains its exact panic and
state. This says nothing about a byte operation outside the preparation domain. -/
theorem source_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    {bytes : Environment.Memory} (h : UintArrayAt y address hp r base m bytes)
    (F : Source.Fr) (fuel : Nat) (i : Nat) (w : Fin Evm.W) (outside : hp.len r .dyn≤i) :
    (Source.writeLoc (E:=E) (Γ:=Γ) F fuel (.mem address i) (sourceUint (Evm.Memory.indexValue w))).run y=
      (.error (.revert (Source.panicData .index)),y) :=
  source_uint_write_bounds y address _ h.source i outside (Evm.Memory.indexValue w)

/-- The producer's immutable typed snapshot observes the exact written word. -/
theorem snapshot_word {C : Contract} {Δ : Ctx} (μ : FrameMem C Δ)
    (a : WordSpan μ.capacity) (w : Fin Evm.W) :
    snapshot (store32 μ a (Evm.Memory.indexValue w))
      ⟨a.offset,lenU 32 (by decide),Or.inr a.fits⟩=Semantics.wordBytes w.val := by
  rw [frame_snapshot_read,frameBytes_store32]
  simpa only [lenU,Int.toNat_natCast,Evm.Memory.indexValue,word_bytes_length] using
    Environment.read_written (Semantics.wordBytes w.val) a.offset.val.toNat (frameBytes μ)

/-- Actual live byte REVERT reads the reached word BEFORE a separately invoked
local restoration. No Source or outer-transaction rollback is inferred. -/
theorem frame_revert {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    (μ : FrameMem C Δ) (h : UintArrayAt y address hp r base m (frameBytes μ))
    (i w : Fin Evm.W) (hi : i.val<hp.len r .dyn)
    (room : 32*(base.val+1+i.val)+32≤μ.capacity)
    (tail : List Roadmap.Word) (suffix : Backend.Program) :
    let offset : Roadmap.Word := ⟨32*(base.val+1+i.val),by
      have fits := h.physical.fits (base.val+1+i.val) ⟨by omega,by omega⟩
      omega⟩
    let image := store32 μ (elementSpan μ h i hi room) (Evm.Memory.indexValue w)
    Failure.Slice.run (.op .REVERT::suffix) ⟨offset::⟨32,by decide⟩::tail,frameBytes image⟩=
      some (⟨tail,frameBytes image⟩,some (.revert (Semantics.wordBytes w.val))) := by
  dsimp only
  have fits := h.physical.fits (base.val+1+i.val) ⟨by omega,by omega⟩
  have small : base.val+1+i.val<Evm.W := by change base.val+1+i.val<2^256;omega
  rw [frameBytes_store32]
  exact revert_written_word (frameBytes μ) ⟨base.val+1+i.val,small⟩ w fits tail suffix

end Solidity.Yul.Adapters.P6Memory
