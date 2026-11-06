import Solidity.Yul.Adapters.P6Memory
import Solidity.Source.Semantics

namespace Solidity.Yul.Adapters.P6Memory.Controls
open Solidity.Backend Solidity.Backend.MemoryOps Solidity.Backend.MemoryOps.Physical
open Solidity.Evm.TryByteImage

private def C : Contract := {vars:=[]}
private abbrev A : Source.STy := .array .memory (.int .u256) none
private abbrev Γ : Source.RCtx := [A,A,.int .u256]
private def E : Source.Env := ⟨[]⟩
private def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
private def y0 : Source.EMState E [] := (.nil,Source.St.init E)
private def allocated := ((Source.allocRef (E:=E) (Γ:=[]) (sourceUintMemory [u 7])).run y0).2
private def source : Source.EMState E Γ :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (sourceUint (u 0)) .nil)),allocated.2)
private def F : Source.Fr := {this:=1,sender:=2,value:=0,static:=true,contract:="P6Consumer"}
private abbrev H : HTy := [.array (.prim .uint)]
private def root : HRef H (.array (.prim .uint)) := ⟨0,rfl⟩
private def hp : Heap H := (⟨[u 7],by decide⟩,())
private def m0 : Evm.Machine := {Evm.Machine.init with stack:=[.val (Evm.wmod 77)]}
private def m : Evm.Machine := Evm.Memory.writeMachine (Evm.Memory.writeMachine m0 1 (.val (Evm.wmod 1))) 2 (.val (Evm.wmod 7))
private def sentinel : Environment.Memory := fun k=>if k=127 then 170 else 0
private def bytes : Environment.Memory := Environment.writeBytes
  (Environment.writeBytes sentinel 32 (Semantics.wordBytes 1)) 64 (Semantics.wordBytes 7)
private def image : FrameMem C [] :=
  { st:=State.init C
    key:=⟨3,1,.viaIR,7,u 1,u 2,u 0⟩
    scalar:=by intro R i;cases i
    capacity:=128
    aligned:=⟨4,rfl⟩
    data:=fun i=>bytes i.val
    highWaterWords:=4
    resident:=by decide
    zeroAbove:=by intro i hi;have bound:=i.isLt;omega }

private theorem image_bytes : frameBytes image=bytes := by
  funext k
  change (if h : k<128 then bytes k else 0)=bytes k
  by_cases inside : k<128
  · exact dif_pos inside
  · rw [dif_neg inside]
    change 0=Environment.writeBytes (Environment.writeBytes sentinel 32 (Semantics.wordBytes 1)) 64 (Semantics.wordBytes 7) k
    rw [Environment.writeBytes_frame _ _ k _ (by rw [word_bytes_length];omega)]
    rw [Environment.writeBytes_frame _ _ k _ (by rw [word_bytes_length];omega)]
    change 0=(if k=127 then 170 else 0)
    rw [if_neg (by omega)]

private theorem frame : WordFrame m bytes (fun c=>(False ∨ c=1) ∨ c=2) := by
  have empty : WordFrame m0 sentinel (fun _=>False) := ⟨fun _ h=>h.elim,fun _ h=>h.elim⟩
  exact (empty.write 1 (Evm.wmod 1) (by decide)).write 2 (Evm.wmod 7) (by decide)

private theorem length : hp.len root .dyn=1 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem initial : UintArrayAt source 0 hp root (Evm.wmod 1) m (frameBytes image) := by
  rw [image_bytes]
  constructor
  · unfold SourceUintMemoryAt
    simp only [MObj.elems_dyn]
    rfl
  · refine ⟨by rw [length];decide,by rw [length];rfl,?_⟩
    intro i v value
    simp only [MObj.elems_dyn] at value
    cases i with
    | zero => cases value;exact Evm.ReprV.uint_of rfl
    | succ i => cases i <;> cases value
  · constructor
    · intro c live
      have cell : c=1 ∨ c=2 := by rw [length] at live;change 1≤c ∧ c<1+1+1 at live;omega
      rcases cell with rfl | rfl <;> decide
    · intro c live
      apply frame.cells
      rw [length] at live
      change 1≤c ∧ c<1+1+1 at live
      omega

private def i : Fin Evm.W := Evm.wmod 0
private def w : Fin Evm.W := Evm.wMax
private theorem valid : i.val<hp.len root .dyn := by rw [length];decide
private theorem room : 32*((Evm.wmod 1).val+1+i.val)+32≤image.capacity := by decide
private def span := elementSpan image initial i valid room
private def after := store32 image span (Evm.Memory.indexValue w)

/-- Both actual source locals alias the SAME allocated object; the real owner
expression evaluator sees the maximum word through each after the real write.
The static source frame still permits memory writes, as its owner specifies. -/
theorem two_local_aliases (G : Source.Glob E) (n : Nat) :
    ∃ out : Source.EMState E Γ,
      (Source.writeLoc F 0 (.mem 0 0) (sourceUint (Evm.Memory.indexValue w))).run source=(.ok (),out) ∧
      (Source.evalE G F (n+2) (.indexArray (.local .here) (.local (.there (.there .here))) rfl)).run out=
        (.ok (.val (sourceUint (Evm.Memory.indexValue w))),out) ∧
      (Source.evalE G F (n+2) (.indexArray (.local (.there .here)) (.local (.there (.there .here))) rfl)).run out=
        (.ok (.val (sourceUint (Evm.Memory.indexValue w))),out) ∧
      (∀ original : Source.HeapTy, Source.MemOK E original source → Source.MemOK E original out) := by
  obtain ⟨out,z,write,repr,aliases,mem⟩ := write_eval_aliases image initial G F 0 n i w valid room
    (.there (.there .here)) rfl
  exact ⟨z,write,aliases .here rfl,aliases (.there .here) rfl,mem⟩

theorem source_initial_MemOK : Source.MemOK E source.2.heap.ty source := by
  have start : Source.MemOK E y0.2.heap.ty y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have keep := source_uint_alloc_memOK (E:=E) (Γ:=[]) y0.2.heap.ty [u 7] y0 start
  have allocatedOK : Source.MemOK E y0.2.heap.ty allocated := keep.1
  have self := allocatedOK.self
  refine ⟨⟨self.1.1,?_⟩,self.2⟩
  exact ⟨⟨A,rfl,rfl⟩,⟨⟨A,rfl,rfl⟩,trivial,trivial⟩⟩

theorem exact_word_and_neighbors :
    snapshot after ⟨span.offset,lenU 32 (by decide),Or.inr span.fits⟩=Semantics.wordBytes w.val ∧
    Environment.readMemory (frameBytes after) 32 32=Semantics.wordBytes 1 ∧
    frameBytes after 127=frameBytes image 127 ∧
    after.st=image.st ∧ after.key=image.key := by
  refine ⟨snapshot_word image span w,?_,?_,rfl,rfl⟩
  · unfold after
    rw [frameBytes_store32]
    have byteOffset : span.offset.val.toNat=64 := rfl
    rw [byteOffset,readMemory_write_frame _ 32 32 64 _ (by decide),image_bytes]
    change Environment.readMemory (Environment.writeBytes (Environment.writeBytes sentinel 32
      (Semantics.wordBytes 1)) 64 (Semantics.wordBytes 7)) 32 32=_
    rw [readMemory_write_frame _ 32 32 64 _ (by decide)]
    simpa only [word_bytes_length] using Environment.read_written (Semantics.wordBytes 1) 32 sentinel
  · unfold after
    rw [frameBytes_store32]
    apply Environment.writeBytes_frame
    rw [word_bytes_length]
    change 127<64 ∨ 64+32≤127
    decide

theorem live_revert (suffix : Backend.Program) :
    Failure.Slice.run (.op .REVERT::suffix)
      ⟨[⟨64,by decide⟩,⟨32,by decide⟩,⟨77,by decide⟩],frameBytes after⟩=
      some (⟨[⟨77,by decide⟩],frameBytes after⟩,some (.revert (Semantics.wordBytes w.val))) :=
  frame_revert image initial i w valid room [⟨77,by decide⟩] suffix

theorem actual_bounds :
    (Source.writeLoc F 0 (.mem 0 1) (sourceUint (Evm.Memory.indexValue w))).run source=
      (.error (.revert (Source.panicData .index)),source) :=
  source_bounds initial F 0 1 w (by rw [length];decide)

theorem stale_bytes_are_wrong : Environment.readMemory (frameBytes image) 64 32≠Semantics.wordBytes w.val := by
  rw [image_bytes]
  change Environment.readMemory (Environment.writeBytes _ 64 (Semantics.wordBytes 7)) 64 32≠_
  have live := Environment.read_written (Semantics.wordBytes 7) 64 (Environment.writeBytes sentinel 32 (Semantics.wordBytes 1))
  simp only [word_bytes_length] at live
  rw [live]
  decide

theorem nonzero_exterior : frameBytes image 127=170 ∧ frameBytes after 127=170 := by
  have before : frameBytes image 127=170 := by
    rw [image_bytes]
    change Environment.writeBytes (Environment.writeBytes sentinel 32 (Semantics.wordBytes 1))
      64 (Semantics.wordBytes 7) 127=170
    rw [Environment.writeBytes_frame _ _ 127 _ (by rw [word_bytes_length];decide)]
    rw [Environment.writeBytes_frame _ _ 127 _ (by rw [word_bytes_length];decide)]
    rfl
  exact ⟨before,exact_word_and_neighbors.2.2.1.trans before⟩

theorem wrong_unscaled_span : span.offset.val.toNat≠2 := by decide

theorem separate_carrier_heap : image.st.H=[] ∧ H=[.array (.prim .uint)] := ⟨rfl,rfl⟩

end Solidity.Yul.Adapters.P6Memory.Controls
