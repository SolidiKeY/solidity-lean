import Solidity.Yul.Adapters.P6ByteMemory
import Solidity.Yul.RawBoundary
import Solidity.Source.Observe

/-! Physical byte transport for the existing H11 raw LOCAL frame. Store/load
never clean or overwrite intrinsic Source locals. The total read is a byte-view
operation; no emitted MLOAD, allocation, storage dirty-word or pipeline adequacy
is inferred. Readback boundaries remain the explicit existing RawBoundary APIs. -/
namespace Solidity.Yul.Adapters.RawPhysical
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Γ : Ctx} {ctx : Source.Ctx}

def span (μ : FrameMem C Γ) (a : WordSpan μ.capacity) : ByteSpan μ.capacity :=
  ⟨a.offset,lenU 32 (by decide),Or.inr a.fits⟩

def store (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) : FrameMem C Γ :=
  P6ByteMemory.writeSpan μ (span μ a) (Source.wordBytes (RawFrame.view state cell))
    (Source.wordBytes_length _)

def readWord (μ : FrameMem C Γ) (offset : Nat) : Word :=
  Source.toWord (Source.beValue (Environment.readMemory (frameBytes μ) offset 32))

def load (μ : FrameMem C Γ) (offset : Nat) (state : RawFrame.State ctx)
    (cell : WordCell (localExternalTypes ctx)) : RawFrame.State ctx :=
  RawFrame.write state cell (readWord μ offset)
/-- Every original raw bit is retained, without canonical narrowing. -/
theorem read_store {C : Contract} {Γ : Ctx} {ctx : Source.Ctx}
    (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (state : RawFrame.State ctx)
    (cell : WordCell (localExternalTypes ctx)) :
    readWord (store μ a state cell) a.offset.val.toNat=RawFrame.view state cell := by
  unfold readWord store
  rw [P6ByteMemory.write_image]
  dsimp only [span]
  have bytes := Environment.read_written (Source.wordBytes (RawFrame.view state cell))
    a.offset.val.toNat (frameBytes μ)
  simp only [Source.wordBytes_length] at bytes
  rw [bytes,Source.wordBytes_value]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (RawFrame.view state cell).isLt

/-- Actual RawFrame.write records an overlay; clean values/world stay separate. -/
theorem load_fields (μ : FrameMem C Γ) (offset : Nat) (state : RawFrame.State ctx)
    (cell : WordCell (localExternalTypes ctx)) :
    (load μ offset state cell).clean=state.clean ∧
    (load μ offset state cell).world=state.world ∧
    (load μ offset state cell).raw cell=some (readWord μ offset) := by
  exact ⟨rfl,rfl,if_pos rfl⟩

theorem load_view (μ : FrameMem C Γ) (offset : Nat) (state : RawFrame.State ctx)
    (cell : WordCell (localExternalTypes ctx)) :
    RawFrame.view (load μ offset state cell) cell=readWord μ offset :=
  RawFrame.read_write _ _ _

theorem load_other (μ : FrameMem C Γ) (offset : Nat) (state : RawFrame.State ctx)
    (cell other : WordCell (localExternalTypes ctx)) (different : other≠cell) :
    RawFrame.view (load μ offset state cell) other=RawFrame.view state other := by
  unfold load
  rw [RawFrame.view_write]
  exact WordCells.write_other _ _ _ _ different

/-- A view roundtrip, deliberately NOT whole RawFrame administrative identity:
a previously absent overlay is recorded by the actual write operation. -/
theorem view_roundtrip (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) :
    RawFrame.view (load (store μ a state cell) a.offset.val.toNat state cell)=RawFrame.view state := by
  funext other
  by_cases same : other=cell
  · subst other
    rw [load_view,read_store]
  · exact load_other _ _ _ _ _ same

theorem store_image (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) :
    frameBytes (store μ a state cell)=Environment.writeBytes (frameBytes μ)
      a.offset.val.toNat (Source.wordBytes (RawFrame.view state cell)) :=
  P6ByteMemory.write_image _ _ _ _

theorem store_carrier (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx)) :
    (store μ a state cell).st=μ.st ∧ (store μ a state cell).key=μ.key :=
  P6ByteMemory.write_carrier _ _ _ _

/-- Equality of existing Source and backend encoders, not a new encoder or
storage-packing alignment policy. Width is the real codec parameter. -/
theorem source_bytes_map (width n : Nat) :
    Source.beBytes width n=(List.range width).map (fun i=>UInt8.ofNat (n/256^(width-1-i))) := by
  induction width generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [Source.beBytes,ih,List.range_succ,List.map_append,List.map_singleton]
    congr 1
    · apply List.map_congr_left
      intro i member
      have hi : i<k := List.mem_range.mp member
      have power : 256*256^(k-1-i)=256^(k-i) := by
        have exp : k-i=(k-1-i)+1 := by omega
        rw [exp,Nat.pow_succ,Nat.mul_comm]
      simp only [Nat.add_sub_cancel,Nat.div_div_eq_div_mul,power]
    · simp only [Nat.add_sub_cancel,Nat.sub_self,Nat.pow_zero,Nat.div_one]
      apply congrArg List.singleton
      apply UInt8.toNat_inj.1
      change (n%256)%256=n%256
      exact Nat.mod_mod _ _
theorem source_backend_wordBytes (w : Word) : Source.wordBytes w=Semantics.wordBytes w.val := by
  rw [Source.wordBytes,source_bytes_map]
  unfold Semantics.wordBytes
  apply List.map_congr_left
  intro i member
  apply UInt8.toNat_inj.1
  change (w.val/256^(31-i))%256=((w.val/256^(31-i))%256)%256
  exact (Nat.mod_mod _ _).symm

/-- The actual published byte-addressed MSTORE consumes the raw word and
preserves the caller stack tail, producing the COMPLETE reached byte image.
This is an instruction slice, without a gas or source/compiler claim. -/
theorem store_target (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (state : RawFrame.State ctx) (cell : WordCell (localExternalTypes ctx))
    (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨a.offset::lenU (RawFrame.view state cell).val (RawFrame.view state cell).isLt::tail,frameBytes μ⟩=
      some ⟨tail,frameBytes (store μ a state cell)⟩ := by
  rw [store_image,source_backend_wordBytes]
  rfl

/-- An actual numeric CellAt supplies the same full word to the raw-local
byte reader. This helper alone has no physical capacity or no-wrap claim. -/
theorem read_cell {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ) (m : Evm.Machine) (cell : Nat)
    (initial : CellAt m (frameBytes μ) cell) :
    ∃ w : Word,m.mem cell=.val w ∧ readWord μ (32*cell)=w := by
  obtain ⟨w,word,bytes⟩ := initial
  refine ⟨w,word,?_⟩
  unfold readWord
  rw [bytes,←source_backend_wordBytes w,Source.wordBytes_value]
  apply Fin.ext
  exact Nat.mod_eq_of_lt w.isLt

/-- Consume the actual regional P6 WordFrame: derive nonwrapping byte span,
actual fixed-cell word-machine load and raw-local observation together.
The32 scaling is explicit, and the physical relation survives the load.
External byte-machine allocation/gas and macro refinement remain separate. -/
theorem load_frame {C : Contract} {Γ : Ctx} {ctx : Source.Ctx}
    (μ : FrameMem C Γ) (m : Evm.Machine) (live : Nat → Prop)
    (initial : WordFrame m (frameBytes μ) live) (cell : Nat) (owned : live cell)
    (room : 32*cell+32≤μ.capacity) (state : RawFrame.State ctx)
    (target : WordCell (localExternalTypes ctx)) :
    ∃ a : WordSpan μ.capacity,a.offset.val.toNat=32*cell ∧ ∃ w : Word,
      (Evm.Instr.mload cell).step m=.ok {m with stack:=.val w::m.stack} 0 ∧
      RawFrame.view (load μ a.offset.val.toNat state target) target=w ∧
      (load μ a.offset.val.toNat state target).raw target=some w ∧
      (load μ a.offset.val.toNat state target).clean=state.clean ∧
      (load μ a.offset.val.toNat state target).world=state.world ∧
      WordFrame {m with stack:=.val w::m.stack} (frameBytes μ) live := by
  let a : WordSpan μ.capacity := ⟨lenU (32*cell) (by have bound := initial.fits cell owned;omega),room⟩
  obtain ⟨w,word,read⟩ := read_cell μ m cell (initial.cells cell owned)
  refine ⟨a,rfl,w,?_,?_,?_,rfl,rfl,⟨initial.fits,initial.cells⟩⟩
  · change Evm.Out.ok {m with stack:=m.mem cell::m.stack} 0=_
    rw [word]
  · rw [load_view]
    exact read
  · have fields := load_fields μ (32*cell) state target
    rw [read] at fields
    exact fields.2.2

end Solidity.Yul.Adapters.RawPhysical
