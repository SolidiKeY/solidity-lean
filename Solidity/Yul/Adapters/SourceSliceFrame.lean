import Solidity.Yul.Adapters.P6Inputs
import Solidity.Source.Calldata

/-! Consume the EXISTING typed calldata slicing/byte producer. Physical
preparation None is separate from the owner's actual Source halt. -/
namespace Solidity.Yul.Adapters.SourceSliceFrame
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}

def consumeValue (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel : Nat) (value : Source.Val E.layout (.bytes .calldata)) (start finish : Nat) (toEnd : Bool) :
    Source.EM E Γ (Roadmap.Bytes × Option (FrameMem C Δ)) := do
  let sliced ← Source.EM.lift (Source.sliceR (D:=E.layout)
    value start finish toEnd)
  let payload ← Source.bytesOfRV F fuel (Source.RVal.val sliced)
  return (payload,if fits : payload.length=destination.length.val.toNat
    then some (P6ByteMemory.writeSpan μ destination payload fits) else none)

def consume (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel off len start finish : Nat) (toEnd : Bool) :
    Source.EM E Γ (Roadmap.Bytes × Option (FrameMem C Δ)) :=
  consumeValue μ destination F fuel (Source.Val.cdRef rfl off len) start finish toEnd

def consumeLocal (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel : Nat) (index : Source.Idx Γ (.bytes .calldata)) (start finish : Nat) (toEnd : Bool) :
    Source.EM E Γ (Roadmap.Bytes × Option (FrameMem C Δ)) := do
  let value ← Source.readLoc F (.local index)
  consumeValue μ destination F fuel value start finish toEnd

/-- Actual source local read, including aliases retained by a caller. No
historical successful index event or current ancestor length is invented. -/
theorem local_run (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel : Nat) (index : Source.Idx Γ (.bytes .calldata)) (start finish : Nat) (toEnd : Bool)
    (y : Source.EMState E Γ) (off len : Nat) (found : y.1.get index=Source.Val.cdRef rfl off len) :
    (consumeLocal μ destination F fuel index start finish toEnd).run y=
      (consume μ destination F fuel off len start finish toEnd).run y := by
  have read : (Source.readLoc F (.local index)).run y=(.ok (y.1.get index),y) := by cases y;rfl
  unfold consumeLocal
  rw [Source.Hoare.run_bind,read,found]
  rfl

/-- The exact source slice result, using the owner's stride/bounds rules. -/
theorem source_slice (off len start finish : Nat) (toEnd : Bool)
    (ordered : start≤if toEnd then len else finish) (bound : (if toEnd then len else finish)≤len) :
    Source.sliceR (D:=E.layout) (Source.Val.cdRef (τ:=.bytes .calldata) rfl off len) start finish toEnd=
      .ok (Source.Val.cdRef rfl (off+start) ((if toEnd then len else finish)-start)) := by
  change (if (if toEnd then len else finish)<start then _
    else if len<(if toEnd then len else finish) then _ else _)=_
  rw [if_neg (by omega),if_neg (by omega)]
  simp only [Nat.one_mul]
  rfl

/-- Complete producer result and unchanged Source state. Size mismatch is
successful Source evaluation plus preparation None, never an invented halt. -/
theorem consume_success (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel off len start finish : Nat) (toEnd : Bool) (y : Source.EMState E Γ)
    (ordered : start≤if toEnd then len else finish) (bound : (if toEnd then len else finish)≤len) :
    (consume μ destination F fuel off len start finish toEnd).run y=
      (.ok (let payload:=(F.cd.drop (off+start)).take ((if toEnd then len else finish)-start)
        (payload,if fits : payload.length=destination.length.val.toNat
          then some (P6ByteMemory.writeSpan μ destination payload fits) else none)),y) := by
  have sliced : (Source.EM.lift (Source.sliceR (D:=E.layout)
      (Source.Val.cdRef (τ:=.bytes .calldata) rfl off len) start finish toEnd) :
      Source.EM E Γ (Source.Val E.layout (.bytes .calldata))).run y=
      (.ok (Source.Val.cdRef rfl (off+start) ((if toEnd then len else finish)-start)),y) := by
    rw [source_slice off len start finish toEnd ordered bound]
    rfl
  unfold consume consumeValue
  rw [Source.Hoare.run_bind,sliced]
  rfl

/-- Owner errors propagate before ANY physical preparation; prior Source state
and caller prefix are unchanged in this read-only producer. -/
theorem consume_halt (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel off len start finish : Nat) (toEnd : Bool) (y : Source.EMState E Γ) (halt : Source.Halt)
    (failed : Source.sliceR (D:=E.layout)
      (Source.Val.cdRef (τ:=.bytes .calldata) rfl off len) start finish toEnd=.error halt) :
    (consume μ destination F fuel off len start finish toEnd).run y=(.error halt,y) := by
  have sliced : (Source.EM.lift (Source.sliceR (D:=E.layout)
      (Source.Val.cdRef (τ:=.bytes .calldata) rfl off len) start finish toEnd) :
      Source.EM E Γ (Source.Val E.layout (.bytes .calldata))).run y=(.error halt,y) := by
    rw [failed]
    rfl
  unfold consume consumeValue
  rw [Source.Hoare.run_bind,sliced]

theorem source_slice_error (off len start finish : Nat) (toEnd : Bool)
    (bad : (if toEnd then len else finish)<start ∨ len<(if toEnd then len else finish)) :
    Source.sliceR (D:=E.layout) (Source.Val.cdRef (τ:=.bytes .calldata) rfl off len) start finish toEnd=
      .error (.revert []) := by
  change (if (if toEnd then len else finish)<start then _
    else if len<(if toEnd then len else finish) then _ else _)=_
  rcases bad with reversed | past
  · rw [if_pos reversed]
  · by_cases reversed : (if toEnd then len else finish)<start
    · rw [if_pos reversed]
    · rw [if_neg reversed,if_pos past]

theorem consume_state (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel off len start finish : Nat) (toEnd : Bool) (y : Source.EMState E Γ) :
    ((consume μ destination F fuel off len start finish toEnd).run y).2=y := by
  by_cases ordered : start≤if toEnd then len else finish
  · by_cases bound : (if toEnd then len else finish)≤len
    · rw [consume_success μ destination F fuel off len start finish toEnd y ordered bound]
    · exact congrArg Prod.snd (consume_halt μ destination F fuel off len start finish toEnd y _
        (source_slice_error off len start finish toEnd (Or.inr (by omega))))
  · exact congrArg Prod.snd (consume_halt μ destination F fuel off len start finish toEnd y _
      (source_slice_error off len start finish toEnd (Or.inl (by omega))))

/-- Actual local producers preserve the WHOLE Source state for every result,
including owner halts and physical preparation None. -/
theorem local_state (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel : Nat) (index : Source.Idx Γ (.bytes .calldata)) (start finish : Nat) (toEnd : Bool)
    (y : Source.EMState E Γ) : ((consumeLocal μ destination F fuel index start finish toEnd).run y).2=y := by
  obtain ⟨h,off,len,found⟩:=Source.Val.cd_shape rfl (y.1.get index)
  rw [local_run μ destination F fuel index start finish toEnd y off len found]
  exact consume_state _ _ _ _ _ _ _ _ _ _

theorem local_memOK (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel : Nat) (index : Source.Idx Γ (.bytes .calldata)) (start finish : Nat) (toEnd : Bool)
    (y : Source.EMState E Γ) (initial : Source.HeapTy) (ok : Source.MemOK E initial y) :
    Source.MemOK E initial ((consumeLocal μ destination F fuel index start finish toEnd).run y).2 := by
  rw [local_state]
  exact ok

/-- Actual reference bounds imply full slice length, instead of assuming
Source.RefOK alone supplies physical provenance. -/
theorem bounded_payload_length (F : Source.Fr) (off len start finish : Nat) (toEnd : Bool)
    (reference : off+len≤F.cd.length) (ordered : start≤if toEnd then len else finish)
    (bound : (if toEnd then len else finish)≤len) :
    ((F.cd.drop (off+start)).take ((if toEnd then len else finish)-start)).length=
      (if toEnd then len else finish)-start := by
  simp only [List.length_take,List.length_drop]
  omega

/-- Concrete source/payload/physical composition with derived preparation,
complete image and readback. No final view agreement is an input. -/
theorem consume_image (μ : FrameMem C Δ) (destination : ByteSpan μ.capacity) (F : Source.Fr)
    (fuel off len start finish : Nat) (toEnd : Bool) (y : Source.EMState E Γ)
    (reference : off+len≤F.cd.length) (ordered : start≤if toEnd then len else finish)
    (bound : (if toEnd then len else finish)≤len)
    (length : destination.length.val.toNat=(if toEnd then len else finish)-start) :
    let payload:=(F.cd.drop (off+start)).take ((if toEnd then len else finish)-start)
    ∃ image : FrameMem C Δ,
      (consume μ destination F fuel off len start finish toEnd).run y=(.ok (payload,some image),y) ∧
      frameBytes image=Environment.writeBytes (frameBytes μ) destination.offset.val.toNat payload ∧
      Environment.readMemory (frameBytes image) destination.offset.val.toNat destination.length.val.toNat=payload ∧
      image.st=μ.st ∧ image.key=μ.key := by
  dsimp only
  let payload:=(F.cd.drop (off+start)).take ((if toEnd then len else finish)-start)
  have fits : payload.length=destination.length.val.toNat :=
    (bounded_payload_length F off len start finish toEnd reference ordered bound).trans length.symm
  refine ⟨P6ByteMemory.writeSpan μ destination payload fits,?_,P6ByteMemory.write_image _ _ _ _,?_,
    (P6ByteMemory.write_carrier _ _ _ _).1,(P6ByteMemory.write_carrier _ _ _ _).2⟩
  · rw [consume_success μ destination F fuel off len start finish toEnd y ordered bound]
    dsimp only
    rw [dif_pos fits]
  · rw [P6ByteMemory.write_image]
    simpa only [fits] using Environment.read_written payload destination.offset.val.toNat (frameBytes μ)

end Solidity.Yul.Adapters.SourceSliceFrame
