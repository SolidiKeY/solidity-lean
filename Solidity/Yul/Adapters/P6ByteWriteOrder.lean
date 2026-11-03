import Solidity.Yul.Adapters.P6ByteMemory

/-! Composition of actual bounded P6 byte writes. Span capacity is transported
by the existing write_capacity theorem. No new state, instruction semantics,
allocation policy or Source-heap identification is introduced. -/
namespace Solidity.Yul.Adapters.P6ByteMemory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Γ : Ctx}

/-- Two real writes with the second span retained at its original coordinates. -/
def writePair (μ : FrameMem C Γ) (first second : ByteSpan μ.capacity)
    (left right : List UInt8) (hl : left.length=first.length.val.toNat)
    (hr : right.length=second.length.val.toNat) : FrameMem C Γ :=
  writeSpan (writeSpan μ first left hl)
    ⟨second.offset,second.length,by rw [write_capacity];exact second.fits⟩ right hr

/-- Extensionality of the existing full typed frame, including logical carrier
and access metadata. Byte equality alone deliberately does not suffice. -/
theorem frame_eq_of_fields (a b : FrameMem C Γ) (state : a.st=b.st) (key : a.key=b.key)
    (capacity : a.capacity=b.capacity) (high : a.highWaterWords=b.highWaterWords)
    (image : frameBytes a=frameBytes b) : a=b := by
  cases a with
  | mk sa ka sca ca aa da ha ra za =>
    cases b with
    | mk sb kb scb cb ab db hb rb zb =>
      cases state
      cases key
      cases capacity
      cases high
      have data : da=db := by
        funext i
        have byte := congrFun image i.val
        simpa only [frameBytes,dif_pos i.isLt] using byte
      cases data
      rfl

/-- Empty accesses contribute no newly accessed words, irrespective of offset. -/
def accessedWords {capacity : Nat} (s : ByteSpan capacity) : Nat :=
  if s.length.val.toNat=0 then 0 else (s.offset.val.toNat+s.length.val.toNat+31)/32

/-- Exact existing write accounting, without a gas or allocation interpretation. -/
theorem write_highWater (μ : FrameMem C Γ) (s : ByteSpan μ.capacity) (bytes : List UInt8) (length) :
    (writeSpan μ s bytes length).highWaterWords=max μ.highWaterWords (accessedWords s) := by
  unfold writeSpan accessedWords
  split <;> simp only [Nat.max_zero]

/-- Exact complete carriers, byte image and access accounting after both writes. -/
theorem writePair_fields (μ : FrameMem C Γ) (a b : ByteSpan μ.capacity)
    (xs ys : List UInt8) (hx : xs.length=a.length.val.toNat) (hy : ys.length=b.length.val.toNat) :
    (writePair μ a b xs ys hx hy).st=μ.st ∧
    (writePair μ a b xs ys hx hy).key=μ.key ∧
    (writePair μ a b xs ys hx hy).capacity=μ.capacity ∧
    frameBytes (writePair μ a b xs ys hx hy)=
      Environment.writeBytes (Environment.writeBytes (frameBytes μ) a.offset.val.toNat xs) b.offset.val.toNat ys ∧
    (writePair μ a b xs ys hx hy).highWaterWords=
      max (max μ.highWaterWords (accessedWords a)) (accessedWords b) := by
  let later : ByteSpan (writeSpan μ a xs hx).capacity := ⟨b.offset,b.length,by rw [write_capacity];exact b.fits⟩
  have first := write_carrier μ a xs hx
  have second := write_carrier (writeSpan μ a xs hx) later ys hy
  refine ⟨second.1.trans first.1,second.2.trans first.2,?_,?_,?_⟩
  · exact (write_capacity (writeSpan μ a xs hx) later ys hy).trans (write_capacity μ a xs hx)
  · unfold writePair
    rw [write_image,write_image]
  · unfold writePair
    rw [write_highWater,write_highWater]
    rfl

/-- Disjoint actual byte regions commute on the COMPLETE frame, including
high-water metadata. Empty regions are included without an offset restriction. -/
theorem writePair_commute (μ : FrameMem C Γ) (a b : ByteSpan μ.capacity)
    (xs ys : List UInt8) (hx : xs.length=a.length.val.toNat) (hy : ys.length=b.length.val.toNat)
    (separate : ∀ k,a.offset.val.toNat≤k ∧ k<a.offset.val.toNat+a.length.val.toNat →
      ¬(b.offset.val.toNat≤k ∧ k<b.offset.val.toNat+b.length.val.toNat)) :
    writePair μ a b xs ys hx hy=writePair μ b a ys xs hy hx := by
  have left := writePair_fields μ a b xs ys hx hy
  have right := writePair_fields μ b a ys xs hy hx
  apply frame_eq_of_fields _ _ (left.1.trans right.1.symm) (left.2.1.trans right.2.1.symm) (left.2.2.1.trans right.2.2.1.symm)
  · rw [left.2.2.2.2,right.2.2.2.2]
    omega
  · rw [left.2.2.2.1,right.2.2.2.1]
    apply MemoryBytes.write_commute
    simpa only [hx,hy] using separate

/-- Replacing the same bounded span twice equals just its final write on the
complete frame. Access metadata is idempotent, including empty spans. -/
theorem writePair_overwrite (μ : FrameMem C Γ) (s : ByteSpan μ.capacity)
    (xs ys : List UInt8) (hx : xs.length=s.length.val.toNat) (hy : ys.length=s.length.val.toNat) :
    writePair μ s s xs ys hx hy=writeSpan μ s ys hy := by
  have pair := writePair_fields μ s s xs ys hx hy
  have final := write_carrier μ s ys hy
  apply frame_eq_of_fields _ _ (pair.1.trans final.1.symm)
    (pair.2.1.trans final.2.symm) (pair.2.2.1.trans (write_capacity μ s ys hy).symm)
  · rw [pair.2.2.2.2,write_highWater]
    omega
  · rw [pair.2.2.2.1,write_image]
    exact MemoryBytes.write_overwrite _ _ xs ys (hx.trans hy.symm)

end Solidity.Yul.Adapters.P6ByteMemory
