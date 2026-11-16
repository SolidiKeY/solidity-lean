import Solidity.Yul.Adapters.P6ByteWriteOrder

/-! Actual typed frame controls for full write-order equality, empty spans,
overlap sensitivity and nonzero exterior bytes. These are not EVM executions
or a Source-heap realization theorem. -/
namespace Solidity.Yul.Adapters.P6ByteMemory.OrderControls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

def C : Contract := {vars:=[]}
def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨11,2,p,1,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=96,aligned:=⟨3,rfl⟩,data:=fun i=>if i.val<32 then 170 else 0
   highWaterWords:=1,resident:=by decide
   zeroAbove:=by intro i high;exact if_neg (by omega)}
def span (p : Pipeline) (offset length : Nat) (ho : offset<2^256) (hl : length<2^256)
    (fits : length=0 ∨ offset+length≤96) : ByteSpan (image p).capacity :=
  ⟨lenU offset ho,lenU length hl,by simpa only [lenU,Int.toNat_natCast] using fits⟩
def a (p : Pipeline) : ByteSpan (image p).capacity := span p 10 3 (by decide) (by decide) (Or.inr (by decide))
def b (p : Pipeline) : ByteSpan (image p).capacity := span p 40 2 (by decide) (by decide) (Or.inr (by decide))
def overlapping (p : Pipeline) : ByteSpan (image p).capacity := span p 11 2 (by decide) (by decide) (Or.inr (by decide))
def emptyInside (p : Pipeline) : ByteSpan (image p).capacity := span p 11 0 (by decide) (by decide) (Or.inl rfl)
def forward (p : Pipeline) : FrameMem C [] := writePair (image p) (a p) (b p) [255,2,7] [17,18] rfl rfl
def backward (p : Pipeline) : FrameMem C [] := writePair (image p) (b p) (a p) [17,18] [255,2,7] rfl rfl

/-- Complete frame equality for actual disjoint writes in either pipeline. -/
theorem orders (p : Pipeline) : forward p=backward p := by
  apply writePair_commute
  intro k ha hb
  change 10≤k ∧ k<10+3 at ha
  change 40≤k ∧ k<40+2 at hb
  omega

/-- An empty region inside another span adds no hidden separation restriction. -/
theorem empty_inside (p : Pipeline) :
    writePair (image p) (a p) (emptyInside p) [255,2,7] [] rfl rfl=
      writePair (image p) (emptyInside p) (a p) [] [255,2,7] rfl rfl := by
  apply writePair_commute
  intro k ha hb
  change 11≤k ∧ k<11+0 at hb
  omega

/-- info: ([255, 2, 7], [17, 18], 170, 2) -/
#guard_msgs in #eval
  ((Environment.readMemory (frameBytes (forward .legacy)) 10 3).map UInt8.toNat,
   (Environment.readMemory (frameBytes (forward .legacy)) 40 2).map UInt8.toNat,
   (frameBytes (forward .legacy) 31).toNat,(forward .legacy).highWaterWords)
/-- info: true -/
#guard_msgs in #eval decide
  ((backward .viaIR).highWaterWords=2 ∧ (backward .viaIR).key.pipeline=.viaIR)
/-- info: false -/
#guard_msgs in #eval decide
  (frameBytes (writePair (image .legacy) (a .legacy) (overlapping .legacy) [255,2,7] [17,18] rfl rfl) 11=
   frameBytes (writePair (image .legacy) (overlapping .legacy) (a .legacy) [17,18] [255,2,7] rfl rfl) 11)

/-- The final payload replaces every first payload bit in either pipeline. -/
theorem replacement (p : Pipeline) :
    writePair (image p) (a p) (a p) [255,2,7] [0,128,1] rfl rfl=
      writeSpan (image p) (a p) [0,128,1] rfl :=
  writePair_overwrite _ _ _ _ _ _

/-- info: ([0, 128, 1], 170, 1) -/
#guard_msgs in #eval
  let result := writePair (image .legacy) (a .legacy) (a .legacy) [255,2,7] [0,128,1] rfl rfl
  ((Environment.readMemory (frameBytes result) 10 3).map UInt8.toNat,
   (frameBytes result 31).toNat,result.highWaterWords)
/-- info: false -/
#guard_msgs in #eval decide
  (frameBytes (writePair (image .viaIR) (a .viaIR) (a .viaIR) [255,2,7] [0,128,1] rfl rfl) 10=255)

end Solidity.Yul.Adapters.P6ByteMemory.OrderControls
