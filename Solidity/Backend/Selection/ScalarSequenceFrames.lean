import Solidity.Backend.Selection.ScalarSequenceResources
import Solidity.Backend.Selection.FrameCapacityV2

/-! Consume the relayed exact resource calculations through the accepted V2
frame contract. Peaks are computed from real instruction boundaries; no legacy
conditional prefix field or runtime caller-frame producer is assumed. -/
namespace Solidity.Backend.Selection.ScalarSequence
open Scalar

def boundedFrame {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1019)
    (a b u : PrimTy.uint.Denote) (s : PrimTy.int.Denote) (cmp : Bool)
    (subResult : BinOp.evalT .subW rfl a b = some u)
    (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s)
    (cmpResult : BinOp.evalT .lt rfl s zero = some cmp) :
    V2.FrameCertificate (frameTail σ spill)
      (encodeValue .bool (!cmp) :: encodeValue .int s :: frameTail σ spill) where
  code := code a b
  peak := 3
  inputRoom := by rw [frame_length]; omega
  frame := by
    intro tail
    obtain ⟨_,_,_,_,_,_,_,target⟩ := stages (C := C) (Γ := [.val .int, .val .uint])
      a b u s cmp (frameTail σ spill ++ tail) subResult subShort castResult cmpResult
    simpa only [List.cons_append] using target
  capacity := by
    intro tail admitted
    apply (capacity_iff a b _).mpr
    constructor <;> omega

def boundedCheckedFrame {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Stack) (room : spill.length ≤ 1016)
    (a b u : PrimTy.uint.Denote) (s : PrimTy.int.Denote) (cmp : Bool)
    (subResult : BinOp.evalT .subW rfl a b = some u)
    (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s)
    (cmpResult : BinOp.evalT .lt rfl s zero = some cmp) :
    V2.FrameCertificate (frameTail σ spill)
      (flag (!PrimTy.uint.inRange (a.val+b.val)) :: encodeValue .uint a ::
       encodeValue .uint b :: encodeValue .bool (!cmp) :: encodeValue .int s ::
       frameTail σ spill) where
  code := checkedCode a b
  peak := 6
  inputRoom := by rw [frame_length]; omega
  frame := by
    intro tail
    have target : run (checkedCode a b) (frameTail σ spill ++ tail) = some
        (flag (!PrimTy.uint.inRange (a.val+b.val)) :: encodeValue .uint a ::
         encodeValue .uint b :: encodeValue .bool (!cmp) :: encodeValue .int s ::
         (frameTail σ spill ++ tail)) :=
      checked_stages (C := C) (Γ := [.val .int, .val .uint])
      a b u s cmp (frameTail σ spill ++ tail) subResult subShort castResult cmpResult
    simpa only [List.cons_append] using target
  capacity := by
    intro tail admitted
    apply (checked_capacity_iff a b _).mpr
    constructor <;> omega

#print axioms boundedFrame
#print axioms boundedCheckedFrame

end Solidity.Backend.Selection.ScalarSequence
