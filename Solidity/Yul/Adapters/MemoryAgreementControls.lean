import Solidity.Yul.Adapters.MemoryAgreement

namespace Solidity.Yul.Adapters.MemoryAgreement.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
private def C : Contract := {vars:=[]}
private def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨9,1,p,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=128,aligned:=⟨4,rfl⟩,data:=fun i=>if i.val=31 then 170 else 0
   highWaterWords:=1,resident:=by decide,zeroAbove:=by
     intro i hi;have ne : i.val≠31 := by omega
     exact if_neg ne}
private def changed (p : Pipeline) : Environment.Memory :=
  fun k=>if k=7 then 255 else frameBytes (image p) k
private theorem changed_fits (p : Pipeline) : Fits (image p) (changed p) := by
  intro k hk
  have ne : k≠7 := by change 32≤k at hk;omega
  rw [changed,if_neg ne]
  exact fits_view _ k hk

theorem whole_identity (p : Pipeline) :
    writeback (image p) (frameBytes (image p)) (fits_view _)=image p := decode_encode _

theorem changed_map (p : Pipeline) :
    frameBytes (writeback (image p) (changed p) (changed_fits p))=changed p := encode_decode _ _ _

theorem padding_kept (p : Pipeline) :
    frameBytes (writeback (image p) (changed p) (changed_fits p)) 31=170 := by
  rw [changed_map]
  rfl

/-- The original fixed accounting cannot represent a newly nonzero byte32. -/
theorem old_extent_rejected (p : Pipeline) :
    ¬Fits (image p) (fun k=>if k=32 then 1 else 0) := by
  intro h
  have bad := h 32 (by change 32≤32;omega)
  change (1 : UInt8)=0 at bad
  exact (by decide : (1 : UInt8)≠0) bad

private def access (p : Pipeline) : WordSpan (image p).capacity := ⟨lenU 32 (by decide),by change 32+32≤128;omega⟩
theorem reached_extent (p : Pipeline) :
    writeback (store32 (image p) (access p) (lenU 77 (by decide)))
      (frameBytes (store32 (image p) (access p) (lenU 77 (by decide)))) (fits_view _)=
      store32 (image p) (access p) (lenU 77 (by decide)) := decode_encode _

/-- info: (255, 170, 0) -/
#guard_msgs in
#eval (frameBytes (writeback (image .legacy) (changed .legacy) (changed_fits .legacy)) 7,
  frameBytes (writeback (image .legacy) (changed .legacy) (changed_fits .legacy)) 31,
  frameBytes (writeback (image .legacy) (changed .legacy) (changed_fits .legacy)) 128)
/-- info: false -/
#guard_msgs in
#eval decide (changed .viaIR 31=0)
end Solidity.Yul.Adapters.MemoryAgreement.Controls
