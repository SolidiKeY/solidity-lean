import Solidity.Yul.Adapters.AllocatedComputedFrame
import Solidity.Source.Semantics

/-! Actual source allocation feeds the complete computed frame and unchanged
writeback in both pipelines; nonzero unrelated tail bytes remain present. -/
namespace Solidity.Yul.Adapters.AllocatedComputedFrame.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
private def E : Source.Env := ⟨[]⟩
private def initial : Source.EMState E [] := (.nil,Source.St.init E)
private def data : Source.Data E.layout (.bytes .memory) := .bytes [17,255]
private def after := objectAllocatedState initial data
private theorem initial_ok : Source.MemOK E initial.2.heap.ty initial :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
private def C : Contract := {vars:=[]}
private def carrier (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨19,1,p,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=320,aligned:=⟨10,rfl⟩,data:=fun _=>0,highWaterWords:=10,
   resident:=by decide,zeroAbove:=by intro i hi;have bound:=i.isLt;omega}
private def residual : ByteView := mstore (fun k=>if k=319 then 170 else 0) 64 256
private theorem fits (p : Pipeline) : MemoryAgreement.Fits (carrier p) residual := by
  intro k high
  change 320≤k at high
  rw [residual,mstore_outside _ _ _ _ (by omega)]
  exact if_neg (by omega)

theorem complete_allocated_frame (pipeline : Pipeline) :
    (Source.allocRef data).run initial=(.ok (.memRef rfl 0),after) ∧
    Source.MemOK E initial.2.heap.ty after ∧
    ∃ (p : Placement after.2.heap) (image : FrameMem C []),
      ComputedFrameHeap.prepare after (carrier pipeline) residual (fits pipeline)=.ok ⟨p,image⟩ ∧
      enumeratedMemoryWriteback after p p (retainInitial _ _) (frameBytes image)=.ok (some (.ok (),after)) := by
  have supported : ∀ a τ d,initial.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
    intro a τ d found
    cases found
  obtain ⟨run,mem,p,image,prepared,coverage,nodup,raw,writeback,metadata⟩ :=
    allocation_roundtrip initial.2.heap.ty initial initial_ok data (.bytes 2) rfl (.bytes _) trivial
      supported trivial rfl (by decide) (carrier pipeline) residual (fits pipeline) (by change 192≤320;decide)
  exact ⟨run,mem,p,image,prepared,writeback⟩

private def observed (pipeline : Pipeline) : List Nat :=
  match ComputedFrameHeap.prepare after (carrier pipeline) residual (fits pipeline) with
  | .error _=>[]
  | .ok ⟨p,image⟩=>[p.address 0,p.free.val,(frameBytes image 160).toNat,
      (frameBytes image 161).toNat,(frameBytes image 319).toNat]
/-- info: [128, 192, 17, 255, 170] -/
#guard_msgs in #eval observed .legacy
/-- info: [128, 192, 17, 255, 170] -/
#guard_msgs in #eval observed .viaIR
/-- info: false -/
#guard_msgs in #eval observed .legacy==[128,192,17,255,0]
end Solidity.Yul.Adapters.AllocatedComputedFrame.Controls
