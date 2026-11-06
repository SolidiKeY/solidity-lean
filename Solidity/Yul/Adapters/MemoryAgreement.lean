import Solidity.Yul.Adapters.P6Memory

/-! Universal byte representation agreement for the actual P6 FrameMem.
The carried intrinsic state is preserved, not decoded from bytes. -/
namespace Solidity.Yul.Adapters.MemoryAgreement
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Γ : Ctx}

/-- Exact finite representation boundary. This is a physical representation
condition, not a source admission restriction or allocator theorem. -/
def Fits (μ : FrameMem C Γ) (bytes : Environment.Memory) : Prop :=
  ∀ k, μ.highWaterWords*32≤k → bytes k=0

/-- Decode every resident and residual byte; retain all actual frame metadata.
No inverse/readback result is supplied by the caller. -/
def writeback (μ : FrameMem C Γ) (bytes : Environment.Memory) (fits : Fits μ bytes) : FrameMem C Γ :=
  { μ with data:=fun i=>bytes i.val, zeroAbove:=fun i hi=>fits i.val hi }

theorem fits_view (μ : FrameMem C Γ) : Fits μ (frameBytes μ) := by
  intro k hk
  unfold frameBytes
  split
  · exact μ.zeroAbove _ hk
  · rfl

theorem decode_encode (μ : FrameMem C Γ) : writeback μ (frameBytes μ) (fits_view μ)=μ := by
  have same : (fun i : Fin μ.capacity=>frameBytes μ i.val)=μ.data := by
    funext i
    exact dif_pos i.isLt
  unfold writeback
  simp only [same]

theorem encode_decode (μ : FrameMem C Γ) (bytes : Environment.Memory) (fits : Fits μ bytes) :
    frameBytes (writeback μ bytes fits)=bytes := by
  funext k
  unfold frameBytes writeback
  split
  · rfl
  · rename_i outside
    change ¬k<μ.capacity at outside
    exact (fits k (by have h:=μ.resident; omega)).symm

theorem unchanged (μ : FrameMem C Γ) (bytes : Environment.Memory) (fits : Fits μ bytes)
    (same : bytes=frameBytes μ) : writeback μ bytes fits=μ := by
  subst bytes
  exact decode_encode μ

theorem metadata (μ : FrameMem C Γ) (bytes : Environment.Memory) (fits : Fits μ bytes) :
    (writeback μ bytes fits).st=μ.st ∧ (writeback μ bytes fits).key=μ.key ∧
    (writeback μ bytes fits).capacity=μ.capacity ∧
    (writeback μ bytes fits).highWaterWords=μ.highWaterWords := ⟨rfl,rfl,rfl,rfl⟩

theorem reads (μ : FrameMem C Γ) (bytes : Environment.Memory) (fits : Fits μ bytes) (a n : Nat) :
    Environment.readMemory (frameBytes (writeback μ bytes fits)) a n=
      Environment.readMemory bytes a n := by rw [encode_decode]

/-- Repeated preparation retains the whole latest map and original metadata. -/
theorem overwrite (μ : FrameMem C Γ) (first second : Environment.Memory)
    (hfirst : Fits μ first) (hsecond : Fits μ second) :
    writeback (writeback μ first hfirst) second hsecond=writeback μ second hsecond := rfl

/-- Existing store32 enlarges the actual access accounting when needed.
Reconstruction uses that reached frame, never a false old high-water bound. -/
theorem stored_unchanged (μ : FrameMem C Γ) (a : WordSpan μ.capacity) (w : PrimTy.uint.Denote) :
    writeback (store32 μ a w) (Environment.writeBytes (frameBytes μ) a.offset.val.toNat
      (Semantics.wordBytes w.val.toNat))
      (by rw [←frameBytes_store32];exact fits_view _) =store32 μ a w := by
  apply unchanged
  exact (frameBytes_store32 μ a w).symm
/-- Transport ALL represented P6 arrays through an arbitrary residual-byte
change. The premise is equality of owned bytes, not a desired output relation.
All unowned bytes are retained exactly by encode_decode. -/
theorem array_residual {E : Source.Env} {Ξ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Ξ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W} {m : Evm.Machine}
    (μ : FrameMem C Γ) (initial : UintArrayAt y address hp r base m (frameBytes μ))
    (bytes : Environment.Memory) (fits : Fits μ bytes)
    (owned : ∀ cell, base.val≤cell ∧ cell<base.val+1+hp.len r .dyn →
      ∀ j, j<32 → bytes (32*cell+j)=frameBytes μ (32*cell+j)) :
    UintArrayAt y address hp r base m (frameBytes (writeback μ bytes fits)) := by
  refine ⟨initial.source,initial.words,initial.physical.fits,?_⟩
  intro cell live
  obtain ⟨w,hm,hb⟩:=initial.physical.cells cell live
  refine ⟨w,hm,?_⟩
  rw [encode_decode]
  exact (readMemory_congr (32*cell) 32 bytes (frameBytes μ) (owned cell live)).trans hb

end Solidity.Yul.Adapters.MemoryAgreement
