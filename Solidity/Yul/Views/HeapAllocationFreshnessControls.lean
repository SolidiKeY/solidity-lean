import Solidity.Yul.Views.HeapAllocationControls

namespace Solidity.Yul.Views.Controls

/-- Actual metamodel zero-extent object. This is NOT a claim that Solidity
admits fixed-length0 arrays or that this state is execution-reachable. It
shows why owner Placement alone cannot imply strictly positive extents. -/
def haZeroData : Source.Data heapByteEnv.layout (.array .memory (.int .u256) (some 0)) :=
  .array 0 (fun _ eq => (Option.some.inj eq).symm) Fin.elim0

def haZeroHeap := (Source.Heap.empty.alloc ⟨_,haZeroData⟩).1

theorem ha_zero_only (a : Nat) (present : (haZeroHeap.cells a).isSome) : a=0 := by
  have less : a<1 := by
    apply Nat.lt_of_not_le
    intro beyond
    have no := haZeroHeap.bounded a beyond
    rw [no] at present
    cases present
  omega

def haZeroPlacement : Placement haZeroHeap where
  address _ := 128
  shape _ := .array false 0
  free := 128
  free_start := by decide
  distinct a b ha hb _ := (ha_zero_only a ha).trans (ha_zero_only b hb).symm
  typed a τ d found := by
    have present : (haZeroHeap.cells a).isSome := by rw [found]; rfl
    have only := ha_zero_only a present
    subst a
    change some (⟨_,haZeroData⟩ : Σ σ,Source.Data heapByteEnv.layout σ)=some ⟨τ,d⟩ at found
    cases found
    exact .array _ _ _
  starts _ _ := by decide
  ends _ _ := by decide
  separate a b ha hb different := False.elim (different ((ha_zero_only a ha).trans (ha_zero_only b hb).symm))

theorem ha_zero_endpoint_not_fresh :
    ¬∀ a, (haZeroHeap.cells a).isSome → haZeroPlacement.address a≠haZeroPlacement.free.val := by
  intro fresh
  exact fresh 0 rfl rfl

/-- A genuinely fresh later address extends even that placement, without a
new alignment requirement or a claim that all owner heaps have positive sizes. -/
def haAfterZero := byteAllocPlacement haZeroHeap haZeroPlacement false [] 129 161 (by decide)
  (heap_later_fresh haZeroHeap haZeroPlacement 129 (by decide)) (by decide)

theorem ha_zero_old_preserved : haAfterZero.address 0=128 ∧ haAfterZero.shape 0=.array false 0 ∧
    haAfterZero.address 1=129 ∧ haAfterZero.shape 1=.bytes 0 := ⟨rfl,rfl,rfl,rfl⟩

end Solidity.Yul.Views.Controls
