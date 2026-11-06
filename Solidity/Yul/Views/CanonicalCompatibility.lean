import Solidity.Yul.Views.CanonicalRetained

/-! Exact all-raw-input compatibility on the old component domain. No verdict,
None/error/state result is discarded. These are real API equalities, not full
Yul/source/compiler adequacy or a renamed residual coverage predicate. -/
namespace Solidity.Yul.Views

theorem decodeExtendedMemoryMember_legacy {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (supported : OrdinaryMemberType τ) (word : Roadmap.Word) :
    decodeExtendedMemoryMember p es τ word = decodeMemoryMember p es τ word := by
  rcases supported with eq | eq | loc
  · subst τ
    by_cases zero : word = 0
    · subst word; rfl
    · by_cases one : word = 1
      · subst word; rfl
      · unfold decodeExtendedMemoryMember decodeCanonicalScalar memoryScalarCandidate
        simp only [if_neg zero, if_neg one]
        rfl
  · subst τ
    unfold decodeExtendedMemoryMember
    rw [decodeCanonicalScalar_encode D (.int Source.IntTy.u256) trivial (uintValueOfWord D word) word (uintValueOfWord_word D word)]
    rfl
  · unfold decodeExtendedMemoryMember decodeCanonicalScalar
    rw [memoryScalarCandidate_memory_none D τ loc word]
    rfl

theorem decodeCanonicalArray_legacy {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p))
    (τ : Source.STy) (supported : OrdinaryMemberType τ) (n : Nat) (m : ByteView) (base : Nat) :
    decodeCanonicalArray p es τ n m base = decodeArrayMembers p es τ n m base := by
  have eq : decodeExtendedMemoryMember p es τ = decodeMemoryMember p es τ :=
    funext (fun word => decodeExtendedMemoryMember_legacy p es τ supported word)
  unfold decodeCanonicalArray
  rw [eq]
  exact decodeArrayWith_legacy p es τ n m base

theorem decodeCanonicalFields_legacy {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (es : List (MixedHeapEntry p))
    (τs : List Source.STy) (supported : ∀ τ ∈ τs, OrdinaryMemberType τ) (m : ByteView) (base : Nat) :
    decodeCanonicalFields p es τs m base = decodeMemoryFields p es τs m base := by
  induction τs generalizing base with
  | nil => rfl
  | cons τ τs ih =>
    change (do let head ← decodeExtendedMemoryMember p es τ (mload m base); let tail ← decodeCanonicalFields p es τs m (base + 32); pure (Source.DataList.cons (Source.Data.val head) tail)) = _
    rw [decodeExtendedMemoryMember_legacy p es τ (supported τ List.mem_cons_self), ih (fun σ hσ => supported σ (List.mem_cons_of_mem _ hσ))]
    rfl

theorem canonicalArrayState_legacy {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (es : List (MixedHeapEntry p)) (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (m : ByteView) :
    canonicalArrayState s p es root τ k n hl m = memberArrayStateWriteback s p es root τ k n hl m := by
  unfold canonicalArrayState memberArrayStateWriteback
  rw [decodeCanonicalArray_legacy p es τ supported]

theorem canonicalArrayHeap_legacy {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ) (k : Option Nat) (n : Nat)
    (hl : ∀ x, k = some x → x = n) (old : Fin n → Source.Val D τ)
    (found : h.get root = some ⟨_, memberArrayData D τ k n hl old⟩) (m : ByteView) :
    canonicalArrayHeap h p es root τ k n hl old found m = memberArrayHeapWriteback h p es root τ k n hl old found m := by
  unfold canonicalArrayHeap memberArrayHeapWriteback
  rw [decodeCanonicalArray_legacy p es τ supported]

theorem canonicalStructState_legacy {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (es : List (MixedHeapEntry p)) (root : Nat) (name : Source.DeclName)
    (supported : ∀ τ ∈ E.layout.fields name, OrdinaryMemberType τ) (m : ByteView) :
    canonicalStructState s p es root name m = structStateWriteback s p es root name m := by
  unfold canonicalStructState structStateWriteback
  rw [decodeCanonicalFields_legacy p es _ supported]

theorem canonicalStructHeap_legacy {D : Source.Layout} (h : Source.Heap D) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList D (D.fields name))
    (supported : ∀ τ ∈ D.fields name, OrdinaryMemberType τ)
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) :
    canonicalStructHeap h p es root name old found m = structHeapWriteback h p es root name old found m := by
  unfold canonicalStructHeap structHeapWriteback
  rw [decodeCanonicalFields_legacy p es _ supported]

theorem canonicalRetainedState_legacy {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (current : Placement s.2.heap)
    (history : RetainedAllocation allocated current) (es : List (MixedHeapEntry current)) (root : Nat) (τ : Source.STy)
    (supported : OrdinaryMemberType τ) (m : ByteView) :
    canonicalRetainedState s allocated current history es root τ m = retainedMemberArrayState s allocated current history es root τ m := by
  unfold canonicalRetainedState retainedMemberArrayState
  rw [decodeCanonicalArray_legacy current es τ supported]

theorem canonicalRetainedHeap_legacy {D : Source.Layout} {origin : Source.Heap D} (h : Source.Heap D)
    (allocated : Placement origin) (current : Placement h) (history : RetainedAllocation allocated current)
    (es : List (MixedHeapEntry current)) (root : Nat) (τ : Source.STy) (supported : OrdinaryMemberType τ)
    (n : Nat) (old : Fin n → Source.Val D τ) (found : h.get root = some ⟨_, dynamicMemberData D τ n old⟩) (m : ByteView) :
    canonicalRetainedHeap h allocated current history es root τ n old found m = retainedMemberArrayHeap h allocated current history es root τ n old found m := by
  unfold canonicalRetainedHeap retainedMemberArrayHeap
  rw [decodeCanonicalArray_legacy current es τ supported]

end Solidity.Yul.Views
