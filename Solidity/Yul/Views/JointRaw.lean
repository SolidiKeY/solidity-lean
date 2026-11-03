import Solidity.Yul.Views.JointRetained

namespace Solidity.Yul.Views

/-- Reuse the unconditional word serialization roundtrip; the canonical
success proof supplies ACTUAL typed values and pointer ownership separately. -/
theorem arraySnapshot_reencode (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256) (m : ByteView) (base : Nat)
    (header : arrayLengthChoice k m base = n) :
    memberArrayView k n bound (fun i => mload m (base + arrayPayloadOffset k + i.val * 32)) m base = m := by
  cases k with
  | some size =>
    exact decodeStaticUint_reencode n m base
  | none =>
    change dynamicUintView n bound (fun i => mload m (base + 32 + i.val * 32)) m base = m
    unfold dynamicUintView
    rw [decodeStaticUint_reencode]
    have eq : (⟨n,bound⟩ : Roadmap.Word) = mload m base := Fin.ext header.symm
    rw [eq, mstore_mload]

/-- Both root images reproduce ALL raw bytes exactly on canonical successful
snapshot decoding, including nonzero residual/padding/tail/reserved bytes.
This is NOT a decoder/cleaning policy for noncanonical owned words. -/
theorem canonicalJoint_raw_reencode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (a : Nat) (name : Source.DeclName)
    (fs : Source.DataList E.layout (E.layout.fields name))
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ z, k = some z → z = n)
    (old values : Fin n → Source.Val E.layout τ)
    (found : h.get b = some ⟨_,memberArrayData E.layout τ k n hl old⟩) (m : ByteView)
    (header : arrayLengthChoice k m (p.address b) = n)
    (df : decodeCanonicalFields p es (E.layout.fields name) m (p.address a) = some fs)
    (da : decodeCanonicalArray p es τ n m (p.address b + arrayPayloadOffset k) = some values) :
    ∃ ws, MemoryFields p fs ws ∧
      (∀ i, MemoryElement p (values i) (mload m (p.address b + arrayPayloadOffset k + i.val * 32))) ∧
      wordListView ws (memberArrayView k n (array_length_from_placement p b n hl _ found)
        (fun i => mload m (p.address b + arrayPayloadOffset k + i.val * 32)) m (p.address b)) (p.address a) = m := by
  obtain ⟨ws, fields, same⟩ := canonicalFields_raw_reencode p es _ m _ fs df
  refine ⟨ws,fields,decodeCanonicalArray_sound p es τ n m _ values da,?_⟩
  rw [arraySnapshot_reencode k n _ m _ header]
  exact same

end Solidity.Yul.Views
