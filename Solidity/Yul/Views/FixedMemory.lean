import Solidity.Yul.Views.NominalMemory

/-! Canonical fixed-point memory words retain the actual scaled integer and
signed full-word encoding. Existing canonical/inventory predicates and guards
are unchanged. This adapter adds no source state, dirty cleaning or size cap. -/
namespace Solidity.Yul.Views.FixedMemory

def fromInt (D : Source.Layout) (f : Source.FixTy) :
    Source.Val D (.int (fixedIntTy f)) → Source.Val D (.fixed f) := by
  intro value
  cases value with
  | int n range => exact .fixed n range
  | memRef loc _ | storRef loc _ | cdRef loc _ _ => cases loc

def decode (D : Source.Layout) (f : Source.FixTy) (word : Roadmap.Word) :
    Option (Source.Val D (.fixed f)) :=
  (decodeCanonicalScalar D (.int (fixedIntTy f)) word).map (fromInt D f)

theorem fromInt_word (D : Source.Layout) (f : Source.FixTy) (v : Source.Val D (.int (fixedIntTy f))) :
    (fromInt D f v).word=v.word := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases v with
  | int n range => rfl
  | memRef loc _ | storRef loc _ | cdRef loc _ _ => cases loc

theorem word (D : Source.Layout) (f : Source.FixTy) (w : Roadmap.Word) (v : Source.Val D (.fixed f))
    (decoded : decode D f w=some v) : v.word=some w := by
  first | (simp only;done) | decide | omega | rfl | skip
  obtain ⟨inner,yes,same⟩ := Option.map_eq_some_iff.mp decoded
  cases same
  rw [fromInt_word]
  exact decodeCanonicalScalar_word D _ w inner yes

theorem decode_encode (D : Source.Layout) (f : Source.FixTy) (v : Source.Val D (.fixed f))
    (w : Roadmap.Word) (encoded : v.word=some w) : decode D f w=some v := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases v with
  | fixed n range =>
    unfold decode
    rw [decodeCanonicalScalar_encode D (.int (fixedIntTy f)) trivial (.int n range) w encoded]
    rfl
  | memRef loc _ | storRef loc _ | cdRef loc _ _ => cases loc

def decodeArray (D : Source.Layout) (f : Source.FixTy) (n : Nat) (m : ByteView) (base : Nat) :=
  decodeArrayWith (decode D f) n m base

theorem array_word (D : Source.Layout) (f : Source.FixTy) (n : Nat)
    (m : ByteView) (base : Nat) (values : Fin n → Source.Val D (.fixed f))
    (decoded : decodeArray D f n m base=some values) :
    ∀ i,(values i).word=some (mload m (base+i.val*32)) := by
  unfold Solidity.Yul.Views.FixedMemory.decodeArray at decoded
  induction n generalizing base with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    change (do let head ← Solidity.Yul.Views.FixedMemory.decode D f (Solidity.Yul.Views.mload m base); let tail ← Solidity.Yul.Views.decodeArrayWith (Solidity.Yul.Views.FixedMemory.decode D f) n m (base+32); pure (Fin.cases head tail))=some values at decoded
    cases dh : Solidity.Yul.Views.FixedMemory.decode D f (Solidity.Yul.Views.mload m base) with
    | none => rw [dh] at decoded; cases decoded
    | some head =>
      cases dt : Solidity.Yul.Views.decodeArrayWith (Solidity.Yul.Views.FixedMemory.decode D f) n m (base+32) with
      | none => rw [dh,dt] at decoded; cases decoded
      | some tail =>
        rw [dh,dt] at decoded
        cases decoded
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero,Fin.val_zero,Nat.zero_mul,Nat.add_zero] using Solidity.Yul.Views.FixedMemory.word D f _ head dh
        · have eq : base+j.succ.val*32=base+32+j.val*32 := by simp only [Fin.val_succ]; omega
          simpa only [Fin.cases_succ,eq] using ih (base+32) tail dt j

theorem array_decode_encode (D : Source.Layout) (f : Source.FixTy) (n : Nat) (m : ByteView) (base : Nat)
    (old : Fin n → Source.Val D (.fixed f))
    (encoded : ∀ i,(old i).word=some (mload m (base+i.val*32))) :
    decodeArray D f n m base=some old := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact decodeArrayWith_of_decodes (decode D f) n m base old (fun i=>decode_encode D f (old i) _ (encoded i))

def arrayState {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (root : Nat) (f : Source.FixTy) (k : Option Nat)
    (n : Nat) (hl : ∀ z,k=some z → z=n) (m : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if arrayLengthChoice k m (p.address root)==n then
    (decodeArray E.layout f n m (p.address root+arrayPayloadOffset k)).map
      (fun values=>(Source.heapPut root ⟨_,memberArrayData E.layout (.fixed f) k n hl values⟩).run s)
  else none

theorem arrayState_unchanged {E : Source.Env} {Γ : Source.RCtx}
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (root : Nat) (f : Source.FixTy) (k : Option Nat)
    (n : Nat) (hl : ∀ z,k=some z → z=n) (old : Fin n → Source.Val E.layout (.fixed f))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout (.fixed f) k n hl old⟩)
    (m : ByteView) (header : arrayLengthChoice k m (p.address root)=n)
    (encoded : ∀ i,(old i).word=some (mload m (p.address root+arrayPayloadOffset k+i.val*32))) :
    arrayState s p root f k n hl m=some (.ok (),s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold arrayState
  simp only [header,BEq.rfl,↓reduceIte]
  rw [array_decode_encode E.layout f n m _ old encoded]
  simp only [Option.map_some]
  rw [memberArrayHeapPut_run s root (.fixed f) k n hl old
    (heap_ty_of_get s.2.heap root _ _ found),heap_write_unchanged s.2.heap root _ _ found,withSourceHeap_unchanged]
theorem arrayState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (root : Nat)
    (f : Source.FixTy) (k : Option Nat) (n : Nat)
    (hl : ∀ z,k=some z → z=n) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : arrayState s p root f k n hl m=some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold arrayState at step
  split at step
  · obtain ⟨values,decoded,same⟩ := Option.map_eq_some_iff.mp step
    subst result
    exact memberArrayHeapPut_MemOK E H s p root (.fixed f) k n hl values _
      (fun i => .scalar _ _ (array_word E.layout f n m _ values decoded i)) ok
  · cases step

end Solidity.Yul.Views.FixedMemory
