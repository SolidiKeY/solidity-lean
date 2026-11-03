import Solidity.Yul.Views.CanonicalMemory

/-! Additive canonical nominal memory words over the ACTUAL Source UDVT
constructor and layout lookup. No old codec/guard changes, dirty cleaning,
new state/IR, recursive planner or depth limit. A logical Layout may contain
arbitrary nominal names; declaredUDVT checks actual Env metadata separately.
Unsupported preparation is not a source/Yul refusal or successful no-op. -/
namespace Solidity.Yul.Views.NominalMemory
open Solidity.Yul.Views

def decode (D : Source.Layout) (name : Source.DeclName) (word : Roadmap.Word) :
    Option (Source.Val D (.udvt name)) :=
  (decodeCanonicalScalar D (D.underlying name) word).map Source.Val.udvt

/-- No missing-name default-to-bool declaration is invented. This checks the
actual owner lookup AND syntax constructor, not merely Layout.underlying. -/
def declaredUDVT (E : Source.Env) (name : Source.DeclName) : Bool :=
  match E.declOf .udvt name with
  | some ⟨.udvt,_,_,_,.udvt _ _⟩ => true
  | _ => false

def decodeDeclared (E : Source.Env) (name : Source.DeclName) (word : Roadmap.Word) :
    Option (Source.Val E.layout (.udvt name)) :=
  if declaredUDVT E name then decode E.layout name word else none

/-- Existing parameter-only Nat recursion and concrete callback, not a second
array decoder/planner. No artificial size or fuel cap is introduced. -/
def decodeArray (D : Source.Layout) (name : Source.DeclName) (n : Nat) (m : ByteView) (base : Nat) :
    Option (Fin n → Source.Val D (.udvt name)) :=
  decodeArrayWith (decode D name) n m base

/-- Existing actual Source heapPut, preserving its full success/error result.
The header must match the explicit expected length. Interpreting that as the
old length and proving placement transport additionally need the real old
object/length facts; this operation alone proves no growth/ownership safety. -/
def arrayState {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (root : Nat) (name : Source.DeclName) (k : Option Nat)
    (n : Nat) (hl : ∀ z,k=some z → z=n) (m : ByteView) :
    Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  if declaredUDVT E name && (arrayLengthChoice k m (p.address root)==n) then
    (decodeArray E.layout name n m (p.address root+arrayPayloadOffset k)).map
      (fun values => (Source.heapPut root ⟨_,memberArrayData E.layout (.udvt name) k n hl values⟩).run s)
  else none

theorem word (D : Source.Layout) (name : Source.DeclName) (w : Roadmap.Word)
    (v : Source.Val D (.udvt name)) (decoded : decode D name w=some v) :
    v.word=some w := by
  unfold decode at decoded
  obtain ⟨inner,yes,same⟩ := Option.map_eq_some_iff.mp decoded
  cases same
  exact decodeCanonicalScalar_word D _ w inner yes

theorem decode_encode (D : Source.Layout) (name : Source.DeclName)
    (supported : CanonicalScalarType D (D.underlying name))
    (v : Source.Val D (.udvt name)) (w : Roadmap.Word) (encoded : v.word=some w) :
    decode D name w=some v := by
  cases v with
  | udvt inner =>
    unfold decode
    rw [decodeCanonicalScalar_encode D _ supported inner w encoded]
    rfl
  | memRef loc _ | storRef loc _ | cdRef loc _ _ => cases loc

/-- Every successful element word is reconstructed exactly; the actual
concrete callback supplies soundness, not a caller-provided inverse field. -/
theorem array_word (D : Source.Layout) (name : Source.DeclName) (n : Nat)
    (m : ByteView) (base : Nat) (values : Fin n → Source.Val D (.udvt name))
    (decoded : decodeArray D name n m base=some values) :
    ∀ i,(values i).word=some (mload m (base+i.val*32)) := by
  unfold Solidity.Yul.Views.NominalMemory.decodeArray at decoded
  induction n generalizing base with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    change (do let head ← Solidity.Yul.Views.NominalMemory.decode D name (Solidity.Yul.Views.mload m base); let tail ← Solidity.Yul.Views.decodeArrayWith (Solidity.Yul.Views.NominalMemory.decode D name) n m (base+32); pure (Fin.cases head tail))=some values at decoded
    cases dh : Solidity.Yul.Views.NominalMemory.decode D name (Solidity.Yul.Views.mload m base) with
    | none => rw [dh] at decoded; cases decoded
    | some head =>
      cases dt : Solidity.Yul.Views.decodeArrayWith (Solidity.Yul.Views.NominalMemory.decode D name) n m (base+32) with
      | none => rw [dh,dt] at decoded; cases decoded
      | some tail =>
        rw [dh,dt] at decoded
        cases decoded
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero,Fin.val_zero,Nat.zero_mul,Nat.add_zero] using Solidity.Yul.Views.NominalMemory.word D name _ head dh
        · have eq : base+j.succ.val*32=base+32+j.val*32 := by simp only [Fin.val_succ]; omega
          simpa only [Fin.cases_succ,eq] using ih (base+32) tail dt j

/-- A raw snapshot encoding the actual nominal values decodes to those values.
The only representation premise is the existing canonical underlying codec. -/
theorem array_decode_encode (D : Source.Layout) (name : Source.DeclName)
    (supported : CanonicalScalarType D (D.underlying name))
    (n : Nat) (m : ByteView) (base : Nat)
    (old : Fin n → Source.Val D (.udvt name))
    (encoded : ∀ i,(old i).word=some (mload m (base+i.val*32))) :
    decodeArray D name n m base=some old := by
  exact decodeArrayWith_of_decodes (decode D name) n m base old
    (fun i => decode_encode D name supported (old i) _ (encoded i))

/-- Unchanged canonical memory preserves the entire source state, including
unwritten cells, caller locals and world. Exact original typed data is required;
a header or a physical address alone does not establish allocation ownership. -/
theorem arrayState_unchanged {E : Source.Env} {Γ : Source.RCtx}
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (root : Nat)
    (name : Source.DeclName) (k : Option Nat) (n : Nat)
    (hl : ∀ z,k=some z → z=n) (old : Fin n → Source.Val E.layout (.udvt name))
    (declared : declaredUDVT E name=true)
    (supported : CanonicalScalarType E.layout (E.layout.underlying name))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout (.udvt name) k n hl old⟩)
    (m : ByteView) (header : arrayLengthChoice k m (p.address root)=n)
    (encoded : ∀ i,(old i).word=some (mload m (p.address root+arrayPayloadOffset k+i.val*32))) :
    arrayState s p root name k n hl m=some (.ok (),s) := by
  unfold arrayState
  simp only [declared, header, BEq.rfl, Bool.and_self, ↓reduceIte]
  rw [array_decode_encode E.layout name supported n m _ old encoded]
  simp only [Option.map_some]
  rw [memberArrayHeapPut_run s root (.udvt name) k n hl old
    (heap_ty_of_get s.2.heap root _ _ found),
    heap_write_unchanged s.2.heap root _ _ found, withSourceHeap_unchanged]

/-- Preparing a same-length nominal array at an existing typed object executes
exactly the existing source heap write; a successful preparation cannot conceal
a source type error. -/
theorem arrayState_write {E : Source.Env} {Γ : Source.RCtx}
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (root : Nat)
    (name : Source.DeclName) (k : Option Nat) (n : Nat)
    (hl : ∀ z,k=some z → z=n) (old : Fin n → Source.Val E.layout (.udvt name))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout (.udvt name) k n hl old⟩)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : arrayState s p root name k n hl m=some result) :
    ∃ values : Fin n → Source.Val E.layout (.udvt name),
      decodeArray E.layout name n m (p.address root+arrayPayloadOffset k)=some values ∧
      result=(.ok (),withSourceHeap s (s.2.heap.write root
        (memberArrayData E.layout (.udvt name) k n hl values)
        (heap_ty_of_get s.2.heap root _ _ found))) := by
  unfold arrayState at step
  split at step
  · obtain ⟨values,decoded,same⟩ := Option.map_eq_some_iff.mp step
    rw [memberArrayHeapPut_run s root (.udvt name) k n hl values
      (heap_ty_of_get s.2.heap root _ _ found)] at same
    exact ⟨values,decoded,same.symm⟩
  · cases step

/-- The actual same-length write has a valid output placement with the original
coordinates, shape and free choice. Other cells and all non-heap state survive. -/
theorem arrayState_placement {E : Source.Env} {Γ : Source.RCtx}
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (root : Nat)
    (name : Source.DeclName) (k : Option Nat) (n : Nat)
    (hl : ∀ z,k=some z → z=n) (old : Fin n → Source.Val E.layout (.udvt name))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout (.udvt name) k n hl old⟩)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : arrayState s p root name k n hl m=some result) :
    (∃ q : Placement result.2.2.heap,
      q.address=p.address ∧ q.shape=p.shape ∧ q.free=p.free) ∧
    result.2.2.heap.ty=s.2.heap.ty ∧ result.2.2.heap.next=s.2.heap.next ∧
    (∀ a,s.2.heap.next≤a → result.2.2.heap.cells a=none) ∧
    (∀ a,a≠root → result.2.2.heap.get a=s.2.heap.get a) ∧
    result.2.1=s.1 ∧ result.2.2.ex=s.2.ex ∧ result.2.2.events=s.2.events ∧
    result.2.2.logs=s.2.logs ∧ result.2.2.fnLocals=s.2.fnLocals := by
  obtain ⟨values,decoded,same⟩ := arrayState_write s p root name k n hl old found m result step
  subst result
  let data := memberArrayData E.layout (.udvt name) k n hl values
  have typed := heap_ty_of_get s.2.heap root _ _ found
  exact ⟨⟨memberArrayWrittenPlacement s.2.heap p root (.udvt name) k n hl old values found,
    rfl,rfl,rfl⟩,funext (fun a => Source.Heap.write_ty s.2.heap root a data typed),
    rfl,(fun a ha => (s.2.heap.write root data typed).bounded a ha),
    (fun a ha => Source.Heap.write_other s.2.heap ha data typed),rfl,rfl,rfl,rfl,rfl⟩

/-- The selected typed array is the exact decoded data, whose canonical words
are the supplied snapshot words. This concerns the selected payload, not a
whole-memory realization or a claim that dirty words are representable. -/
theorem arrayState_readback {E : Source.Env} {Γ : Source.RCtx}
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (root : Nat)
    (name : Source.DeclName) (k : Option Nat) (n : Nat)
    (hl : ∀ z,k=some z → z=n) (old : Fin n → Source.Val E.layout (.udvt name))
    (found : s.2.heap.get root=some ⟨_,memberArrayData E.layout (.udvt name) k n hl old⟩)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : arrayState s p root name k n hl m=some result) :
    ∃ values : Fin n → Source.Val E.layout (.udvt name),
      result.2.2.heap.get root=some ⟨_,memberArrayData E.layout (.udvt name) k n hl values⟩ ∧
      ∀ i,(values i).word=some (mload m (p.address root+arrayPayloadOffset k+i.val*32)) := by
  obtain ⟨values,decoded,same⟩ := arrayState_write s p root name k n hl old found m result step
  subst result
  exact ⟨values,Source.Heap.write_get s.2.heap root
    (memberArrayData E.layout (.udvt name) k n hl values)
    (heap_ty_of_get s.2.heap root _ _ found),array_word E.layout name n m _ values decoded⟩

/-- Transport every original owner heap typing through the COMPLETE real
heapPut outcome, including an actual type-error halt. Canonical preparation
None is separate and is not reclassified as a source result. -/
theorem arrayState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (root : Nat)
    (name : Source.DeclName) (k : Option Nat) (n : Nat)
    (hl : ∀ z,k=some z → z=n) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : arrayState s p root name k n hl m=some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold arrayState at step
  split at step
  · obtain ⟨values,decoded,same⟩ := Option.map_eq_some_iff.mp step
    subst result
    exact memberArrayHeapPut_MemOK E H s p root (.udvt name) k n hl values _
      (fun i => .scalar _ _ (array_word E.layout name n m _ values decoded i)) ok
  · cases step

end Solidity.Yul.Views.NominalMemory
