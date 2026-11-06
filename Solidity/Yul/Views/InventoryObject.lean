import Solidity.Yul.Views.JointSequential

/-! Concrete canonical object decoding for the existing intrinsic heap inventory.
No second source state or untyped IR. The result contains actual indexed Data,
its exact shape and a constructor-derived image, not inverse/safety law fields.
Only existing ordinary allocated bytes/string/array/struct components are used. -/
namespace Solidity.Yul.Views

structure InventoryObject {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (τ : Source.STy) where
  data : Source.Data E.layout τ
  shape : MemoryShape
  shaped : HasMemoryShape data shape
  image : MemoryImage p data

theorem InventoryObject.top {E : Source.Env} {h : Source.Heap E.layout} {p : Placement h} {τ : Source.STy}
    (o : InventoryObject p τ) : Source.Data.Top (E := E) o.data := by
  rcases o with ⟨data,shape,shaped,image⟩
  cases shaped <;> trivial

def InventoryObject.transport {E : Source.Env} {h h' : Source.Heap E.layout} {p : Placement h}
    (q : Placement h') (types : h'.ty = h.ty) (addresses : q.address = p.address)
    {τ : Source.STy} (o : InventoryObject p τ) : InventoryObject q τ :=
  ⟨o.data,o.shape,o.shaped,o.image.transport q types addresses⟩

theorem decodedFields_snapshot {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τs : List Source.STy) (m : ByteView) (base : Nat)
    (fs : Source.DataList E.layout τs) (decoded : decodeCanonicalFields p es τs m base = some fs) :
    MemoryFields p fs (List.ofFn (fun i : Fin τs.length => mload m (base+i.val*32))) := by
  obtain ⟨ws,fields,reads⟩ := decodeCanonicalFields_representation p es τs m base fs decoded
  have same : ws = List.ofFn (fun i : Fin τs.length => mload m (base+i.val*32)) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]; exact fields.length
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact (reads i ws[i] (List.getElem?_eq_getElem hi)).symm
  rw [← same]
  exact fields

def snapshotBytes {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (m : ByteView) (base : Nat) :
    InventoryObject p (.bytes .memory) :=
  let bs := readBytes m (base+32) (mload m base).val
  let len : bs.length = (mload m base).val := by simp only [bs,readBytes,List.length_map,List.length_range]
  ⟨.bytes bs,.bytes bs.length,.bytes bs,.bytes bs (by rw [len]; exact (mload m base).isLt)⟩

def snapshotString {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (m : ByteView) (base : Nat) :
    InventoryObject p (.string .memory) :=
  let bs := readBytes m (base+32) (mload m base).val
  let len : bs.length = (mload m base).val := by simp only [bs,readBytes,List.length_map,List.length_range]
  ⟨.string bs,.bytes bs.length,.string bs,.string bs (by rw [len]; exact (mload m base).isLt)⟩

theorem snapshotLengthChoice (k : Option Nat) (m : ByteView) (base : Nat) :
    ∀ n, k = some n → n = arrayLengthChoice k m base := by
  cases k with
  | none => intro n eq; cases eq
  | some n => intro z eq; cases eq; rfl

def snapshotArray {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (l : Source.DataLoc) (τ : Source.STy) (k : Option Nat) (m : ByteView) (base : Nat) : Option (InventoryObject p (.array l τ k)) :=
  let n := arrayLengthChoice k m base
  if bound : n < 2^256 then
    (decodeCanonicalArray p es τ n m (base+arrayPayloadOffset k)).pmap (fun values decoded =>
      ⟨.array n (snapshotLengthChoice k m base) (fun i => .val (values i)),.array k.isNone n,
        .array n (snapshotLengthChoice k m base) _,
        .words _ _ (.array n (snapshotLengthChoice k m base) bound values
          (fun i => mload m (base+arrayPayloadOffset k+i.val*32)) (decodeCanonicalArray_sound p es τ n m _ values decoded))⟩)
      (fun _ member => member)
  else none

def snapshotStruct {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (l : Source.DataLoc) (name : Source.DeclName) (m : ByteView) (base : Nat) : Option (InventoryObject p (.struct l name)) :=
  (decodeCanonicalFields p es (E.layout.fields name) m base).pmap (fun fs decoded =>
    ⟨.struct fs,.strct (E.layout.fields name).length,.strct fs,
      .words _ _ (.strct fs _ (decodedFields_snapshot p es _ m base fs decoded))⟩)
    (fun _ member => member)

/-- Case elimination on the ordinary type syntax, not indexed source data.
The 256bit length bound is the real word/layout bound, never a resource cap.
For an actual static array entry it follows from its existing Placement. -/
def decodeInventoryObject {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (τ : Source.STy) (m : ByteView) (base : Nat) : Option (InventoryObject p τ) := by
  cases τ with
  | bytes l => cases l with
    | memory => exact some (snapshotBytes p m base)
    | storage | calldata => exact none
  | string l => cases l with
    | memory => exact some (snapshotString p m base)
    | storage | calldata => exact none
  | array l τ k => exact snapshotArray p es l τ k m base
  | struct l name => exact snapshotStruct p es l name m base
  | _ => exact none

theorem snapshotArray_actual_bound {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (a : Nat)
    {l : Source.DataLoc} {τ : Source.STy} {k : Option Nat} (n : Nat) (hl : ∀ z, k = some z → z = n)
    (old : Fin n → Source.Data E.layout τ) (found : h.get a = some ⟨.array l τ k,.array n hl old⟩)
    (m : ByteView) : arrayLengthChoice k m (p.address a) < 2^256 := by
  cases k with
  | none => exact (mload m (p.address a)).isLt
  | some z =>
    have eq := hl z rfl
    subst z
    exact array_length_from_placement p a n hl old found

end Solidity.Yul.Views
