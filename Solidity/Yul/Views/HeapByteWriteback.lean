import Solidity.Yul.Views.ByteObjects

/-! Selected ordinary allocated byte/string objects in the ACTUAL source heap.
The Bool selects a codec, not a new value/state language: every value is indexed
by the exact Source.STy. Header length is retained so the original Placement's
exact shape remains valid. None is unsupported selected-object preparation, NOT
Yul refusal/no-op or a policy for header changes, growth or shared zero empties.
No extra decoder size/fuel cap, allocation observation or inverse premise. -/
namespace Solidity.Yul.Views

def heapByteType (string : Bool) : Source.STy :=
  if string then .string .memory else .bytes .memory

def heapByteData (D : Source.Layout) (string : Bool) (bs : List UInt8) : Source.Data D (heapByteType string) :=
  match string with
  | false => .bytes bs
  | true => .string bs

def decodeHeapByte (D : Source.Layout) (string : Bool) (m : ByteView) (base : Nat) : Source.Data D (heapByteType string) :=
  match string with
  | false => decodeBytesObject D m base
  | true => decodeStringObject D m base

theorem decodeHeapByte_data (D : Source.Layout) (string : Bool) (m : ByteView) (base : Nat) :
    decodeHeapByte D string m base = heapByteData D string (readBytes m (base + 32) (mload m base).val) := by
  cases string <;> rfl

theorem decodeHeapByte_encode (D : Source.Layout) (string : Bool) (bs : List UInt8)
    (hl : bs.length < 2 ^ 256) (m : ByteView) (base : Nat) :
    decodeHeapByte D string (bytesObjectView bs hl m base) base = heapByteData D string bs := by
  cases string
  · exact decode_bytesObjectView D bs hl m base
  · exact decode_stringObjectView D bs hl m base

theorem heapByteData_shape (D : Source.Layout) (string : Bool) (bs : List UInt8) :
    HasMemoryShape (heapByteData D string bs) (.bytes bs.length) := by
  cases string
  · exact .bytes _
  · exact .string _

theorem heap_cells_ext {D : Source.Layout} (h k : Source.Heap D)
    (cells : h.cells = k.cells) (next : h.next = k.next) : h = k := by
  cases h
  cases k
  cases cells
  cases next
  rfl

theorem heap_ty_of_get {D : Source.Layout} (h : Source.Heap D) (a : Nat)
    (τ : Source.STy) (d : Source.Data D τ) (found : h.get a = some ⟨τ, d⟩) : h.ty a = some τ := by
  change (h.get a).map Sigma.fst = some τ
  rw [found]
  rfl

theorem heap_write_unchanged {D : Source.Layout} (h : Source.Heap D) (a : Nat)
    (τ : Source.STy) (d : Source.Data D τ) (found : h.get a = some ⟨τ, d⟩) :
    h.write a d (heap_ty_of_get h a τ d found) = h := by
  apply heap_cells_ext (h.write a d (heap_ty_of_get h a τ d found)) h ?_ rfl
  funext b
  by_cases e : b = a
  · subst b
    change (h.write a d _).get a = h.get a
    rw [Source.Heap.write_get, found]
  · exact Source.Heap.write_other h e d _

theorem byte_shape_live_bound (n : Nat) : 32 + n ≤ (MemoryShape.bytes n).size := by
  have h := Nat.mod_add_div (n + 31) 32
  have hr := Nat.mod_lt (n + 31) (by decide : 0 < 32)
  change 32 + n ≤ 32 + (n + 31) / 32 * 32
  omega

theorem heapByte_placement_shape {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩) : p.shape a = .bytes bs.length := by
  have hs := p.typed a _ _ found
  cases string <;> generalize he : p.shape a = sh at hs <;> cases hs <;> rfl

theorem heapByte_length_bound {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩) : bs.length < 2 ^ 256 := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have he := p.ends a present
  rw [heapByte_placement_shape h p a string bs found] at he
  have hb := byte_shape_live_bound bs.length
  have hf := p.free.isLt
  omega

/-- Decode with the existing unbounded byte/string decoder, only after checking
that the real object's original length/header is retained. -/
def heapByteWriteback {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩) (m : ByteView) : Option (Source.Heap D) :=
  if (mload m (p.address a)).val = bs.length then
    some (h.write a (decodeHeapByte D string m (p.address a)) (heap_ty_of_get h a _ _ found))
  else none

theorem heapByteWriteback_success {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteWriteback h p a string bs found m = some out) :
    (mload m (p.address a)).val = bs.length ∧
    out = h.write a (decodeHeapByte D string m (p.address a)) (heap_ty_of_get h a _ _ found) := by
  unfold heapByteWriteback at e
  split at e
  · exact ⟨‹_›, (Option.some.inj e).symm⟩
  · cases e

theorem heapByteWriteback_alias {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a alias : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteWriteback h p a string bs found m = some out)
    (same : alias = a) : out.get alias = some ⟨heapByteType string, decodeHeapByte D string m (p.address a)⟩ := by
  rw [same, (heapByteWriteback_success h p a string bs found m out e).2]
  exact Source.Heap.write_get _ _ _ _

theorem heapByteWriteback_other {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a b : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteWriteback h p a string bs found m = some out)
    (other : b ≠ a) : out.get b = h.get b := by
  rw [(heapByteWriteback_success h p a string bs found m out e).2]
  exact Source.Heap.write_other _ other _ _

theorem heapByteWriteback_types_next {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩)
    (m : ByteView) (out : Source.Heap D) (e : heapByteWriteback h p a string bs found m = some out) :
    out.ty = h.ty ∧ out.next = h.next ∧ ∀ b, h.next ≤ b → out.cells b = none := by
  rw [(heapByteWriteback_success h p a string bs found m out e).2]
  exact ⟨funext (fun b => Source.Heap.write_ty _ _ b _ _), rfl, fun b hb => (h.write a _ _).bounded b hb⟩

theorem heapByteWriteback_unchanged {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩) (m : ByteView)
    (header : (mload m (p.address a)).val = bs.length)
    (payload : readBytes m (p.address a + 32) bs.length = bs) :
    heapByteWriteback h p a string bs found m = some h := by
  simp only [heapByteWriteback, header, if_true]
  rw [decodeHeapByte_data, header, payload]
  exact congrArg some (heap_write_unchanged h a _ _ found)

theorem heapByteWriteback_encode {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (old bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string old⟩)
    (hl : bs.length < 2 ^ 256) (sameLength : bs.length = old.length) (m : ByteView) :
    heapByteWriteback h p a string old found (bytesObjectView bs hl m (p.address a)) =
      some (h.write a (heapByteData D string bs) (heap_ty_of_get h a _ _ found)) := by
  simp only [heapByteWriteback, bytesObject_header, sameLength, if_true]
  rw [decodeHeapByte_encode]

theorem heapByteWriteback_bad_header {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (a : Nat) (string : Bool) (bs : List UInt8)
    (found : h.get a = some ⟨heapByteType string, heapByteData D string bs⟩) (m : ByteView)
    (bad : (mload m (p.address a)).val ≠ bs.length) : heapByteWriteback h p a string bs found m = none := by
  simp only [heapByteWriteback, if_neg bad]

end Solidity.Yul.Views
