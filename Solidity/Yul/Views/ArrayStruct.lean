import Solidity.Yul.Views.StructArray

/-! Constructive nested struct with a fixed scalar array followed by an actual
heterogeneous struct. Schema fields describe actual source declaration metadata;
no inverse, source-state agreement or hash separation is assumed in the schema. -/
namespace Solidity.Yul.Views

def castDataFields {D : Source.Layout} {xs ys : List Source.STy}
    (h : xs = ys) (fs : Source.DataList D xs) : Source.DataList D ys := h ▸ fs

theorem castDataFields_back {D : Source.Layout} {xs ys : List Source.STy}
    (h : xs = ys) (fs : Source.DataList D ys) : castDataFields h (castDataFields h.symm fs) = fs := by
  cases h
  rfl

def fixedArrayFields? {D : Source.Layout} {τ : Source.STy} (n : Nat)
    (v : Source.Data D (.array .storage τ (some n))) : Option (Source.DataList D (List.replicate n τ)) := by
  cases v with
  | val _ => exact none
  | array len hl xs =>
    have he : n = len := hl n rfl
    subst len
    exact some (arrayMembers n xs)

structure ArrayStructSchema (D : Source.Layout) (outer inner : Source.DeclName) (τ : Source.STy) (n : Nat) where
  scalarField : Field
  scalarWidth : StorageWidth D τ scalarField.width
  scalarCodec : ScalarCodec D τ scalarField
  innerCodecs : PackedMembers D (D.fields inner)
  positive : 0 < n
  fields : D.fields outer = [.array .storage τ (some n), .struct .storage inner]

def ArrayStructSchema.first {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) : PackedMembers D (List.replicate n τ) :=
  repeatedMembers s.scalarField s.scalarWidth s.scalarCodec n

def ArrayStructSchema.nextByte {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Nat) : Nat := roundSlot (s.first.endByte p)

def ArrayStructSchema.endByte {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Nat) : Nat := roundSlot (s.innerCodecs.endByte (s.nextByte p))

def ArrayStructSchema.owns {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p a : Nat) : Prop :=
  s.first.owns p a ∨ s.innerCodecs.owns (s.nextByte p) a

def ArrayStructSchema.Fits {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Roadmap.Word) : Prop := s.endByte (p.val * 32) ≤ (2 ^ 256) * 32

def ArrayStructSchema.makeData {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (xs : Fin n → Source.Data D τ)
    (ds : Source.DataList D (D.fields inner)) : Source.Data D (.struct .storage outer) :=
  .struct (castDataFields s.fields.symm
    (.cons (.array n (fun _ h => (Option.some.inj h).symm) xs) (.cons (.struct ds) .nil)))

def ArrayStructSchema.parts? {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (v : Source.Data D (.struct .storage outer)) :
    Option (Source.DataList D (List.replicate n τ) × Source.DataList D (D.fields inner)) := by
  cases v with
  | val _ => exact none
  | struct fs =>
    let fields := castDataFields s.fields fs
    exact do
      let array ← fixedArrayFields? n (scalarMemberHead fields)
      let members ← structFields? inner (scalarMemberHead (scalarMemberTail fields))
      pure (array, members)

theorem ArrayStructSchema.parts_makeData {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (xs : Fin n → Source.Data D τ)
    (ds : Source.DataList D (D.fields inner)) :
    s.parts? (s.makeData xs ds) = some (arrayMembers n xs, ds) := by
  change (do
    let array ← fixedArrayFields? n (scalarMemberHead (castDataFields s.fields
      (castDataFields s.fields.symm (.cons (.array n (fun _ h => (Option.some.inj h).symm) xs) (.cons (.struct ds) .nil)))))
    let members ← structFields? inner (scalarMemberHead (scalarMemberTail (castDataFields s.fields
      (castDataFields s.fields.symm (.cons (.array n (fun _ h => (Option.some.inj h).symm) xs) (.cons (.struct ds) .nil))))))
    pure (array, members)) = _
  rw [castDataFields_back]
  rfl

def ArrayStructSchema.encodeParts {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (ar : Source.DataList D (List.replicate n τ))
    (ds : Source.DataList D (D.fields inner)) (p : Nat) (m : ByteView) : Option ByteView :=
  (s.first.encode ar p m).bind (s.innerCodecs.encode ds (s.nextByte p))

def encodeArrayStruct {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Roadmap.Word) (_ : s.Fits p)
    (v : Source.Data D (.struct .storage outer)) (m : SlotView) : Option SlotView :=
  (s.parts? v).bind (fun parts => (s.encodeParts parts.1 parts.2 (p.val * 32) (slotBytes m)).map slotsOfBytes)

def decodeArrayStruct {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Roadmap.Word) (_ : s.Fits p) (m : SlotView) :
    Option (Source.Data D (.struct .storage outer)) := do
  let ar ← s.first.decode (p.val * 32) (slotBytes m)
  let ds ← s.innerCodecs.decode (s.nextByte (p.val * 32)) (slotBytes m)
  pure (s.makeData (membersArray n ar) ds)

theorem ArrayStructSchema.owned_bounds {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p a : Nat) (h : s.owns p a) : p ≤ a ∧ a < s.endByte p := by
  have h1 := s.first.end_mono p
  have h2 : s.first.endByte p ≤ s.nextByte p := (roundSlot_spec (s.first.endByte p)).1
  have h3 := s.innerCodecs.end_mono (s.nextByte p)
  have h4 := (roundSlot_spec (s.innerCodecs.endByte (s.nextByte p))).1
  cases h with
  | inl hh =>
    have hb := s.first.owned_bounds p a hh
    change p ≤ a ∧ a < roundSlot (s.innerCodecs.endByte (s.nextByte p))
    exact ⟨hb.1, by omega⟩
  | inr hh =>
    have hb := s.innerCodecs.owned_bounds (s.nextByte p) a hh
    change p ≤ a ∧ a < roundSlot (s.innerCodecs.endByte (s.nextByte p))
    exact ⟨by omega, by omega⟩

theorem arrayStruct_physical_roundtrip {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Roadmap.Word) (fits : s.Fits p)
    (xs : Fin n → Source.Val D τ) (ds : Source.DataList D (D.fields inner))
    (h : ScalarMembers ds) (m : SlotView) :
    ∃ out, encodeArrayStruct s p fits (s.makeData (fun i => .val (xs i)) ds) m = some out ∧
      decodeArrayStruct s p fits out = some (s.makeData (fun i => .val (xs i)) ds) := by
  obtain ⟨mid, ea⟩ := s.first.encode_exists _ (arrayMembers_scalar n xs) _ (slotBytes m)
  obtain ⟨bs, eb⟩ := s.innerCodecs.encode_exists ds h (s.nextByte (p.val * 32)) mid
  have pair := composed_roundtrip s.first s.innerCodecs (p.val * 32) (s.nextByte (p.val * 32))
    (disjoint_at_roundSlot _ _ _) _ ds (slotBytes m) mid bs ea eb
  have first : s.first.decode (p.val * 32) (slotBytes (slotsOfBytes bs)) =
      some (arrayMembers n (fun i => .val (xs i))) := by
    rw [s.first.decode_congr _ _ bs (fun a ha => slotBytes_slotsOfBytes bs a
      (Nat.lt_of_lt_of_le (s.owned_bounds _ a (Or.inl ha)).2 fits))]
    exact pair.1
  have second : s.innerCodecs.decode (s.nextByte (p.val * 32)) (slotBytes (slotsOfBytes bs)) = some ds := by
    rw [s.innerCodecs.decode_congr _ _ bs (fun a ha => slotBytes_slotsOfBytes bs a
      (Nat.lt_of_lt_of_le (s.owned_bounds _ a (Or.inr ha)).2 fits))]
    exact pair.2
  refine ⟨slotsOfBytes bs, ?_, ?_⟩
  · rw [encodeArrayStruct, s.parts_makeData]
    change (s.encodeParts (arrayMembers n (fun i => .val (xs i))) ds _ (slotBytes m)).map slotsOfBytes = _
    unfold ArrayStructSchema.encodeParts
    rw [ea]
    change (s.innerCodecs.encode ds _ mid).map slotsOfBytes = _
    rw [eb]; rfl
  · unfold decodeArrayStruct
    rw [first, second]
    change some (s.makeData (membersArray n (arrayMembers n (fun i => .val (xs i)))) ds) = _
    rw [membersArray_arrayMembers]

theorem arrayStruct_encoded_residual {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Roadmap.Word) (fits : s.Fits p)
    (v : Source.Data D (.struct .storage outer)) (m out : SlotView)
    (e : encodeArrayStruct s p fits v m = some out) (a : Nat)
    (bound : a < (2 ^ 256) * 32) (unowned : ¬ s.owns (p.val * 32) a) :
    slotBytes out a = slotBytes m a := by
  obtain ⟨parts, _, ep⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨bs, eb, hout⟩ := Option.map_eq_some_iff.mp ep
  obtain ⟨mid, ea, ec⟩ := Option.bind_eq_some_iff.mp eb
  rw [← hout, slotBytes_slotsOfBytes bs a bound]
  exact composed_residual s.first s.innerCodecs _ _ parts.1 parts.2 (slotBytes m) mid bs ea ec a
    (fun ha => unowned (Or.inl ha)) (fun hb => unowned (Or.inr hb))

theorem arrayStruct_encoded_unchanged {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Roadmap.Word) (fits : s.Fits p)
    (v : Source.Data D (.struct .storage outer)) (m out : SlotView)
    (e : encodeArrayStruct s p fits v m = some out) : encodeArrayStruct s p fits v out = some out := by
  obtain ⟨parts, hp, ep⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨bs, eb, hout⟩ := Option.map_eq_some_iff.mp ep
  obtain ⟨mid, ea, ec⟩ := Option.bind_eq_some_iff.mp eb
  have first := s.first.matches_transfer parts.1 (p.val * 32) mid bs
    (s.first.encode_matches parts.1 _ (slotBytes m) mid ea)
    (fun a ha => (component_owned_reads_preserved s.first s.innerCodecs _ _
      (disjoint_at_roundSlot _ _ _) parts.2 mid bs ec a ha).symm)
  have ca := s.first.matches_transfer parts.1 (p.val * 32) bs (slotBytes (slotsOfBytes bs)) first
    (fun a ha => (slotBytes_slotsOfBytes bs a (Nat.lt_of_lt_of_le (s.owned_bounds _ a (Or.inl ha)).2 fits)).symm)
  have cb := s.innerCodecs.matches_transfer parts.2 (s.nextByte (p.val * 32)) bs (slotBytes (slotsOfBytes bs))
    (s.innerCodecs.encode_matches parts.2 _ mid bs ec)
    (fun a ha => (slotBytes_slotsOfBytes bs a (Nat.lt_of_lt_of_le (s.owned_bounds _ a (Or.inr ha)).2 fits)).symm)
  subst out
  rw [encodeArrayStruct, hp]
  change (s.encodeParts parts.1 parts.2 _ (slotBytes (slotsOfBytes bs))).map slotsOfBytes = _
  rw [show s.encodeParts parts.1 parts.2 _ (slotBytes (slotsOfBytes bs)) = some (slotBytes (slotsOfBytes bs)) from
    composed_unchanged s.first s.innerCodecs _ _ parts.1 parts.2 _ ca cb]
  simp only [Option.map_some, slotsOfBytes_slotBytes]

theorem ArrayStructSchema.aligned_end {D : Source.Layout} {outer inner : Source.DeclName} {τ : Source.STy} {n : Nat}
    (s : ArrayStructSchema D outer inner τ n) (p : Nat) : s.endByte p % 32 = 0 :=
  (roundSlot_spec _).2.2

end Solidity.Yul.Views
