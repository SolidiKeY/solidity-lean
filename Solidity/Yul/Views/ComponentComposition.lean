import Solidity.Yul.Views.AggregateData

/-! Disjoint composition of the existing concrete encoders. All laws use
actual successful encoder outputs. Natural byte coordinates are internal;
physical Word-map corollaries retain their nonwrapping extent premises. -/
namespace Solidity.Yul.Views

def roundSlot (a : Nat) : Nat := (a + 31) / 32 * 32

theorem roundSlot_spec (a : Nat) :
    a ≤ roundSlot a ∧ roundSlot a < a + 32 ∧ roundSlot a % 32 = 0 := by
  unfold roundSlot
  have := Nat.mod_add_div (a + 31) 32
  have := Nat.mod_lt (a + 31) (by decide : 0 < 32)
  omega

theorem roundSlot_aligned (a : Nat) (h : a % 32 = 0) : roundSlot a = a := by
  have hs := roundSlot_spec a
  have := Nat.mod_add_div a 32
  omega

def ComponentsDisjoint {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (p : Nat) (b : PackedMembers D ys) (q : Nat) : Prop :=
  ∀ i, a.owns p i → ¬ b.owns q i

theorem ComponentsDisjoint.symm {D : Source.Layout} {xs ys : List Source.STy}
    {a : PackedMembers D xs} {b : PackedMembers D ys} {p q : Nat}
    (h : ComponentsDisjoint a p b q) : ComponentsDisjoint b q a p :=
  fun i hb ha => h i ha hb

theorem disjoint_after_end {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Nat)
    (after : a.endByte p ≤ q) : ComponentsDisjoint a p b q := by
  intro i ha hb
  have h1 := a.owned_bounds p i ha
  have h2 := b.owned_bounds q i hb
  omega

theorem disjoint_at_roundSlot {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p : Nat) :
    ComponentsDisjoint a p b (roundSlot (a.endByte p)) :=
  disjoint_after_end a b _ _ (roundSlot_spec _).1

theorem disjoint_at_nextSlot {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (base : Roadmap.Word) :
    ComponentsDisjoint a (base.val * 32) b (a.nextSlot base * 32) :=
  disjoint_after_end a b _ _ (a.nextSlot_spec base).1

theorem component_owned_reads_preserved {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Nat)
    (h : ComponentsDisjoint a p b q) (ds : Source.DataList D ys) (m out : ByteView)
    (e : b.encode ds q m = some out) (i : Nat) (owned : a.owns p i) : out i = m i :=
  b.encode_residual ds q m out e i (h i owned)

theorem component_decode_preserved {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Nat)
    (h : ComponentsDisjoint a p b q) (ds : Source.DataList D ys) (m out : ByteView)
    (e : b.encode ds q m = some out) : a.decode p out = a.decode p m :=
  a.decode_congr p out m (fun i hi => component_owned_reads_preserved a b p q h ds m out e i hi)

theorem composed_roundtrip {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Nat)
    (h : ComponentsDisjoint a p b q) (da : Source.DataList D xs) (db : Source.DataList D ys)
    (m mid out : ByteView) (ea : a.encode da p m = some mid) (eb : b.encode db q mid = some out) :
    a.decode p out = some da ∧ b.decode q out = some db := by
  constructor
  · rw [component_decode_preserved a b p q h db mid out eb]
    exact a.decode_encode da p m mid ea
  · exact b.decode_encode db q mid out eb

theorem composed_residual {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Nat)
    (da : Source.DataList D xs) (db : Source.DataList D ys) (m mid out : ByteView)
    (ea : a.encode da p m = some mid) (eb : b.encode db q mid = some out)
    (i : Nat) (ha : ¬ a.owns p i) (hb : ¬ b.owns q i) : out i = m i := by
  rw [b.encode_residual db q mid out eb i hb, a.encode_residual da p m mid ea i ha]

theorem composed_unchanged {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Nat)
    (da : Source.DataList D xs) (db : Source.DataList D ys) (m : ByteView)
    (ha : a.matches da p m) (hb : b.matches db q m) :
    (a.encode da p m).bind (b.encode db q) = some m := by
  rw [a.encode_unchanged da p m ha]
  exact b.encode_unchanged db q m hb

theorem physical_composed_roundtrip {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Roadmap.Word)
    (fa : a.Fits p) (fb : b.Fits q) (h : ComponentsDisjoint a (p.val * 32) b (q.val * 32))
    (da : Source.DataList D xs) (db : Source.DataList D ys) (m mid out : SlotView)
    (ea : a.encodeSlots da p fa m = some mid) (eb : b.encodeSlots db q fb mid = some out) :
    a.decode (p.val * 32) (slotBytes out) = some da ∧
    b.decode (q.val * 32) (slotBytes out) = some db := by
  have first : a.decode (p.val * 32) (slotBytes mid) = some da := by
    unfold PackedMembers.encodeSlots at ea
    cases he : a.encode da (p.val * 32) (slotBytes m) with
    | none => simp only [he, Option.map_none] at ea; cases ea
    | some bs =>
      simp only [he, Option.map_some] at ea
      cases ea
      exact a.slot_roundtrip da p fa m bs he
  constructor
  · rw [a.decode_congr _ _ (slotBytes mid) (fun i hi =>
      b.encodedSlots_residual db q fb mid out eb i
        (Nat.lt_of_lt_of_le (a.owned_bounds _ i hi).2 fa) (h i hi))]
    exact first
  · unfold PackedMembers.encodeSlots at eb
    cases he : b.encode db (q.val * 32) (slotBytes mid) with
    | none => simp only [he, Option.map_none] at eb; cases eb
    | some bs =>
      simp only [he, Option.map_some] at eb
      cases eb
      exact b.slot_roundtrip db q fb mid bs he

theorem physical_composed_residual {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Roadmap.Word)
    (fa : a.Fits p) (fb : b.Fits q) (da : Source.DataList D xs) (db : Source.DataList D ys)
    (m mid out : SlotView) (ea : a.encodeSlots da p fa m = some mid)
    (eb : b.encodeSlots db q fb mid = some out) (i : Nat) (bound : i < (2 ^ 256) * 32)
    (ha : ¬ a.owns (p.val * 32) i) (hb : ¬ b.owns (q.val * 32) i) :
    slotBytes out i = slotBytes m i := by
  rw [b.encodedSlots_residual db q fb mid out eb i bound hb,
    a.encodedSlots_residual da p fa m mid ea i bound ha]

theorem PackedMembers.matches_transfer {D : Source.Layout} {xs : List Source.STy}
    (cs : PackedMembers D xs) (ds : Source.DataList D xs) (p : Nat) (m m' : ByteView)
    (h : cs.matches ds p m) (same : ∀ a, cs.owns p a → m a = m' a) : cs.matches ds p m' := by
  induction cs generalizing p m m' with
  | nil => cases ds; trivial
  | cons f w c rest ih =>
    cases ds with
    | cons v tail =>
      cases v with
      | val v =>
        constructor
        · intro i
          rw [← same _ (Or.inl ⟨by omega, by have := i.isLt; omega⟩)]
          exact h.1 i
        · exact ih tail _ m m' h.2 (fun a ha => same a (Or.inr ha))
      | _ => cases h

theorem physical_composed_unchanged {D : Source.Layout} {xs ys : List Source.STy}
    (a : PackedMembers D xs) (b : PackedMembers D ys) (p q : Roadmap.Word)
    (fa : a.Fits p) (fb : b.Fits q) (da : Source.DataList D xs) (db : Source.DataList D ys)
    (m : SlotView) (ha : a.matches da (p.val * 32) (slotBytes m))
    (hb : b.matches db (q.val * 32) (slotBytes m)) :
    (a.encodeSlots da p fa m).bind (b.encodeSlots db q fb) = some m := by
  rw [a.slot_unchanged da p fa m ha]
  exact b.slot_unchanged db q fb m hb

def PackedMembers.ownsDecidable {D : Source.Layout} {xs : List Source.STy}
    (cs : PackedMembers D xs) (p a : Nat) : Decidable (cs.owns p a) := by
  cases cs with
  | nil => exact isFalse (fun h => h)
  | cons f _ _ rest =>
    letI := rest.ownsDecidable (packedStart p f.width + f.width) a
    exact inferInstanceAs (Decidable ((_ ≤ _ ∧ _ < _) ∨ rest.owns (packedStart p f.width + f.width) a))

end Solidity.Yul.Views
