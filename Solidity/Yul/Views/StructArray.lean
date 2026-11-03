import Solidity.Yul.Views.ComponentComposition

/-! Fixed arrays of actual heterogeneous struct contents. Recursion is on Nat;
all field contents remain Source.DataList D (D.fields d). Public Word-based entry points start each
element on a storage-slot boundary and round its end; low-level helpers accept Nat coordinates. No Source representation is replaced. -/
namespace Solidity.Yul.Views

def structArrayEnd {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) : Nat → Nat → Nat
  | 0, p => p
  | n + 1, p => structArrayEnd cs n (roundSlot (cs.endByte p))

def structArrayOwns {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) : Nat → Nat → Nat → Prop
  | 0, _, _ => False
  | n + 1, p, a => cs.owns p a ∨ structArrayOwns cs n (roundSlot (cs.endByte p)) a

def encodeStructs {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) : (n : Nat) →
    (Fin n → Source.DataList D (D.fields d)) → Nat → ByteView → Option ByteView
  | 0, _, _, m => some m
  | n + 1, fs, p, m => (cs.encode (fs ⟨0, by omega⟩) p m).bind
      (fun mid => encodeStructs cs n (fun i => fs i.succ) (roundSlot (cs.endByte p)) mid)

def decodeStructs {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) : (n : Nat) → Nat → ByteView →
    Option (Fin n → Source.DataList D (D.fields d))
  | 0, _, _ => some Fin.elim0
  | n + 1, p, m => do
    let head ← cs.decode p m
    let tail ← decodeStructs cs n (roundSlot (cs.endByte p)) m
    pure (Fin.cases head tail)

theorem structArrayEnd_mono {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n p : Nat) : p ≤ structArrayEnd cs n p := by
  induction n generalizing p with
  | zero => exact Nat.le_refl p
  | succ n ih => exact Nat.le_trans (Nat.le_trans (cs.end_mono p) (roundSlot_spec _).1) (ih _)

theorem structArrayOwned_bounds {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n p a : Nat) (h : structArrayOwns cs n p a) :
    p ≤ a ∧ a < structArrayEnd cs n p := by
  induction n generalizing p with
  | zero => cases h
  | succ n ih =>
    change cs.owns p a ∨ _ at h
    change p ≤ a ∧ a < structArrayEnd cs n (roundSlot (cs.endByte p))
    cases h with
    | inl hh =>
      have hb := cs.owned_bounds p a hh
      have hn := (roundSlot_spec (cs.endByte p)).1
      have ht := structArrayEnd_mono cs n (roundSlot (cs.endByte p))
      exact ⟨hb.1, by omega⟩
    | inr hh =>
      have hb := ih _ hh
      have hn := (roundSlot_spec (cs.endByte p)).1
      have hs := cs.end_mono p
      exact ⟨by omega, hb.2⟩

theorem encodeStructs_before {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n : Nat) (fs : Fin n → Source.DataList D (D.fields d))
    (p : Nat) (m out : ByteView) (e : encodeStructs cs n fs p m = some out)
    (a : Nat) (h : a < p) : out a = m a := by
  induction n generalizing p m out with
  | zero => cases e; rfl
  | succ n ih =>
    obtain ⟨mid, eh, et⟩ := Option.bind_eq_some_iff.mp e
    have hn := (roundSlot_spec (cs.endByte p)).1
    have hs := cs.end_mono p
    rw [ih (fun i => fs i.succ) _ mid out et (by omega)]
    exact cs.encode_before _ p m mid eh a h

theorem encodeStructs_residual {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n : Nat) (fs : Fin n → Source.DataList D (D.fields d))
    (p : Nat) (m out : ByteView) (e : encodeStructs cs n fs p m = some out)
    (a : Nat) (h : ¬ structArrayOwns cs n p a) : out a = m a := by
  induction n generalizing p m out with
  | zero => cases e; rfl
  | succ n ih =>
    obtain ⟨mid, eh, et⟩ := Option.bind_eq_some_iff.mp e
    change ¬ (_ ∨ _) at h
    rw [ih (fun i => fs i.succ) _ mid out et (fun ht => h (Or.inr ht))]
    exact cs.encode_residual _ p m mid eh a (fun hh => h (Or.inl hh))

theorem encodeStructs_exists {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n : Nat) (fs : Fin n → Source.DataList D (D.fields d))
    (h : ∀ i, ScalarMembers (fs i)) (p : Nat) (m : ByteView) :
    ∃ out, encodeStructs cs n fs p m = some out := by
  induction n generalizing p m with
  | zero => exact ⟨m, rfl⟩
  | succ n ih =>
    obtain ⟨mid, eh⟩ := cs.encode_exists (fs ⟨0, by omega⟩) (h _) p m
    obtain ⟨out, et⟩ := ih (fun i => fs i.succ) (fun i => h i.succ) _ mid
    exact ⟨out, Option.bind_eq_some_iff.mpr ⟨mid, eh, et⟩⟩

theorem decodeStructs_encode {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n : Nat) (fs : Fin n → Source.DataList D (D.fields d))
    (p : Nat) (m out : ByteView) (e : encodeStructs cs n fs p m = some out) :
    decodeStructs cs n p out = some fs := by
  induction n generalizing p m out with
  | zero =>
    change some Fin.elim0 = some fs
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨mid, eh, et⟩ := Option.bind_eq_some_iff.mp e
    have head : cs.decode p out = some (fs ⟨0, by omega⟩) := by
      rw [cs.decode_congr p out mid (fun a ha => by
        apply encodeStructs_before cs n (fun i => fs i.succ) _ mid out et a
        have hb := cs.owned_bounds p a ha
        have hn := (roundSlot_spec (cs.endByte p)).1
        omega)]
      exact cs.decode_encode _ p m mid eh
    rw [decodeStructs, head, ih (fun i => fs i.succ) _ mid out et]
    change some (Fin.cases (fs ⟨0, by omega⟩) (fun i => fs i.succ)) = some fs
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem decodeStructs_congr {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n p : Nat) (m m' : ByteView)
    (h : ∀ a, structArrayOwns cs n p a → m a = m' a) :
    decodeStructs cs n p m = decodeStructs cs n p m' := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [decodeStructs, decodeStructs,
      cs.decode_congr p m m' (fun a ha => h a (Or.inl ha)),
      ih _ (fun a ha => h a (Or.inr ha))]

def structArrayMatches {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) : (n : Nat) →
    (Fin n → Source.DataList D (D.fields d)) → Nat → ByteView → Prop
  | 0, _, _, _ => True
  | n + 1, fs, p, m => cs.matches (fs ⟨0, by omega⟩) p m ∧
      structArrayMatches cs n (fun i => fs i.succ) (roundSlot (cs.endByte p)) m

theorem encodeStructs_unchanged {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n : Nat) (fs : Fin n → Source.DataList D (D.fields d))
    (p : Nat) (m : ByteView) (h : structArrayMatches cs n fs p m) :
    encodeStructs cs n fs p m = some m := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [encodeStructs, cs.encode_unchanged _ p m h.1]
    exact ih (fun i => fs i.succ) _ h.2

/-- References are not treated as their target struct's contents. -/
def structFields? {D : Source.Layout} (d : Source.DeclName)
    (v : Source.Data D (.struct .storage d)) : Option (Source.DataList D (D.fields d)) := by
  cases v with
  | val _ => exact none
  | struct fs => exact some fs

def collectStructFields {D : Source.Layout} (d : Source.DeclName) : (n : Nat) →
    (Fin n → Source.Data D (.struct .storage d)) → Option (Fin n → Source.DataList D (D.fields d))
  | 0, _ => some Fin.elim0
  | n + 1, xs => do
    let head ← structFields? d (xs ⟨0, by omega⟩)
    let tail ← collectStructFields d n (fun i => xs i.succ)
    pure (Fin.cases head tail)

theorem collectStructFields_contents {D : Source.Layout} (d : Source.DeclName) (n : Nat)
    (fs : Fin n → Source.DataList D (D.fields d)) :
    collectStructFields d n (fun i => .struct (fs i)) = some fs := by
  induction n with
  | zero =>
    change some Fin.elim0 = some fs
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [collectStructFields]
    change (do
      let head ← some (fs ⟨0, by omega⟩)
      let tail ← collectStructFields d n (fun i => .struct (fs i.succ))
      pure (Fin.cases head tail)) = some fs
    rw [ih (fun i => fs i.succ)]
    change some (Fin.cases (fs ⟨0, by omega⟩) (fun i => fs i.succ)) = some fs
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Actual fixed-array source input; no pointer resolution or untyped value layer. -/
def encodeStructArray {D : Source.Layout} (d : Source.DeclName) (cs : PackedMembers D (D.fields d))
    (n : Nat) (_ : 0 < n) (p : Roadmap.Word)
    (_ : structArrayEnd cs n (p.val * 32) ≤ (2 ^ 256) * 32)
    (v : Source.Data D (.array .storage (.struct .storage d) (some n))) (m : SlotView) : Option SlotView := by
  cases v with
  | val _ => exact none
  | array len hl xs =>
    have he : n = len := hl n rfl
    subst len
    exact ((collectStructFields d n xs).bind (fun fs => encodeStructs cs n fs (p.val * 32) (slotBytes m))).map slotsOfBytes

def decodeStructArray {D : Source.Layout} (d : Source.DeclName) (cs : PackedMembers D (D.fields d))
    (n : Nat) (_ : 0 < n) (p : Roadmap.Word)
    (_ : structArrayEnd cs n (p.val * 32) ≤ (2 ^ 256) * 32) (m : SlotView) :
    Option (Source.Data D (.array .storage (.struct .storage d) (some n))) :=
  (decodeStructs cs n (p.val * 32) (slotBytes m)).map
    (fun fs => .array n (fun _ h => (Option.some.inj h).symm) (fun i => .struct (fs i)))

theorem structArray_physical_roundtrip {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (n : Nat) (hn : 0 < n) (p : Roadmap.Word)
    (fits : structArrayEnd cs n (p.val * 32) ≤ (2 ^ 256) * 32)
    (fs : Fin n → Source.DataList D (D.fields d)) (h : ∀ i, ScalarMembers (fs i)) (m : SlotView) :
    ∃ out, encodeStructArray d cs n hn p fits
        (.array n (fun _ h => (Option.some.inj h).symm) (fun i => .struct (fs i))) m = some out ∧
      decodeStructArray d cs n hn p fits out =
        some (.array n (fun _ h => (Option.some.inj h).symm) (fun i => .struct (fs i))) := by
  obtain ⟨bs, e⟩ := encodeStructs_exists cs n fs h (p.val * 32) (slotBytes m)
  refine ⟨slotsOfBytes bs, ?_, ?_⟩
  · change ((collectStructFields d n (fun i => .struct (fs i))).bind
      (fun fs => encodeStructs cs n fs (p.val * 32) (slotBytes m))).map slotsOfBytes = _
    rw [collectStructFields_contents]
    change (encodeStructs cs n fs (p.val * 32) (slotBytes m)).map slotsOfBytes = _
    rw [e]; rfl
  · have same : decodeStructs cs n (p.val * 32) (slotBytes (slotsOfBytes bs)) = some fs := by
      rw [decodeStructs_congr cs n _ _ bs (fun a ha =>
        slotBytes_slotsOfBytes bs a (Nat.lt_of_lt_of_le (structArrayOwned_bounds cs n _ a ha).2 fits))]
      exact decodeStructs_encode cs n fs _ _ bs e
    simp only [decodeStructArray, same, Option.map_some]

theorem structArrayEnd_aligned {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n p : Nat) (h : p % 32 = 0) :
    structArrayEnd cs n p % 32 = 0 := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih => exact ih _ (roundSlot_spec _).2.2

theorem structArray_head_tail_disjoint {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n p a : Nat) (head : cs.owns p a) :
    ¬ structArrayOwns cs n (roundSlot (cs.endByte p)) a := by
  intro tail
  have hh := cs.owned_bounds p a head
  have ht := structArrayOwned_bounds cs n _ a tail
  have hn := (roundSlot_spec (cs.endByte p)).1
  omega

theorem structArrayMatches_transfer {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n : Nat) (fs : Fin n → Source.DataList D (D.fields d))
    (p : Nat) (m m' : ByteView) (h : structArrayMatches cs n fs p m)
    (same : ∀ a, structArrayOwns cs n p a → m a = m' a) : structArrayMatches cs n fs p m' := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih => exact ⟨cs.matches_transfer _ p m m' h.1 (fun a ha => same a (Or.inl ha)),
      ih (fun i => fs i.succ) _ h.2 (fun a ha => same a (Or.inr ha))⟩

theorem encodeStructs_matches {D : Source.Layout} {d : Source.DeclName}
    (cs : PackedMembers D (D.fields d)) (n : Nat) (fs : Fin n → Source.DataList D (D.fields d))
    (p : Nat) (m out : ByteView) (e : encodeStructs cs n fs p m = some out) :
    structArrayMatches cs n fs p out := by
  induction n generalizing p m out with
  | zero => trivial
  | succ n ih =>
    obtain ⟨mid, eh, et⟩ := Option.bind_eq_some_iff.mp e
    constructor
    · apply cs.matches_transfer _ p mid out (cs.encode_matches _ p m mid eh)
      intro a ha
      apply (encodeStructs_before cs n (fun i => fs i.succ) _ mid out et a _).symm
      have hb := cs.owned_bounds p a ha
      have hn := (roundSlot_spec (cs.endByte p)).1
      omega
    · exact ih (fun i => fs i.succ) _ mid out et

theorem structArray_encoded_residual {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (n : Nat) (hn : 0 < n) (p : Roadmap.Word)
    (fits : structArrayEnd cs n (p.val * 32) ≤ (2 ^ 256) * 32)
    (v : Source.Data D (.array .storage (.struct .storage d) (some n))) (m out : SlotView)
    (e : encodeStructArray d cs n hn p fits v m = some out) (a : Nat)
    (bound : a < (2 ^ 256) * 32) (unowned : ¬ structArrayOwns cs n (p.val * 32) a) :
    slotBytes out a = slotBytes m a := by
  cases v with
  | val _ => cases e
  | array len hl xs =>
    have he : n = len := hl n rfl
    subst len
    obtain ⟨bs, eb, hout⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨fs, _, ef⟩ := Option.bind_eq_some_iff.mp eb
    rw [← hout, slotBytes_slotsOfBytes bs a bound]
    exact encodeStructs_residual cs n fs _ _ bs ef a unowned

theorem structArray_encoded_unchanged {D : Source.Layout} (d : Source.DeclName)
    (cs : PackedMembers D (D.fields d)) (n : Nat) (hn : 0 < n) (p : Roadmap.Word)
    (fits : structArrayEnd cs n (p.val * 32) ≤ (2 ^ 256) * 32)
    (v : Source.Data D (.array .storage (.struct .storage d) (some n))) (m out : SlotView)
    (e : encodeStructArray d cs n hn p fits v m = some out) :
    encodeStructArray d cs n hn p fits v out = some out := by
  cases v with
  | val _ => cases e
  | array len hl xs =>
    have he : n = len := hl n rfl
    subst len
    obtain ⟨bs, eb, hout⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨fs, hc, ef⟩ := Option.bind_eq_some_iff.mp eb
    have canonical := structArrayMatches_transfer cs n fs (p.val * 32) bs (slotBytes (slotsOfBytes bs))
      (encodeStructs_matches cs n fs _ _ bs ef) (fun a ha =>
        (slotBytes_slotsOfBytes bs a (Nat.lt_of_lt_of_le (structArrayOwned_bounds cs n _ a ha).2 fits)).symm)
    subst out
    change ((collectStructFields d n xs).bind
      (fun fs => encodeStructs cs n fs (p.val * 32) (slotBytes (slotsOfBytes bs)))).map slotsOfBytes = _
    rw [hc]
    change (encodeStructs cs n fs _ _).map slotsOfBytes = _
    rw [encodeStructs_unchanged cs n fs _ _ canonical]
    simp only [Option.map_some, slotsOfBytes_slotBytes]

/-- Checked declared-length boundary, retaining actual typed element contents. -/
def checkedStructArray (D : Source.Layout) (d : Source.DeclName) (declared actual : Nat)
    (xs : Fin actual → Source.Data D (.struct .storage d)) :
    Option (Source.Data D (.array .storage (.struct .storage d) (some declared))) :=
  if he : actual = declared then some (.array actual
    (fun _ hm => (Option.some.inj hm).symm.trans he.symm) xs) else none

end Solidity.Yul.Views
