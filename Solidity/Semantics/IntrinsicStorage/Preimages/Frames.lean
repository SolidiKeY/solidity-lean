import Solidity.Semantics.IntrinsicStorage.Layout
import Solidity.Semantics.ContractWorld

/-! Structural preimages of actual dependent storage. Coverage quantifies over
all addresses and mapping defaults. A finite universe of bounded preimages
makes the specification a list without evaluating the address or key domains. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage

/-- A stored field with its full-word offset, including every represented field. -/
inductive FieldCell : {fs : List (Name × Ty)} → SFields fs → Nat → {T : Ty} → SVal T → Prop
  | head {f T fs} (v : SVal T) (vs : SFields fs) : FieldCell (.cons (f := f) v vs) 0 v
  | tail {f T fs U} (v : SVal T) (vs : SFields fs) {o : Nat} {w : SVal U}
      (h : FieldCell vs o w) : FieldCell (.cons (f := f) v vs) (size T + o) w

/-- One concrete storage edge. Shadows and overwritten explicit map entries
remain represented; fallback edges cover exactly the keys using the default. -/
inductive Child : {T : Ty} → SVal T → Storage.Loc → {U : Ty} → SVal U → Storage.Loc → Prop
  | field {s U} (fs : SFields (structDef s)) {o : Nat} {v : SVal U}
      (h : FieldCell fs o v) (l : Storage.Loc) : Child (.struct fs) l v (l.add o)
  | live {E n} (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
      {i : Nat} {v : SVal E} (h : vs.toList[i]? = some v) (l : Storage.Loc) :
      Child (.array vs sh hn) l v (.data l (i * size E))
  | shadow {E n} (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
      {i : Nat} {v : SVal E} (h : sh.toList[i]? = some v) (l : Storage.Loc) :
      Child (.array vs sh hn) l v (.data l ((n + i) * size E))
  | fixed {E n} (vs : SVec E n) {i : Nat} {v : SVal E}
      (h : vs.toList[i]? = some v) (l : Storage.Loc) :
      Child (.fixed vs) l v (l.add (i * size E))
  | entry {K V} (vs : SMap K V) (d : SVal V) {k : K.Denote} {v : SVal V}
      (h : (k, v) ∈ vs.toList) (l : Storage.Loc) :
      Child (.map vs d) l v (.hash (keyWord k) l 0)
  | fallback {K V} (vs : SMap K V) (d : SVal V) (k : K.Denote)
      (h : lookupBy k vs.toList = none) (l : Storage.Loc) :
      Child (.map vs d) l d (.hash (keyWord k) l 0)

theorem fieldCell_get {fs : List (Name × Ty)} (vs : SFields fs) {f : Name} {T : Ty}
    (h : lookupBy f fs = some T) : FieldCell vs (offsetIn fs f) (vs.get h) := by
  cases vs with
  | nil => simp only [lookupBy] at h; cases h
  | @cons g U fs v rest =>
    by_cases e : f = g
    · have ht := SFields.lookupBy_cons_pos e h
      subst ht
      simpa only [offsetIn, e, if_true, SFields.get_cons, dif_pos] using FieldCell.head v rest
    · simpa only [offsetIn, e, if_false, SFields.get_cons, dif_neg] using
        FieldCell.tail v rest (fieldCell_get rest (SFields.lookupBy_cons_neg e h))

theorem child_array {E : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) {i : Nat} {v : SVal E}
    (h : (vs.toList ++ sh.toList)[i]? = some v) (l : Storage.Loc) :
    Child (.array vs sh hn) l v (.data l (i * size E)) := by
  by_cases hi : i < n
  · rw [List.getElem?_append_left (by simpa only [SVec.length_toList] using hi)] at h
    exact .live vs sh hn h l
  · rw [List.getElem?_append_right (by simpa only [SVec.length_toList] using Nat.le_of_not_gt hi),
      SVec.length_toList] at h
    have he : n + (i - n) = i := by omega
    simpa only [he] using Child.shadow vs sh hn h l

theorem Child.bounded {T U : Ty} {v : SVal T} {w : SVal U} {l m : Storage.Loc}
    (h : Child v l w m) (hl : BoundedKeys l) : BoundedKeys m := by
  cases h with
  | field fs h l => simpa only [boundedKeys_add] using hl
  | live => exact hl
  | shadow => exact hl
  | fixed => simpa only [boundedKeys_add] using hl
  | entry vs d h l => exact ⟨keyWord_lt _, hl⟩
  | fallback vs d k h l => exact ⟨keyWord_lt k, hl⟩

/-- Finite ancestry within the actual value, with no imposed depth cutoff. -/
inductive Below : {T : Ty} → SVal T → Storage.Loc → {U : Ty} → SVal U → Storage.Loc → Prop
  | refl {T} (v : SVal T) (l : Storage.Loc) : Below v l v l
  | step {T U V} {v : SVal T} {w : SVal U} {x : SVal V} {l m n : Storage.Loc}
      (head : Child v l w m) (tail : Below w m x n) : Below v l x n

theorem Below.bounded {T U : Ty} {v : SVal T} {w : SVal U} {l m : Storage.Loc}
    (h : Below v l w m) (hl : BoundedKeys l) : BoundedKeys m := by
  induction h with
  | refl => exact hl
  | step head tail ih => exact ih (head.bounded hl)

theorem Below.trans {T U V : Ty} {v : SVal T} {w : SVal U} {x : SVal V}
    {l m n : Storage.Loc} (h : Below v l w m) (g : Below w m x n) : Below v l x n := by
  induction h with
  | refl => exact g
  | step head tail ih => exact .step head (ih g)

/-- Actual successful lookup reaches the same typed value at the canonical
location. Failed lookups are handled separately by execution observations. -/
theorem below_find {T U : Ty} (p : Path T U) (v : SVal T) {w : SVal U}
    (h : v.find p = some w) (l : Storage.Loc) : Below v l w (locate p l) := by
  induction p generalizing l with
  | nil =>
    rw [SVal.find_nil] at h
    cases h
    exact .refl v l
  | field hf p ih =>
    cases v with
    | struct fs =>
      rw [SVal.find_field] at h
      exact .step (.field fs (fieldCell_get fs hf) l) (ih _ h _)
  | «at» i p ih =>
    cases v with
    | array vs sh hn =>
      rw [SVal.find_at] at h
      split at h
      next x hx => exact .step (child_array vs sh hn hx l) (ih x h _)
      next => cases h
  | atF i p ih =>
    cases v with
    | fixed vs =>
      rw [SVal.find_atF] at h
      split at h
      next x hx => exact .step (.fixed vs hx l) (ih x h _)
      next => cases h
  | key k p ih =>
    cases v with
    | map vs d =>
      rw [SVal.find_key] at h
      split at h
      next x hx => exact .step (.entry vs d (lookupBy_eq_some_mem hx) l) (ih x h _)
      next hx => exact .step (.fallback vs d k hx l) (ih d h _)

/-- An empty dynamic array still has a data origin; inline primitives only
inherit their ancestors. Mapping keys enter through actual Child edges. -/
inductive LocalInput : {T : Ty} → SVal T → Storage.Loc → Pre → Prop
  | ancestor {T} (v : SVal T) (l : Storage.Loc) {p : Pre}
      (h : p ∈ ancestry l) : LocalInput v l p
  | data {E n} (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256) (l : Storage.Loc) :
      LocalInput (.array vs sh hn) l (.data (l.word (2 ^ 256) keccakH))

def ValueInput {T : Ty} (v : SVal T) (l : Storage.Loc) (p : Pre) : Prop :=
  ∃ (U : Ty) (w : SVal U) (m : Storage.Loc), Below v l w m ∧ LocalInput w m p

theorem ValueInput.words {T : Ty} {v : SVal T} {l : Storage.Loc} {p : Pre}
    (h : ValueInput v l p) (hl : BoundedKeys l) : p.Words := by
  obtain ⟨U, w, m, below, input⟩ := h
  cases input with
  | ancestor w m hp => exact ancestry_words m (below.bounded hl) p hp
  | data => exact word_lt _

theorem ValueInput.child {T U : Ty} {v : SVal T} {w : SVal U} {l m : Storage.Loc}
    (h : Child v l w m) {p : Pre} (hp : ValueInput w m p) : ValueInput v l p := by
  obtain ⟨V, x, n, below, input⟩ := hp
  exact ⟨V, x, n, .step h below, input⟩

def StoredInput {C : Contract} (st : Solidity.Storage C) (p : Pre) : Prop :=
  ∃ (T : Ty) (v : SVal T) (o : Nat), FieldCell st o v ∧ ValueInput v (.root o) p

/-- No caller-supplied account support: every actual address is quantified. -/
def WorldInput {K : Type} {contracts : K → Contract} (w : ContractWorld.World contracts)
    (p : Pre) : Prop :=
  ∃ (a : ContractWorld.Address) (k : K) (st : Solidity.Storage (contracts k)),
    w.accounts a = some ⟨k, st⟩ ∧ StoredInput st p

theorem WorldInput.words {K : Type} {contracts : K → Contract}
    {w : ContractWorld.World contracts} {p : Pre} (h : WorldInput w p) : p.Words := by
  obtain ⟨a, k, st, ha, T, v, o, hv, hp⟩ := h
  exact hp.words True.intro

/-- A mathematical finite universe, never enumerated by the checks. -/
def preUniverse : List Pre :=
  ((List.finRange (2 ^ 256)).map (fun w => Pre.data w.val)) ++
  ((List.finRange (2 ^ 256)).flatMap (fun k =>
    (List.finRange (2 ^ 256)).map (fun w => Pre.entry k.val w.val)))

private theorem in_finRange {n : Nat} (i : Fin n) : i ∈ List.finRange n :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

theorem mem_preUniverse {p : Pre} (hp : p.Words) : p ∈ preUniverse := by
  cases p with
  | data w =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨⟨w, hp⟩, in_finRange _, rfl⟩
  | entry k w =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨⟨k, hp.1⟩, in_finRange _,
      List.mem_map.mpr ⟨⟨w, hp.2⟩, in_finRange _, rfl⟩⟩

/-- Choice decides occurrence, not which accounts or defaults to omit. -/
noncomputable def stored {K : Type} {contracts : K → Contract}
    (w : ContractWorld.World contracts) : List (List UInt8) := by
  classical
  exact (preUniverse.filter (fun p => decide (WorldInput w p))).map encoded

theorem mem_stored {K : Type} {contracts : K → Contract}
    (w : ContractWorld.World contracts) (b : List UInt8) :
    b ∈ stored w ↔ ∃ p, WorldInput w p ∧ encoded p = b := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, hb⟩ := List.mem_map.mp h
    exact ⟨p, of_decide_eq_true (List.mem_filter.mp hp).2, hb⟩
  · rintro ⟨p, hp, rfl⟩
    apply List.mem_map.mpr
    exact ⟨p, List.mem_filter.mpr ⟨mem_preUniverse hp.words, decide_eq_true hp⟩, rfl⟩

theorem read_stored {K : Type} {contracts : K → Contract}
    (w : ContractWorld.World contracts) (a : ContractWorld.Address) (k : K)
    (st : Solidity.Storage (contracts k)) (ha : w.accounts a = some ⟨k, st⟩)
    {T : Ty} (r : SRef (contracts k) T) {v : SVal T} (hv : st.find r = some v)
    {p : Pre} (hp : p ∈ ancestry (reference r)) : encoded p ∈ stored w := by
  apply (mem_stored w _).mpr
  refine ⟨p, ⟨a, k, st, ha, r.ty, st.get r.hroot, offsetIn _ r.root,
    fieldCell_get st r.hroot, T, v, reference r, ?_, ?_⟩, rfl⟩
  · exact below_find r.path _ hv _
  · exact .ancestor v _ hp


/-- Structural inputs of an actual aggregate operand at its reached location. -/
noncomputable def valueInputs {T : Ty} (v : SVal T) (l : Storage.Loc) : List (List UInt8) := by
  classical
  exact (preUniverse.filter (fun p => decide (ValueInput v l p))).map encoded

theorem valueInputs_covers {T : Ty} (v : SVal T) (l : Storage.Loc) (hl : BoundedKeys l)
    {p : Pre} (hp : ValueInput v l p) : encoded p ∈ valueInputs v l := by
  classical
  exact List.mem_map.mpr ⟨p,
    List.mem_filter.mpr ⟨mem_preUniverse (hp.words hl), decide_eq_true hp⟩, rfl⟩

end Solidity.Semantics.IntrinsicStorage
