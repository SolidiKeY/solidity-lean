import Solidity.Theory.Observe

/-!
# The interpreter's storage as a Theory term

`SVal.abs` reads a storage value of the interpreter (`Semantics.SVal`) as a
term of the Theory algebra, and `State.abs` the whole storage as one struct
node whose members are the state variables.  The bridge (`Theory/Bridge/*`)
states each interpreter operation against the Theory operation on `abs`, and
`Theory/Bridge/Denote.lean` reads a formula's terms through it.

**The layout.**  Every node is a chain of `storeSt` over a kinded empty leaf
(`mtK`), so that a node's kind is the leaf's and a write the interpreter
makes at an absent member lands where `storeAt` puts it — innermost, over
the leaf (`setBy` appends at the end):
- a struct: its fields, the first binding outermost (the one `lookupBy`
  finds), over `structSt`;
- an array: every slot at its index, live ones and the ones past the end
  (`shadow`) alike, slot 0 outermost, over `arrSt fx`, with the length
  outermost — stored for a fixed-size array too, which the interpreter
  refuses to read (`SVal.find`) but a copy and a delete read;
- a mapping: its entries over `mapSt`, whose absent keys read the default.

So `abs` never produces a node of kind `none` (`abs_kind`): absence is a
member missing from the chain, read off the leaf as `st mtSt`.

The shadow is a second, nested `slots` call rather than `slots 0 (es ++ sh)`:
structural recursion does not see through the append.  `slots_append` is the
equation between the two readings.

The slot selection is proved once (`select_slots`), and the array's read
(`select_abs_array`) from it (design R6: indices are `Nat` casts built by
`i + 1` chains, which a proof should not unfold twice).  `storeAt_*` are the
writes the save and push bridges need, in the same layout.

Nothing here imports `Update` or the calculus: the Theory sits below them
(design R10).
-/

namespace Solidity
namespace Semantics

open Theory Theory.StValue

/-- A storage value as a term.  Fields and entries: first binding outermost
(`lookupBy`/`setBy`).  Array: every slot of `elems ++ shadow` at its index,
slot 0 outermost, over `arrSt fx`, with the length outermost (fixed arrays
too).  Mapping: entries over `mapSt dflt.abs`. -/
def SVal.abs : SVal → StValue
  | .prim p => .prim p
  | .struct fs => .st (fields fs)
  | .array es sh fx =>
      .st (.storeSt (slots 0 es (slots es.length sh (Struct.arrSt fx))) lengthSeg
        (.prim (.int (es.length : Int))))
  | .map es d => .st (entries es (Struct.mapSt (SVal.abs d)))
where
  /-- A struct's fields, the first binding outermost, over `structSt`. -/
  fields : List (Name × SVal) → Struct
  | [] => Struct.structSt
  | (n, v) :: rest => .storeSt (fields rest) (.field n) (SVal.abs v)
  /-- The slots from index `i` on, slot `i` outermost, over `b`. -/
  slots (i : Nat) : List SVal → Struct → Struct
  | [], b => b
  | v :: rest, b => .storeSt (slots (i + 1) rest b) (.at (i : Int)) (SVal.abs v)
  /-- A mapping's entries, the first binding outermost, over `b`. -/
  entries : List (Int × SVal) → Struct → Struct
  | [], b => b
  | (k, v) :: rest, b => .storeSt (entries rest b) (.at k) (SVal.abs v)

/-- The storage as one struct node, the roots as members: the path `(r, segs)`
is `.field r :: segs` (`rootPath`). -/
def State.abs (σ : State) : Struct := SVal.abs.fields σ.storage

end Semantics

namespace Theory

open Semantics StValue

/-- The Theory path of the interpreter's storage path `(r, segs)`. -/
abbrev rootPath (r : Name) (segs : List Seg) : List Seg := .field r :: segs

/-! ## Kinds of the three chains -/

/-- A struct's chain is a struct node. -/
theorem _root_.Solidity.Semantics.SVal.kind_fields (fs : List (Name × SVal)) :
    (SVal.abs.fields fs).kind = some .struct := by
  induction fs with
  | nil => rfl
  | cons x rest ih => obtain ⟨n, v⟩ := x; exact ih

/-- The slots keep their base's kind. -/
theorem _root_.Solidity.Semantics.SVal.kind_slots (i : Nat) (l : List SVal) (b : Struct) :
    (SVal.abs.slots i l b).kind = b.kind := by
  induction l generalizing i with
  | nil => rfl
  | cons v rest ih => exact ih (i + 1)

/-- The entries keep their base's kind. -/
theorem _root_.Solidity.Semantics.SVal.kind_entries (es : List (Int × SVal)) (b : Struct) :
    (SVal.abs.entries es b).kind = b.kind := by
  induction es with
  | nil => rfl
  | cons x rest ih => obtain ⟨k, v⟩ := x; exact ih

/-! ## What one read of `abs` shows -/

/-- `abs` keeps a primitive and gives every node its kind; it never gives
`none`, so an absent member is told apart from an empty struct. -/
theorem _root_.Solidity.Semantics.SVal.abs_kind (v : SVal) : v.abs.seen = match v with
    | .prim p => .prim p
    | .struct _ => .node (some .struct)
    | .array _ _ fx => .node (some (.arr fx))
    | .map .. => .node (some .map) := by
  cases v with
  | prim p => rfl
  | struct fs => exact congrArg Seen.node (SVal.kind_fields fs)
  | array es sh fx =>
      exact congrArg Seen.node ((SVal.kind_slots 0 es _).trans (SVal.kind_slots _ sh _))
  | map es d => exact congrArg Seen.node (SVal.kind_entries es _)

/-- A field of a struct is the first binding's `abs`; an index reads nothing. -/
theorem _root_.Solidity.Semantics.SVal.select_abs_fields (fs : List (Name × SVal)) (a : Seg) :
    selectSt (SVal.abs.fields fs) a =
      match a with
      | .field f => (match lookupBy f fs with | some v => v.abs | none => .st .mtSt)
      | .at _ => .st .mtSt := by
  induction fs with
  | nil => cases a <;> rfl
  | cons x rest ih =>
      obtain ⟨n, v⟩ := x
      cases a with
      | field f =>
          by_cases h : f = n
          · subst h; simp only [SVal.abs.fields, selectSt, lookupBy, if_pos]
          · have hne : Seg.field n ≠ Seg.field f := fun e => h (Seg.field.inj e).symm
            simp only [SVal.abs.fields, selectSt, lookupBy, if_neg hne, if_neg h, ih]
      | «at» i => simp only [SVal.abs.fields, selectSt, reduceCtorEq, if_false, ih]

/-- The slot selection, proved once: index `j` of the slots from `i` on is
element `j - i` when it is in range, and the base's read otherwise; a field
falls through to the base. -/
theorem _root_.Solidity.Semantics.SVal.select_slots (i : Nat) (l : List SVal) (b : Struct)
    (a : Seg) :
    selectSt (SVal.abs.slots i l b) a =
      match a with
      | .at j =>
          if h : (i : Int) ≤ j ∧ (j - i).toNat < l.length then (l.get ⟨(j - i).toNat, h.2⟩).abs
          else selectSt b a
      | .field _ => selectSt b a := by
  induction l generalizing i with
  | nil =>
      cases a <;>
        simp only [SVal.abs.slots, List.length_nil, Nat.not_lt_zero, and_false, dite_false]
  | cons v rest ih =>
      cases a with
      | field f => simp only [SVal.abs.slots, selectSt, reduceCtorEq, if_false, ih]
      | «at» j =>
          by_cases hij : (i : Int) = j
          · subst hij
            simp only [SVal.abs.slots, selectOnStore, ↓reduceIte, Int.le_refl, Int.sub_self,
              Int.toNat_zero, List.length_cons, Nat.zero_lt_succ, and_self, ↓reduceDIte,
              Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero]
          · have hne : Seg.at (i : Int) ≠ Seg.at j := fun e => hij (Seg.at.inj e)
            rw [SVal.abs.slots, selectSt, if_neg hne, ih (i + 1)]
            simp only
            split <;> split
            · rename_i h1 h2
              have hk : (j - (i : Int)).toNat = (j - ((i + 1 : Nat) : Int)).toNat + 1 := by omega
              simp only [List.get_eq_getElem, hk, List.getElem_cons_succ]
            -- the two ranges agree once `j ≠ i`
            all_goals first
              | rfl
              | (rename_i h1 h2; exfalso
                 simp only [Int.natCast_add, Int.cast_ofNat_Int, Int.toNat_sub', List.length_cons,
                   not_and, Nat.not_lt] at h1 h2
                 omega)

/-- The two readings of an array's slots, nested and appended. -/
theorem _root_.Solidity.Semantics.SVal.slots_append (i : Nat) (l₁ l₂ : List SVal) (b : Struct) :
    SVal.abs.slots i (l₁ ++ l₂) b = SVal.abs.slots i l₁ (SVal.abs.slots (i + l₁.length) l₂ b) := by
  induction l₁ generalizing i with
  | nil => simp only [List.nil_append, SVal.abs.slots, List.length_nil, Nat.add_zero]
  | cons v rest ih =>
      rw [List.cons_append, SVal.abs.slots, SVal.abs.slots, ih (i + 1), List.length_cons,
        Nat.add_assoc, Nat.add_comm 1 rest.length]

/-- An array reads its length at `length`, and every slot, live or past the
end, at its index. -/
theorem _root_.Solidity.Semantics.SVal.select_abs_array (e sh : List SVal) (fx : Bool) (a : Seg) :
    selectSt (asStruct (SVal.array e sh fx).abs) a =
      match a with
      | .field f => if f = "length" then .int e.length else .st .mtSt
      | .at i =>
          if h : 0 ≤ i ∧ i.toNat < (e ++ sh).length then ((e ++ sh).get ⟨i.toNat, h.2⟩).abs
          else .st .mtSt := by
  have hsl : SVal.abs.slots 0 e (SVal.abs.slots e.length sh (Struct.arrSt fx)) =
      SVal.abs.slots 0 (e ++ sh) (Struct.arrSt fx) := by
    rw [SVal.slots_append, Nat.zero_add]
  cases a with
  | field f =>
      by_cases h : f = "length"
      · subst h; simp only [SVal.abs, asStruct_st, selectOnStore, ↓reduceIte]
      · have hne : lengthSeg ≠ Seg.field f := fun e => h (Seg.field.inj e).symm
        simp only [SVal.abs, asStruct, selectSt, if_neg hne, if_neg h, hsl, SVal.select_slots]
  | «at» i =>
      simp only [SVal.abs, asStruct, selectSt, lengthSeg, reduceCtorEq, if_false, hsl,
        SVal.select_slots]
      simp only [Int.cast_ofNat_Int, Int.sub_zero, List.length_append, List.get_eq_getElem]

/-- A mapping reads an entry's `abs`, or its default's at an absent key (and
at any field). -/
theorem _root_.Solidity.Semantics.SVal.select_abs_map (es : List (Int × SVal)) (d : SVal)
    (a : Seg) :
    selectSt (asStruct (SVal.map es d).abs) a =
      match a with
      | .at k => (match lookupBy k es with | some v => v.abs | none => d.abs)
      | .field _ => d.abs := by
  simp only [SVal.abs, asStruct]
  induction es with
  | nil => cases a <;> rfl
  | cons x rest ih =>
      obtain ⟨k, v⟩ := x
      cases a with
      | «at» j =>
          by_cases h : j = k
          · subst h; simp only [SVal.abs.entries, selectSt, lookupBy, if_pos]
          · have hne : Seg.at k ≠ Seg.at j := fun e => h (Seg.at.inj e).symm
            simp only [SVal.abs.entries, selectSt, lookupBy, if_neg hne, if_neg h]
            exact ih
      | field f =>
          simp only [SVal.abs.entries, selectSt, reduceCtorEq, if_false]
          exact ih

/-! ## The layout under a write -/

/-- A write at a slot in range replaces it in place. -/
theorem _root_.Solidity.Semantics.SVal.storeAt_slots (i : Nat) (l : List SVal) (b : Struct)
    {k : Nat} (hk : k < l.length) (v : SVal) :
    storeAt (SVal.abs.slots i l b) (.at ((i + k : Nat) : Int)) v.abs =
      SVal.abs.slots i (l.set k v) b := by
  induction l generalizing i k with
  | nil => exact absurd hk (Nat.not_lt_zero k)
  | cons v0 rest ih =>
      cases k with
      | zero => simp only [SVal.abs.slots, Nat.add_zero, storeAt, ↓reduceIte, List.set_cons_zero]
      | succ k =>
          have hk' : k < rest.length := by
            simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk; omega
          have hne : Seg.at (i : Int) ≠ Seg.at ((i + (k + 1) : Nat) : Int) := by
            intro e; have := Seg.at.inj e; omega
          rw [SVal.abs.slots, storeAt, if_neg hne, show i + (k + 1) = (i + 1) + k by omega,
            ih (i + 1) hk', List.set_cons_succ, SVal.abs.slots]

/-- A write at any other member goes through the slots to the base. -/
theorem _root_.Solidity.Semantics.SVal.storeAt_slots_frame (i : Nat) (l : List SVal) (b : Struct)
    (a : Seg) (w : StValue) (h : ∀ k, k < l.length → a ≠ .at ((i + k : Nat) : Int)) :
    storeAt (SVal.abs.slots i l b) a w = SVal.abs.slots i l (storeAt b a w) := by
  induction l generalizing i with
  | nil => rfl
  | cons v0 rest ih =>
      have hne : Seg.at (i : Int) ≠ a :=
        fun e => h 0 (by simp only [List.length_cons, Nat.zero_lt_succ]) (by rw [← e]; rfl)
      have h' : ∀ k, k < rest.length → a ≠ .at (((i + 1) + k : Nat) : Int) := by
        intro k hk
        have := h (k + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega)
        rwa [show i + (k + 1) = (i + 1) + k by omega] at this
      rw [SVal.abs.slots, storeAt, if_neg hne, ih (i + 1) h', SVal.abs.slots]

/-- A field write is `setBy`: in place where the field is, appended innermost
where it is not. -/
theorem _root_.Solidity.Semantics.SVal.storeAt_abs_fields (fs : List (Name × SVal)) (f : Name)
    (v : SVal) :
    storeAt (SVal.abs.fields fs) (.field f) v.abs = SVal.abs.fields (setBy f v fs) := by
  induction fs with
  | nil => rfl
  | cons x rest ih =>
      obtain ⟨n, v0⟩ := x
      by_cases h : f = n
      · subst h; simp only [SVal.abs.fields, storeAt, setBy, if_pos]
      · have hne : Seg.field n ≠ Seg.field f := fun e => h (Seg.field.inj e).symm
        simp only [SVal.abs.fields, storeAt, setBy, if_neg hne, if_neg h, ih]

/-- An entry write is `setBy`, the same way, over the mapping's leaf. -/
theorem _root_.Solidity.Semantics.SVal.storeAt_abs_entries (es : List (Int × SVal)) (d : StValue)
    (k : Int) (v : SVal) :
    storeAt (SVal.abs.entries es (Struct.mapSt d)) (.at k) v.abs =
      SVal.abs.entries (setBy k v es) (Struct.mapSt d) := by
  induction es with
  | nil => rfl
  | cons x rest ih =>
      obtain ⟨k', v0⟩ := x
      by_cases h : k = k'
      · subst h; simp only [SVal.abs.entries, storeAt, setBy, if_pos]
      · have hne : Seg.at k' ≠ Seg.at k := fun e => h (Seg.at.inj e).symm
        simp only [SVal.abs.entries, storeAt, setBy, if_neg hne, if_neg h, ih]

end Theory
end Solidity
