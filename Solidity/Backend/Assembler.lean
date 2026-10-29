import Solidity.Backend.Jumpdest

/-!
# The assembler (G45.04)

Symbolic assembly in solc's vocabulary (`libevmasm`'s `AssemblyItem`):

* `instr i` — a fixed instruction;
* `tag l` — the label `l`, assembled as `JUMPDEST`;
* `pushTag l` — `PUSHw` of `l`'s absolute offset, `base` plus its offset
  in this section (solc's `PushTag`), the operand of a jump;
* `pushTagRel l` — `PUSHw` of `l`'s offset relative to the section start;
* `pushLibraryAddress x` — `PUSH20` of library `x`'s address, or a
  20-byte zero placeholder with a link reference when the address is not
  known yet (solc's `PushLibraryAddress` and its `linkReferences`).

**Widths.** Each label gets one `PUSH` width, at most 32, for all its
references. `fixWidths` starts every width at 0 (`PUSH0`) and widens each to
the bytes its target needs (`byteWidth`) until nothing changes, a
fixpoint: widths only grow and are bounded by 32, so the sum of
`32 - width` over the referenced labels decreases on every round
(`termination_by`). Widening one push can move a later target past a width
boundary, which is why one pass does not suffice.

**Proved.**

* `assemble_pushTag` — every resolved `pushTag l` pushes, big-endian, the
  absolute offset of `l`'s `JUMPDEST`, and that offset is a valid jump
  destination of the encoded bytes, whatever encoded program of size `base`
  precedes the section and whatever bytes follow it (relocation);
* `assemble_pushTagRel` — the relative form pushes the section offset;
* `assemble_isSome` — assembly succeeds when the tags are distinct, every
  referenced tag exists and the all-32-byte layout fits in 32-byte pushes;
* `link_patch` — writing each library's address over its placeholder
  bytes gives exactly the bytes of the code assembled with those addresses.
-/

namespace Solidity.Backend

/-! ## Big-endian immediates -/

/-- The low `n` bytes of `v`, most significant first. -/
def toBytesBE : (n : Nat) → Nat → Vector UInt8 n
  | 0, _ => #v[]
  | n + 1, v => (toBytesBE n (v / 256)).push (UInt8.ofNat (v % 256))

/-- A big-endian byte string's value. -/
def ofBytesBE (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem ofBytesBE_append_singleton (l : List UInt8) (b : UInt8) :
    ofBytesBE (l ++ [b]) = ofBytesBE l * 256 + b.toNat := by
  simp only [ofBytesBE, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ofBytesBE_toBytesBE : ∀ (n v : Nat), v < 256 ^ n → ofBytesBE (toBytesBE n v).toList = v
  | 0, v, h => by
    simp only [Nat.pow_zero] at h
    simp only [toBytesBE, ofBytesBE, Vector.toList_mk, List.foldl_nil]
    omega
  | n + 1, v, h => by
    have hv : v / 256 < 256 ^ n := by
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    simp only [toBytesBE, Vector.toList_push, ofBytesBE_append_singleton,
      ofBytesBE_toBytesBE n (v / 256) hv, UInt8.toNat_ofNat']
    omega

/-- The fewest bytes that hold `v`: `v < 256 ^ byteWidth v`. -/
def byteWidth (v : Nat) : Nat := if v = 0 then 0 else byteWidth (v / 256) + 1
termination_by v
decreasing_by omega

theorem lt_pow_byteWidth (v : Nat) : v < 256 ^ byteWidth v := by
  fun_induction byteWidth v with
  | case1 => simp only [Nat.pow_zero, Nat.lt_one_iff]
  | case2 v hv ih =>
    rw [Nat.pow_succ]
    omega

theorem byteWidth_le {v n : Nat} (h : v < 256 ^ n) : byteWidth v ≤ n := by
  induction n generalizing v with
  | zero =>
    simp only [Nat.pow_zero] at h
    rw [byteWidth]
    simp only [show v = 0 by omega, if_true, Nat.le_refl]
  | succ n ih =>
    rw [byteWidth]
    split
    · omega
    · have hv : v / 256 < 256 ^ n := by
        rw [Nat.pow_succ] at h
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
      have hle : byteWidth (v / 256) ≤ n := ih hv
      omega

/-! ## Items and layout -/

/-- A symbolic assembly item over labels `L` and library names `Lib`. -/
inductive Item (L Lib : Type) where
  | instr (i : Instr)
  | tag (l : L)
  | pushTag (l : L)
  | pushTagRel (l : L)
  | pushLibraryAddress (x : Lib)
  deriving Repr

variable {L Lib : Type}

/-- A `PUSH` width for each label. -/
abbrev Widths (L : Type) := L → Fin 33

namespace Item

/-- The item's size in bytes under widths `W`. -/
def size (W : Widths L) : Item L Lib → Nat
  | .instr i => i.size
  | .tag _ => 1
  | .pushTag l => (W l).val + 1
  | .pushTagRel l => (W l).val + 1
  | .pushLibraryAddress _ => 21

/-- The label a reference item refers to. -/
def ref? : Item L Lib → Option L
  | .pushTag l => some l
  | .pushTagRel l => some l
  | _ => none

/-- The label a `tag` defines. -/
def tag? : Item L Lib → Option L
  | .tag l => some l
  | _ => none

end Item

/-- The labels the items refer to. -/
def refs (items : List (Item L Lib)) : List L := items.filterMap Item.ref?

/-- The labels the items define, in order. -/
def tags (items : List (Item L Lib)) : List L := items.filterMap Item.tag?

/-- The byte offset of item `k`. -/
def itemOffset (W : Widths L) (items : List (Item L Lib)) (k : Nat) : Nat :=
  ((items.take k).map (Item.size W)).sum

variable [DecidableEq L]

/-- The index of the first `tag l`. -/
def tagIndex (items : List (Item L Lib)) (l : L) : Option Nat :=
  items.findIdx? fun it => it.tag? == some l

/-- The byte offset of `tag l` in the section (0 when it is missing). -/
def tagOffset (W : Widths L) (items : List (Item L Lib)) (l : L) : Nat :=
  match tagIndex items l with
  | some k => itemOffset W items k
  | none => 0

/-! ## Width selection -/

/-- One round: widen each label's width to what its absolute offset needs
under the current layout, capped at 32. -/
def widen (base : Nat) (items : List (Item L Lib)) (W : Widths L) : Widths L :=
  fun l => ⟨min 32 (max (W l).val (byteWidth (base + tagOffset W items l))), by omega⟩

theorem le_widen (base : Nat) (items : List (Item L Lib)) (W : Widths L) (l : L) :
    (W l).val ≤ (widen base items W l).val := by
  have hW : (W l).val < 33 := (W l).isLt
  simp only [widen]
  omega

theorem sum_map_lt {α : Type} (xs : List α) (f g : α → Nat) (hle : ∀ x ∈ xs, g x ≤ f x)
    (hlt : ∃ x ∈ xs, g x < f x) : (xs.map g).sum < (xs.map f).sum := by
  induction xs with
  | nil => obtain ⟨x, hx, _⟩ := hlt; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    have hy : g y ≤ f y := hle y List.mem_cons_self
    have hrest : (ys.map g).sum ≤ (ys.map f).sum := by
      clear ih hlt
      induction ys with
      | nil => exact Nat.le_refl _
      | cons z zs ihz =>
        simp only [List.map_cons, List.sum_cons]
        have hz : g z ≤ f z := hle z (List.mem_cons_of_mem _ List.mem_cons_self)
        have hzs : (zs.map g).sum ≤ (zs.map f).sum := ihz (fun x hx => hle x (by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
        omega
    obtain ⟨x, hx, hgx⟩ := hlt
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have hys : (ys.map g).sum < (ys.map f).sum :=
        ih (fun x hx => hle x (List.mem_cons_of_mem _ hx)) ⟨x, hx, hgx⟩
      omega

/-- Widen until no referenced label's width changes. -/
def fixWidths (base : Nat) (items : List (Item L Lib)) (W : Widths L) : Widths L :=
  if _h : (refs items).all (fun l => widen base items W l == W l) then W
  else fixWidths base items (widen base items W)
termination_by ((refs items).map fun l => 32 - (W l).val).sum
decreasing_by
  apply sum_map_lt
  · intro l _
    have hle : (W l).val ≤ (widen base items W l).val := le_widen base items W l
    omega
  · simp only [Bool.not_eq_true, List.all_eq_false, beq_iff_eq] at _h
    obtain ⟨l, hl, hne⟩ := _h
    have hle : (W l).val ≤ (widen base items W l).val := le_widen base items W l
    refine ⟨l, hl, ?_⟩
    have : (W l).val ≠ (widen base items W l).val := fun e => hne (Fin.ext e.symm)
    omega

/-- At the fixpoint every referenced label's width is stable. -/
theorem fixWidths_stable (base : Nat) (items : List (Item L Lib)) (W : Widths L) :
    ∀ l ∈ refs items, widen base items (fixWidths base items W) l = fixWidths base items W l := by
  fun_induction fixWidths base items W with
  | case1 W h =>
    intro l hl
    simp only [List.all_eq_true, beq_iff_eq] at h
    exact h l hl
  | case2 W _ ih => exact ih

theorem fixWidths_le (base : Nat) (items : List (Item L Lib)) (W : Widths L) (l : L) :
    (W l).val ≤ (fixWidths base items W l).val := by
  fun_induction fixWidths base items W with
  | case1 => exact Nat.le_refl _
  | case2 W _ ih => exact Nat.le_trans (le_widen base items W l) ih

/-! ## Emitting code -/

/-- The 20-byte placeholder of an unlinked library address. -/
def placeholder : Vector UInt8 20 := Vector.replicate 20 0

/-- The instruction an item assembles to. -/
def Item.emit (W : Widths L) (target : L → Nat) (base : Nat)
    (link : Lib → Option (Vector UInt8 20)) : Item L Lib → Instr
  | .instr i => i
  | .tag _ => .op .JUMPDEST
  | .pushTag l => .push (W l) (toBytesBE (W l) (base + target l))
  | .pushTagRel l => .push (W l) (toBytesBE (W l) (target l))
  | .pushLibraryAddress x => .push 20 ((link x).getD placeholder)

omit [DecidableEq L] in
theorem Item.size_emit (W : Widths L) (target : L → Nat) (base : Nat)
    (link : Lib → Option (Vector UInt8 20)) (it : Item L Lib) :
    (it.emit W target base link).size = it.size W := by
  cases it <;> rfl

/-- The unresolved library references from byte offset `off` on: the
offset of each placeholder's first byte and its library. -/
def linkRefsFrom (W : Widths L) (link : Lib → Option (Vector UInt8 20)) :
    Nat → List (Item L Lib) → List (Nat × Lib)
  | _, [] => []
  | off, it :: rest =>
    (match it with
      | .pushLibraryAddress x => if (link x).isNone then [(off + 1, x)] else []
      | _ => []) ++ linkRefsFrom W link (off + it.size W) rest

/-- Assembled code and the placeholders still to be linked. -/
structure Assembled (Lib : Type) where
  code : Program
  /-- Each placeholder's first byte, as an offset into the whole code (the
  section starts at `base`), and its library. -/
  linkRefs : List (Nat × Lib)

/-- What `assemble` checks of the layout: distinct tags, every referenced
tag defined, every absolute target fitting its push. -/
def layoutOk (base : Nat) (items : List (Item L Lib)) (W : Widths L) : Bool :=
  decide (tags items).Nodup &&
  (refs items).all (fun l => (tagIndex items l).isSome) &&
  (refs items).all (fun l => decide (base + tagOffset W items l < 256 ^ (W l).val))

/-- The widths `assemble` chooses. -/
def asmWidths (base : Nat) (items : List (Item L Lib)) : Widths L :=
  fixWidths base items fun _ => 0

/-- Assemble a section placed at byte `base` of the final code. -/
def assemble (base : Nat) (link : Lib → Option (Vector UInt8 20))
    (items : List (Item L Lib)) : Option (Assembled Lib) :=
  let W := asmWidths base items
  if layoutOk base items W then
    some { code := items.map (Item.emit W (tagOffset W items) base link)
           linkRefs := linkRefsFrom W link base items }
  else none

/-! ## Correctness -/

theorem assemble_eq {base : Nat} {link : Lib → Option (Vector UInt8 20)}
    {items : List (Item L Lib)} {out : Assembled Lib} (h : assemble base link items = some out) :
    layoutOk base items (asmWidths base items) = true ∧
      out.code = items.map (Item.emit (asmWidths base items)
        (tagOffset (asmWidths base items) items) base link) ∧
      out.linkRefs = linkRefsFrom (asmWidths base items) link base items := by
  simp only [assemble] at h
  split at h
  · rename_i hok
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hok, rfl, rfl⟩
  · cases h

omit [DecidableEq L] in
theorem offset_map_emit (W : Widths L) (target : L → Nat) (base : Nat)
    (link : Lib → Option (Vector UInt8 20)) (items : List (Item L Lib)) (k : Nat) :
    offset (items.map (Item.emit W target base link)) k = itemOffset W items k := by
  simp only [offset, itemOffset, size, ← List.map_take, List.map_map]
  congr 1
  apply List.map_congr_left
  intro it _
  exact Item.size_emit W target base link it

/-- The assembled code has one instruction per item, at the item's offset,
and its size is the layout's: where the next section starts. -/
theorem assemble_layout {base : Nat} {link : Lib → Option (Vector UInt8 20)}
    {items : List (Item L Lib)} {out : Assembled Lib} (h : assemble base link items = some out) :
    out.code.length = items.length ∧
      (∀ k, offset out.code k = itemOffset (asmWidths base items) items k) ∧
      size out.code = itemOffset (asmWidths base items) items items.length := by
  obtain ⟨_, hc, _⟩ := assemble_eq h
  have hoff : ∀ k, offset out.code k = itemOffset (asmWidths base items) items k := by
    intro k; rw [hc]; exact offset_map_emit _ _ _ _ _ k
  refine ⟨by rw [hc, List.length_map], hoff, ?_⟩
  rw [← hoff, offset, List.take_of_length_le (by rw [hc, List.length_map]; exact Nat.le_refl _)]

theorem tagIndex_get {items : List (Item L Lib)} {l : L} {j : Nat}
    (h : tagIndex items l = some j) : items[j]? = some (.tag l) := by
  obtain ⟨hj, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  rw [List.getElem?_eq_getElem hj]
  cases hit : items[j] with
  | tag l' =>
    simp only [hit, Item.tag?, beq_iff_eq, Option.some.injEq] at hp
    rw [hp]
  | _ => simp only [hit, Item.tag?, beq_iff_eq, reduceCtorEq] at hp

theorem filterMap_nodup_index {α β : Type} (f : α → Option β) :
    ∀ (xs : List α), (xs.filterMap f).Nodup → ∀ {i j : Nat} {x : β},
      (xs[i]?.bind f) = some x → (xs[j]?.bind f) = some x → i = j
  | [], _, i, j, x, hi, _ => by simp only [List.getElem?_nil, Option.bind_none, reduceCtorEq] at hi
  | y :: ys, hnd, i, j, x, hi, hj => by
    have hmem : ∀ {k : Nat}, (ys[k]?.bind f) = some x → x ∈ ys.filterMap f := by
      intro k hk
      cases hyk : ys[k]? with
      | none => simp only [hyk, Option.bind_none, reduceCtorEq] at hk
      | some z =>
        simp only [hyk, Option.bind_some] at hk
        exact List.mem_filterMap.mpr ⟨z, List.mem_of_getElem? hyk, hk⟩
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.bind_some] at hi
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.filterMap_cons, hi, List.nodup_cons] at hnd
        exact absurd (hmem hj) hnd.1
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.bind_some] at hj
        simp only [List.getElem?_cons_succ] at hi
        simp only [List.filterMap_cons, hj, List.nodup_cons] at hnd
        exact absurd (hmem hi) hnd.1
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        have hnd' : (ys.filterMap f).Nodup := by
          cases hy : f y with
          | none => simpa only [List.filterMap_cons, hy] using hnd
          | some z =>
            simp only [List.filterMap_cons, hy, List.nodup_cons] at hnd
            exact hnd.2
        rw [filterMap_nodup_index f ys hnd' hi hj]

/-- With distinct tags, `tag l` is at exactly one index: the one
`tagIndex` finds. -/
theorem tagIndex_unique {items : List (Item L Lib)} (hnd : (tags items).Nodup) {l : L} {j : Nat}
    (hj : items[j]? = some (.tag l)) : tagIndex items l = some j := by
  have hsome : (tagIndex items l).isSome := by
    simp only [tagIndex, List.findIdx?_isSome, List.any_eq_true]
    exact ⟨_, List.mem_of_getElem? hj, by simp only [Item.tag?, beq_self_eq_true]⟩
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
  have hit := tagIndex_get hi
  rw [hi, filterMap_nodup_index Item.tag? items hnd (i := i) (j := j) (x := l)
    (by rw [hit]; rfl) (by rw [hj]; rfl)]

omit [DecidableEq L] in
theorem mem_refs {items : List (Item L Lib)} {k : Nat} {it : Item L Lib} {l : L}
    (hk : items[k]? = some it) (hr : it.ref? = some l) : l ∈ refs items := by
  simp only [refs, List.mem_filterMap]
  exact ⟨it, List.mem_of_getElem? hk, hr⟩

/-- The common part of `assemble_pushTag` and `assemble_pushTagRel`. -/
theorem assemble_ref {base : Nat} {link : Lib → Option (Vector UInt8 20)}
    {items : List (Item L Lib)} {out : Assembled Lib}
    (h : assemble base link items = some out) {k : Nat} {it : Item L Lib} {l : L}
    (hk : items[k]? = some it) (hr : it.ref? = some l) :
    ∃ j, tagIndex items l = some j ∧ out.code[j]? = some (.op .JUMPDEST) ∧
      out.code[k]? = some (it.emit (asmWidths base items)
        (tagOffset (asmWidths base items) items) base link) ∧
      tagOffset (asmWidths base items) items l = offset out.code j ∧
      base + offset out.code j < 256 ^ (asmWidths base items l).val := by
  obtain ⟨hok, hc, _⟩ := assemble_eq h
  simp only [layoutOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨_, hdef⟩, hfit⟩ := hok
  have hl : l ∈ refs items := mem_refs hk hr
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hdef l hl)
  have hjt : items[j]? = some (.tag l) := tagIndex_get hj
  have htoff : tagOffset (asmWidths base items) items l =
      itemOffset (asmWidths base items) items j := by
    simp only [tagOffset, hj]
  refine ⟨j, hj, ?_, ?_, ?_, ?_⟩
  · simp only [hc, List.getElem?_map, hjt, Option.map_some, Item.emit]
  · simp only [hc, List.getElem?_map, hk, Option.map_some]
  · rw [hc, offset_map_emit, htoff]
  · rw [hc, offset_map_emit, ← htoff]
    exact hfit l hl

/-- **Jumps reach their labels.** A resolved `pushTag l` is a `PUSH` of
`l`'s width whose big-endian value is the absolute offset of *the* `tag l`
(`tagIndex`; with distinct tags the only one, `tagIndex_unique`), which is
a `JUMPDEST`; behind any encoded prefix of size `base` and before any
trailing bytes, that offset is a valid jump destination. -/
theorem assemble_pushTag {base : Nat} {link : Lib → Option (Vector UInt8 20)}
    {items : List (Item L Lib)} {out : Assembled Lib}
    (h : assemble base link items = some out) {k : Nat} {l : L}
    (hk : items[k]? = some (.pushTag l)) :
    ∃ j imm, tagIndex items l = some j ∧ out.code[j]? = some (.op .JUMPDEST) ∧
      out.code[k]? = some (.push (asmWidths base items l) imm) ∧
      ofBytesBE imm.toList = base + offset out.code j ∧
      ofBytesBE imm.toList = base + tagOffset (asmWidths base items) items l ∧
      ∀ (pre : Program) (X : List UInt8), size pre = base →
        validJumpdest (encode pre ++ encode out.code ++ X) (ofBytesBE imm.toList) = true := by
  obtain ⟨j, hj, hjd, hkc, hoff, hfit⟩ := assemble_ref h hk rfl
  simp only [Item.emit] at hkc
  have hval : ofBytesBE (toBytesBE (asmWidths base items l) (base + offset out.code j)).toList =
      base + offset out.code j := ofBytesBE_toBytesBE _ _ hfit
  refine ⟨j, _, hj, hjd, hkc, ?_, ?_, ?_⟩
  · rw [hoff, hval]
  · rw [hoff, hval]
  · intro pre X hpre
    rw [hoff, hval, ← encode_append, ← hpre, ← offset_append]
    apply validJumpdest_encode_append
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hjd]

/-- A resolved `pushTagRel l` pushes the offset of `tag l` within the
section; adding the section's `base` relocates it to a valid destination of
the whole code. -/
theorem assemble_pushTagRel {base : Nat} {link : Lib → Option (Vector UInt8 20)}
    {items : List (Item L Lib)} {out : Assembled Lib}
    (h : assemble base link items = some out) {k : Nat} {l : L}
    (hk : items[k]? = some (.pushTagRel l)) :
    ∃ j imm, tagIndex items l = some j ∧ out.code[j]? = some (.op .JUMPDEST) ∧
      out.code[k]? = some (.push (asmWidths base items l) imm) ∧
      ofBytesBE imm.toList = offset out.code j ∧
      ∀ (pre : Program) (X : List UInt8), size pre = base →
        validJumpdest (encode pre ++ encode out.code ++ X) (base + ofBytesBE imm.toList) = true := by
  obtain ⟨j, hj, hjd, hkc, hoff, hfit⟩ := assemble_ref h hk rfl
  simp only [Item.emit] at hkc
  have hval : ofBytesBE (toBytesBE (asmWidths base items l) (offset out.code j)).toList =
      offset out.code j :=
    ofBytesBE_toBytesBE _ _ (Nat.lt_of_le_of_lt (Nat.le_add_left _ base) hfit)
  refine ⟨j, _, hj, hjd, hkc, ?_, ?_⟩
  · rw [hoff, hval]
  · intro pre X hpre
    rw [hoff, hval, ← encode_append, ← hpre, ← offset_append]
    apply validJumpdest_encode_append
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hjd]

/-! ## Assembly succeeds -/

omit [DecidableEq L] in
theorem itemOffset_mono {W W' : Widths L} (hW : ∀ l, (W l).val ≤ (W' l).val)
    (items : List (Item L Lib)) (k : Nat) : itemOffset W items k ≤ itemOffset W' items k := by
  induction items generalizing k with
  | nil => simp only [itemOffset, List.take_nil, List.map_nil, List.sum_nil, Nat.le_refl]
  | cons it rest ih =>
    cases k with
    | zero => simp only [itemOffset, List.take_zero, List.map_nil, List.sum_nil, Nat.le_refl]
    | succ k =>
      have hit : it.size W ≤ it.size W' := by
        cases it with
        | pushTag l => exact Nat.succ_le_succ (hW l)
        | pushTagRel l => exact Nat.succ_le_succ (hW l)
        | _ => exact Nat.le_refl _
      have hk : itemOffset W rest k ≤ itemOffset W' rest k := ih k
      simp only [itemOffset, List.take_succ_cons, List.map_cons, List.sum_cons] at hk ⊢
      omega

theorem tagOffset_mono {W W' : Widths L} (hW : ∀ l, (W l).val ≤ (W' l).val)
    (items : List (Item L Lib)) (l : L) : tagOffset W items l ≤ tagOffset W' items l := by
  simp only [tagOffset]
  split
  · exact itemOffset_mono hW items _
  · exact Nat.le_refl 0

/-- The chosen widths fit every target whose all-32-byte layout fits. -/
theorem asmWidths_fit {base : Nat} {items : List (Item L Lib)} {l : L} (hl : l ∈ refs items)
    (h32 : base + tagOffset (fun _ => (32 : Fin 33)) items l < 256 ^ 32) :
    base + tagOffset (asmWidths base items) items l < 256 ^ (asmWidths base items l).val := by
  have hst := fixWidths_stable base items (fun _ => 0) l hl
  simp only [widen, Fin.ext_iff] at hst
  change min 32 (max (asmWidths base items l).val
    (byteWidth (base + tagOffset (asmWidths base items) items l))) = (asmWidths base items l).val at hst
  by_cases hb : byteWidth (base + tagOffset (asmWidths base items) items l) ≤
      (asmWidths base items l).val
  · exact Nat.lt_of_lt_of_le (lt_pow_byteWidth _) (Nat.pow_le_pow_right (by omega) hb)
  · have h32eq : (asmWidths base items l).val = 32 := by omega
    rw [h32eq]
    have hmono := tagOffset_mono (W := asmWidths base items) (W' := fun _ => (32 : Fin 33))
      (fun l' => Nat.le_of_lt_succ (asmWidths base items l').isLt) items l
    omega

/-- Assembly succeeds when the tags are distinct, every referenced tag is
defined, and every target fits a 32-byte push under the widest layout. -/
theorem assemble_isSome {base : Nat} (link : Lib → Option (Vector UInt8 20))
    {items : List (Item L Lib)} (hnd : (tags items).Nodup)
    (hdef : ∀ l ∈ refs items, (tagIndex items l).isSome)
    (h32 : ∀ l ∈ refs items, base + tagOffset (fun _ => (32 : Fin 33)) items l < 256 ^ 32) :
    (assemble base link items).isSome := by
  have hok : layoutOk base items (asmWidths base items) = true := by
    simp only [layoutOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨hnd, hdef⟩, fun l hl => asmWidths_fit hl (h32 l hl)⟩
  simp only [assemble, hok, if_true, Option.isSome_some]

/-! ## Linking -/

/-- Write `bs` over the bytes of `c` from offset `off` on. -/
def patchAt (c : List UInt8) (off : Nat) (bs : List UInt8) : List UInt8 :=
  c.take off ++ bs ++ c.drop (off + bs.length)

/-- Write each library's address over its placeholder. -/
def linkBytes (c : List UInt8) (refs : List (Nat × Lib)) (addr : Lib → Vector UInt8 20) :
    List UInt8 :=
  refs.foldl (fun c r => patchAt c r.1 (addr r.2).toList) c

/-- A link map completed by `addr` where it has no entry. -/
def fillLink (link : Lib → Option (Vector UInt8 20)) (addr : Lib → Vector UInt8 20) :
    Lib → Option (Vector UInt8 20) :=
  fun x => some ((link x).getD (addr x))

theorem patchAt_middle (P E : List UInt8) (b : UInt8) (z a : List UInt8)
    (h : z.length = a.length) :
    patchAt (P ++ (b :: z) ++ E) (P.length + 1) a = P ++ (b :: a) ++ E := by
  have ht : (P ++ (b :: z) ++ E).take (P.length + 1) = P ++ [b] := by
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.cons_append, List.take_succ_cons, List.take_zero]
  have hd : (P ++ (b :: z) ++ E).drop (P.length + 1 + a.length) = E := by
    rw [List.append_assoc, List.drop_append, List.drop_of_length_le (by omega),
      List.nil_append, show P.length + 1 + a.length - P.length = (b :: z).length by
        simp only [List.length_cons]; omega, List.drop_left]
  rw [patchAt, ht, hd]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

omit [DecidableEq L] in
theorem linkBytes_from (W : Widths L) (target : L → Nat) (base : Nat)
    (link : Lib → Option (Vector UInt8 20)) (addr : Lib → Vector UInt8 20) :
    ∀ (rest : List (Item L Lib)) (P X : List UInt8),
      linkBytes (P ++ encode (rest.map (Item.emit W target base link)) ++ X)
          (linkRefsFrom W link P.length rest) addr =
        P ++ encode (rest.map (Item.emit W target base (fillLink link addr))) ++ X
  | [], P, X => by simp only [List.map_nil, encode_nil, linkRefsFrom, linkBytes, List.foldl_nil]
  | it :: rest, P, X => by
    have hsame : ∀ (P' : List UInt8), P'.length = P.length + it.size W →
        (it.emit W target base link).encode = (it.emit W target base (fillLink link addr)).encode →
        (match it with
          | .pushLibraryAddress x => if (link x).isNone then [(P.length + 1, x)] else []
          | _ => []) = [] →
        P ++ (it.emit W target base link).encode = P' →
        linkBytes (P ++ encode ((it :: rest).map (Item.emit W target base link)) ++ X)
            (linkRefsFrom W link P.length (it :: rest)) addr =
          P ++ encode ((it :: rest).map (Item.emit W target base (fillLink link addr))) ++ X := by
      intro P' hlen henc hnil hP'
      simp only [linkRefsFrom, hnil, List.nil_append, List.map_cons, encode_cons,
        ← List.append_assoc, hP', ← hlen]
      rw [linkBytes_from W target base link addr rest P' X, ← hP', ← henc]
    have hlen : (P ++ (it.emit W target base link).encode).length = P.length + it.size W := by
      rw [List.length_append, Instr.length_encode, Item.size_emit]
    cases it with
    | pushLibraryAddress x =>
      cases hx : link x with
      | some a =>
        exact hsame _ hlen (by simp only [Item.emit, hx, fillLink, Option.getD_some])
          (by simp only [hx, Option.isNone_some, Bool.false_eq_true, if_false]) rfl
      | none =>
        let P' := P ++ (0x73 :: (addr x).toList)
        have hlen' : P'.length = P.length + 21 := by
          simp only [P', List.length_append, List.length_cons, Vector.length_toList]
        simp only [linkRefsFrom, hx, Option.isNone_none, if_true, List.map_cons, encode_cons,
          linkBytes, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hpatch : patchAt (P ++ (Item.emit W target base link (.pushLibraryAddress x)).encode ++
            (encode (rest.map (Item.emit W target base link)) ++ X)) (P.length + 1)
              (addr x).toList =
            P' ++ (encode (rest.map (Item.emit W target base link)) ++ X) := by
          simp only [Item.emit, hx, Option.getD_none, Instr.encode]
          rw [patchAt_middle _ _ _ _ _ (by simp only [Vector.length_toList]; rfl)]
          rfl
        simp only [List.append_assoc] at hpatch ⊢
        rw [hpatch]
        have hrest : List.foldl (fun c r => patchAt c r.1 (addr r.2).toList)
            (P' ++ (encode (rest.map (Item.emit W target base link)) ++ X))
            (linkRefsFrom W link (P.length + 21) rest) =
            P' ++ (encode (rest.map (Item.emit W target base (fillLink link addr))) ++ X) := by
          have h' := linkBytes_from W target base link addr rest P' X
          simp only [linkBytes, hlen', List.append_assoc] at h'
          exact h'
        rw [show Item.size W (Item.pushLibraryAddress x : Item L Lib) = 21 from rfl, hrest]
        simp only [P', Item.emit, fillLink, hx, Option.getD_none, Instr.encode, List.append_assoc,
          List.cons_append]
        rfl
    | instr i => exact hsame _ hlen rfl rfl rfl
    | tag l => exact hsame _ hlen rfl rfl rfl
    | pushTag l => exact hsame _ hlen rfl rfl rfl
    | pushTagRel l => exact hsame _ hlen rfl rfl rfl

omit [DecidableEq L] in
theorem linkRefsFrom_fillLink (W : Widths L) (link : Lib → Option (Vector UInt8 20))
    (addr : Lib → Vector UInt8 20) :
    ∀ (off : Nat) (items : List (Item L Lib)), linkRefsFrom W (fillLink link addr) off items = []
  | _, [] => rfl
  | off, it :: rest => by
    cases it <;> simp only [linkRefsFrom, fillLink, Option.isNone_some, Bool.false_eq_true,
      if_false, List.nil_append, linkRefsFrom_fillLink W link addr _ rest]

/-- **Linking.** In the whole code (any encoded prefix of size `base`, any
trailing bytes), writing each library's address over its placeholder gives
exactly the bytes assembled with those addresses, with nothing left to
link; offsets and every instruction but the library pushes are unchanged,
so every `assemble_pushTag` destination survives linking. -/
theorem link_patch {base : Nat} {link : Lib → Option (Vector UInt8 20)}
    {items : List (Item L Lib)} {out : Assembled Lib} (addr : Lib → Vector UInt8 20)
    (h : assemble base link items = some out) :
    ∃ out', assemble base (fillLink link addr) items = some out' ∧ out'.linkRefs = [] ∧
      (∀ (pre : Program) (X : List UInt8), size pre = base →
        linkBytes (encode pre ++ encode out.code ++ X) out.linkRefs addr =
          encode pre ++ encode out'.code ++ X) ∧
      (∀ k, offset out'.code k = offset out.code k) ∧
      (∀ (k : Nat) (it : Item L Lib), items[k]? = some it →
        (∀ x, it ≠ (.pushLibraryAddress x : Item L Lib)) →
        out'.code[k]? = out.code[k]?) := by
  obtain ⟨hok, hc, hr⟩ := assemble_eq h
  refine ⟨_, by simp only [assemble, hok, if_true]; rfl, linkRefsFrom_fillLink _ link addr base items,
    ?_, ?_, ?_⟩
  · intro pre X hpre
    have hlen : (encode pre).length = base := by rw [length_encode, hpre]
    rw [hc, hr, ← hlen]
    exact linkBytes_from _ _ _ link addr items (encode pre) X
  · intro k
    rw [hc, offset_map_emit, offset_map_emit]
  · intro k it hk hnl
    rw [hc]
    simp only [List.getElem?_map, hk, Option.map_some, Option.some.injEq]
    cases it with
    | pushLibraryAddress x => exact absurd rfl (hnl x)
    | _ => rfl

end Solidity.Backend
