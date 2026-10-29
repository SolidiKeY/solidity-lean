import Solidity.Backend.Assembler

/-!
# Structured control flow to labelled code (G45.03 preparation)

A structured block — straight-line instructions, `if`/`else` on a word
the condition code leaves on the stack, `while` loops, sequencing — expands
into assembler items (`Backend/Assembler.lean`) with labels drawn from a
counter, in solc's legacy shapes:

* `ite c t e` (n, n+1 fresh): `c; ISZERO; PUSH [n]; JUMPI; t; PUSH [n+1];
  JUMP; n: JUMPDEST; e; n+1: JUMPDEST`, the false branch at `n`;
* `loop c b` (n, n+1 fresh): `n: JUMPDEST; c; ISZERO; PUSH [n+1]; JUMPI; b;
  PUSH [n]; JUMP; n+1: JUMPDEST`, the backedge `PUSH [n]; JUMP`.

**Proved.** The expansion only defines labels from its counter range,
defines each once (`tags_nodup`) and defines every label it references
(`refs_defined`). So `assemble` succeeds whenever the widest layout fits
(`expand_assemble_isSome`), and by `assemble_pushTag` and `tagIndex_unique`
every branch, exit and backedge jump lands on the `JUMPDEST` of its own
label. `expand_loop_layout` places a loop's labels: its head at the loop's
first byte and its exit at its last.

The meaning of the expanded code (that it runs the structured program) is
G45.03 itself and needs the EVM's step semantics; it is not claimed here.
-/

namespace Solidity.Backend

/-- Structured code. Conditions are instruction sequences leaving one word. -/
inductive Block where
  | code (is : List Instr)
  | seq (a b : Block)
  | ite (cond : List Instr) (thn els : Block)
  | loop (cond : List Instr) (body : Block)
  deriving Repr

namespace Block

/-- Items over `Nat` labels, from label `n` on, and the next free label. -/
def expand : Block → Nat → List (Item Nat Empty) × Nat
  | .code is, n => (is.map .instr, n)
  | .seq a b, n =>
    let (ia, m) := a.expand n
    let (ib, k) := b.expand m
    (ia ++ ib, k)
  | .ite c t e, n =>
    let (it, m) := t.expand (n + 2)
    let (ie, k) := e.expand m
    (c.map .instr ++ [.instr (.op .ISZERO), .pushTag n, .instr (.op .JUMPI)] ++ it ++
      [.pushTag (n + 1), .instr (.op .JUMP), .tag n] ++ ie ++ [.tag (n + 1)], k)
  | .loop c b, n =>
    let (ib, k) := b.expand (n + 2)
    ([.tag n] ++ c.map .instr ++ [.instr (.op .ISZERO), .pushTag (n + 1), .instr (.op .JUMPI)] ++
      ib ++ [.pushTag n, .instr (.op .JUMP), .tag (n + 1)], k)

theorem expand_le (b : Block) (n : Nat) : n ≤ (b.expand n).2 := by
  induction b generalizing n with
  | code is => exact Nat.le_refl n
  | seq a b iha ihb => exact Nat.le_trans (iha n) (ihb _)
  | ite c t e iht ihe =>
    have h1 : n + 2 ≤ (t.expand (n + 2)).2 := iht (n + 2)
    have h2 : (t.expand (n + 2)).2 ≤ (e.expand (t.expand (n + 2)).2).2 := ihe _
    simp only [expand]
    omega
  | loop c b ihb =>
    have h1 : n + 2 ≤ (b.expand (n + 2)).2 := ihb (n + 2)
    simp only [expand]
    omega

private theorem filterMap_none {α β : Type} (l : List α) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.filterMap_cons, ih]

/-- The labels a block's expansion defines, by structure. -/
theorem tags_expand (b : Block) (n : Nat) : tags (b.expand n).1 =
    match b with
    | .code _ => []
    | .seq a b' => tags (a.expand n).1 ++ tags (b'.expand (a.expand n).2).1
    | .ite _ t e => tags (t.expand (n + 2)).1 ++ [n] ++
        tags (e.expand (t.expand (n + 2)).2).1 ++ [n + 1]
    | .loop _ b' => [n] ++ tags (b'.expand (n + 2)).1 ++ [n + 1] := by
  cases b <;> simp only [expand, tags, List.filterMap_append, List.filterMap_map,
    List.filterMap_cons, List.filterMap_nil, Function.comp_def, Item.tag?,
    filterMap_none, List.nil_append, List.append_assoc, List.cons_append]

/-- The labels a block's expansion references, by structure. -/
theorem refs_expand (b : Block) (n : Nat) : refs (b.expand n).1 =
    match b with
    | .code _ => []
    | .seq a b' => refs (a.expand n).1 ++ refs (b'.expand (a.expand n).2).1
    | .ite _ t e => [n] ++ refs (t.expand (n + 2)).1 ++ [n + 1] ++
        refs (e.expand (t.expand (n + 2)).2).1
    | .loop _ b' => [n + 1] ++ refs (b'.expand (n + 2)).1 ++ [n] := by
  cases b <;> simp only [expand, refs, List.filterMap_append, List.filterMap_map,
    List.filterMap_cons, List.filterMap_nil, Function.comp_def, Item.ref?,
    filterMap_none, List.nil_append, List.append_assoc, List.cons_append, List.append_nil]

/-- Every label the expansion defines comes from its counter range. -/
theorem tags_range (b : Block) (n : Nat) :
    ∀ l ∈ tags (b.expand n).1, n ≤ l ∧ l < (b.expand n).2 := by
  induction b generalizing n with
  | code is =>
    intro l hl
    rw [tags_expand] at hl
    exact absurd hl List.not_mem_nil
  | seq a b iha ihb =>
    intro l hl
    rw [tags_expand, List.mem_append] at hl
    have h1 : n ≤ (a.expand n).2 := expand_le a n
    have h2 : (a.expand n).2 ≤ (b.expand (a.expand n).2).2 := expand_le b _
    simp only [expand]
    rcases hl with hl | hl
    · obtain ⟨_, _⟩ := iha n l hl; omega
    · obtain ⟨_, _⟩ := ihb _ l hl; omega
  | ite c t e iht ihe =>
    intro l hl
    rw [tags_expand] at hl
    simp only [List.mem_append, List.mem_singleton] at hl
    have h1 : n + 2 ≤ (t.expand (n + 2)).2 := expand_le t (n + 2)
    have h2 : (t.expand (n + 2)).2 ≤ (e.expand (t.expand (n + 2)).2).2 := expand_le e _
    simp only [expand]
    rcases hl with ((hl | rfl) | hl) | rfl
    · obtain ⟨_, _⟩ := iht (n + 2) l hl; omega
    · omega
    · obtain ⟨_, _⟩ := ihe _ l hl; omega
    · omega
  | loop c b ihb =>
    intro l hl
    rw [tags_expand] at hl
    simp only [List.mem_append, List.mem_singleton] at hl
    have h1 : n + 2 ≤ (b.expand (n + 2)).2 := expand_le b (n + 2)
    simp only [expand]
    rcases hl with (rfl | hl) | rfl
    · omega
    · obtain ⟨_, _⟩ := ihb (n + 2) l hl; omega
    · omega

/-- The expansion defines each label at most once. -/
theorem tags_nodup (b : Block) (n : Nat) : (tags (b.expand n).1).Nodup := by
  induction b generalizing n with
  | code is => rw [tags_expand]; exact List.nodup_nil
  | seq a b iha ihb =>
    rw [tags_expand, List.nodup_append]
    refine ⟨iha n, ihb _, ?_⟩
    intro x hx y hy hxy
    obtain ⟨_, _⟩ := tags_range a n x hx
    obtain ⟨_, _⟩ := tags_range b _ y hy
    omega
  | ite c t e iht ihe =>
    rw [tags_expand]
    simp only [List.nodup_append, List.nodup_cons, List.nodup_nil, List.mem_append,
      List.mem_singleton, List.not_mem_nil, not_false_eq_true, and_true, true_and]
    have he : ∀ l ∈ tags (t.expand (n + 2)).1, n + 2 ≤ l ∧ l < (t.expand (n + 2)).2 :=
      tags_range t (n + 2)
    have ht : ∀ l ∈ tags (e.expand (t.expand (n + 2)).2).1,
        (t.expand (n + 2)).2 ≤ l ∧ l < (e.expand (t.expand (n + 2)).2).2 :=
      tags_range e (t.expand (n + 2)).2
    have hle : n + 2 ≤ (t.expand (n + 2)).2 := expand_le t (n + 2)
    refine ⟨⟨⟨iht (n + 2), ?_⟩, ihe _, ?_⟩, ?_⟩
    · intro x hx y hy hxy; obtain ⟨_, _⟩ := he x hx; omega
    · intro x hx y hy hxy
      rcases hx with hx | hxn
      · obtain ⟨_, _⟩ := he x hx; obtain ⟨_, _⟩ := ht y hy; omega
      · obtain ⟨_, _⟩ := ht y hy; omega
    · intro x hx y hy hxy
      rcases hx with (hx | hxn) | hx
      · obtain ⟨_, _⟩ := he x hx; omega
      · omega
      · obtain ⟨_, _⟩ := ht x hx; omega
  | loop c b ihb =>
    rw [tags_expand]
    simp only [List.nodup_append, List.nodup_cons, List.nodup_nil, List.mem_append,
      List.mem_singleton, List.not_mem_nil, not_false_eq_true, and_true, true_and]
    have hb : ∀ l ∈ tags (b.expand (n + 2)).1, n + 2 ≤ l ∧ l < (b.expand (n + 2)).2 :=
      tags_range b (n + 2)
    refine ⟨⟨ihb (n + 2), ?_⟩, ?_⟩
    · intro x hx y hy hxy; obtain ⟨_, _⟩ := hb y hy; omega
    · intro x hx y hy hxy
      rcases hx with hxn | hx
      · omega
      · obtain ⟨_, _⟩ := hb x hx; omega

/-- Every label the expansion references, it defines. -/
theorem refs_defined (b : Block) (n : Nat) :
    ∀ l ∈ refs (b.expand n).1, l ∈ tags (b.expand n).1 := by
  induction b generalizing n with
  | code is => intro l hl; rw [refs_expand] at hl; exact absurd hl List.not_mem_nil
  | seq a b iha ihb =>
    intro l hl
    rw [refs_expand, List.mem_append] at hl
    rw [tags_expand, List.mem_append]
    rcases hl with hl | hl
    · exact Or.inl (iha n l hl)
    · exact Or.inr (ihb _ l hl)
  | ite c t e iht ihe =>
    intro l hl
    rw [refs_expand] at hl
    rw [tags_expand]
    simp only [List.mem_append, List.mem_singleton] at hl ⊢
    rcases hl with ((rfl | hl) | rfl) | hl
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inl (Or.inl (iht _ l hl)))
    · exact Or.inr rfl
    · exact Or.inl (Or.inr (ihe _ l hl))
  | loop c b ihb =>
    intro l hl
    rw [refs_expand] at hl
    rw [tags_expand]
    simp only [List.mem_append, List.mem_singleton] at hl ⊢
    rcases hl with (rfl | hl) | rfl
    · exact Or.inr rfl
    · exact Or.inl (Or.inr (ihb _ l hl))
    · exact Or.inl (Or.inl rfl)

end Block

theorem tagIndex_isSome {L Lib : Type} [DecidableEq L] {items : List (Item L Lib)} {l : L}
    (h : l ∈ tags items) : (tagIndex items l).isSome := by
  obtain ⟨it, hit, ht⟩ := List.mem_filterMap.mp h
  simp only [tagIndex, List.findIdx?_isSome, List.any_eq_true, beq_iff_eq]
  exact ⟨it, hit, ht⟩

private theorem getElem?_last {α : Type} (xs : List α) (a : α) :
    (xs ++ [a])[(xs ++ [a]).length - 1]? = some a := by
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

private theorem getElem?_mid_last {α : Type} (pre M post : List α) (a : α) :
    (pre ++ (M ++ [a]) ++ post)[pre.length + (M ++ [a]).length - 1]? = some a := by
  rw [List.length_append, List.length_singleton,
    show pre.length + (M.length + 1) - 1 = pre.length + M.length by omega, List.append_assoc,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simp only [List.length_append, List.length_singleton]; omega),
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem itemOffset_succ {L Lib : Type} (W : Widths L) {items : List (Item L Lib)} {k : Nat}
    {it : Item L Lib} (h : items[k]? = some it) :
    itemOffset W items (k + 1) = itemOffset W items k + it.size W := by
  have hk : k < items.length := (List.getElem?_eq_some_iff.mp h).1
  simp only [itemOffset, List.take_succ, h, Option.toList_some, List.map_append, List.map_cons,
    List.map_nil, List.sum_append_nat, List.sum_cons, List.sum_nil, Nat.add_zero]

namespace Block

/-- An expansion assembles whenever its widest layout fits 32-byte pushes;
then every jump lands on its own label (`assemble_pushTag`,
`tagIndex_unique`, with `tags_nodup`). -/
theorem expand_assemble_isSome (b : Block) (n base : Nat)
    (link : Empty → Option (Vector UInt8 20))
    (h32 : ∀ l ∈ refs (b.expand n).1,
      base + tagOffset (fun _ => (32 : Fin 33)) (b.expand n).1 l < 256 ^ 32) :
    (assemble base link (b.expand n).1).isSome :=
  assemble_isSome link (tags_nodup b n)
    (fun l hl => tagIndex_isSome (refs_defined b n l hl)) h32

/-- **Loop layout.** In an assembled top-level loop, the head label (the
target of the backedge) is the loop's first instruction and the exit label
its last, the code's last byte; both are `JUMPDEST`s. `loop_jumps` places
a loop anywhere. -/
theorem expand_loop_layout (c : List Instr) (body : Block) (n base : Nat)
    (link : Empty → Option (Vector UInt8 20)) {out : Assembled Empty}
    (h : assemble base link ((Block.loop c body).expand n).1 = some out) :
    let items := ((Block.loop c body).expand n).1
    tagIndex items n = some 0 ∧ tagIndex items (n + 1) = some (items.length - 1) ∧
      out.code[0]? = some (.op .JUMPDEST) ∧ out.code[items.length - 1]? = some (.op .JUMPDEST) ∧
      offset out.code (items.length - 1) + 1 = size out.code := by
  intro items
  have hnd : (tags items).Nodup := tags_nodup (Block.loop c body) n
  have h0 : items[0]? = some (.tag n) := by
    simp only [items, expand, List.cons_append, List.getElem?_cons_zero]
  have hsplit : items = ([.tag n] ++ c.map .instr ++
      [.instr (.op .ISZERO), .pushTag (n + 1), .instr (.op .JUMPI)] ++
      (body.expand (n + 2)).1 ++ [.pushTag n, .instr (.op .JUMP)]) ++ [.tag (n + 1)] := by
    simp only [items, expand, List.append_assoc, List.cons_append, List.nil_append]
  have hlast : items[items.length - 1]? = some (.tag (n + 1)) := by
    rw [hsplit]
    exact getElem?_last _ _
  obtain ⟨_, hc, _⟩ := assemble_eq h
  obtain ⟨hlen, hoff, hsize⟩ := assemble_layout h
  have hlen' : 0 < items.length := (List.getElem?_eq_some_iff.mp h0).1
  refine ⟨tagIndex_unique hnd h0, tagIndex_unique hnd hlast, ?_, ?_, ?_⟩
  · rw [hc, List.getElem?_map, show ((Block.loop c body).expand n).1[0]? = some (.tag n) from h0]
    rfl
  · rw [hc, List.getElem?_map, show ((Block.loop c body).expand n).1[items.length - 1]? =
      some (.tag (n + 1)) from hlast]
    rfl
  · rw [hsize, hoff, show items.length = items.length - 1 + 1 by omega,
      itemOffset_succ _ hlast, Nat.add_sub_cancel]
    rfl

/-- The tags of a loop's expansion sit at its first and last item, wherever
the loop is placed among items with distinct tags. -/
theorem loop_tagIndex (c : List Instr) (body : Block) (n : Nat) (pre post : List (Item Nat Empty))
    (hnd : (tags (pre ++ ((Block.loop c body).expand n).1 ++ post)).Nodup) :
    tagIndex (pre ++ ((Block.loop c body).expand n).1 ++ post) n = some pre.length ∧
      tagIndex (pre ++ ((Block.loop c body).expand n).1 ++ post) (n + 1) =
        some (pre.length + ((Block.loop c body).expand n).1.length - 1) := by
  have hsplit : ((Block.loop c body).expand n).1 = .tag n :: ((c.map .instr ++
      [.instr (.op .ISZERO), .pushTag (n + 1), .instr (.op .JUMPI)] ++
      (body.expand (n + 2)).1 ++ [.pushTag n, .instr (.op .JUMP)]) ++ [.tag (n + 1)]) := by
    simp only [expand, List.append_assoc, List.cons_append, List.nil_append]
  constructor
  · apply tagIndex_unique hnd
    rw [hsplit, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.cons_append, List.getElem?_cons_zero]
  · apply tagIndex_unique hnd
    rw [hsplit, ← List.cons_append]
    exact getElem?_mid_last _ _ _ _

/-- A resolved push of label `l`, whose tag is item `j`, pushes the
absolute offset of item `j`. -/
theorem pushTag_value {base : Nat} {link : Empty → Option (Vector UInt8 20)}
    {items : List (Item Nat Empty)} {out : Assembled Empty}
    (h : assemble base link items = some out) {l j k : Nat} (hj : tagIndex items l = some j)
    (hk : items[k]? = some (.pushTag l)) :
    ∃ imm, out.code[k]? = some (.push (asmWidths base items l) imm) ∧
      ofBytesBE imm.toList = base + offset out.code j := by
  obtain ⟨j', imm, hj', _, hkc, hv, _, _⟩ := assemble_pushTag h hk
  rw [hj, Option.some.injEq] at hj'
  exact ⟨imm, hkc, by rw [hv, hj']⟩

/-- **Loop jumps.** In any assembled code containing a loop's expansion
(after items `pre`), every push of the loop's head label — its backedge —
pushes the absolute offset of the loop's first byte, and every push of its
exit label the absolute offset of its last. -/
theorem loop_jumps (c : List Instr) (body : Block) (n base : Nat)
    (link : Empty → Option (Vector UInt8 20)) (pre post : List (Item Nat Empty))
    {out : Assembled Empty}
    (h : assemble base link (pre ++ ((Block.loop c body).expand n).1 ++ post) = some out)
    {k : Nat} :
    ((pre ++ ((Block.loop c body).expand n).1 ++ post)[k]? = some (.pushTag n) →
      ∃ imm, out.code[k]? = some (.push (asmWidths base
          (pre ++ ((Block.loop c body).expand n).1 ++ post) n) imm) ∧
        ofBytesBE imm.toList = base + offset out.code pre.length) ∧
    ((pre ++ ((Block.loop c body).expand n).1 ++ post)[k]? = some (.pushTag (n + 1)) →
      ∃ imm, out.code[k]? = some (.push (asmWidths base
          (pre ++ ((Block.loop c body).expand n).1 ++ post) (n + 1)) imm) ∧
        ofBytesBE imm.toList =
          base + offset out.code (pre.length + ((Block.loop c body).expand n).1.length - 1)) := by
  obtain ⟨hok, _, _⟩ := assemble_eq h
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hhead, hexit⟩ := loop_tagIndex c body n pre post hok.1.1
  exact ⟨pushTag_value h hhead, pushTag_value h hexit⟩

private theorem getElem?_mid {α : Type} (pre A rest post : List α) (a : α) :
    (pre ++ (A ++ a :: rest) ++ post)[pre.length + A.length]? = some a := by
  rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.append_assoc,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.cons_append,
    List.getElem?_cons_zero]

/-- The items of an `if` before its false branch: the condition, the
conditional jump and the true branch with its jump to the end. -/
def iteHead (c : List Instr) (t : Block) (n : Nat) : List (Item Nat Empty) :=
  c.map .instr ++ [.instr (.op .ISZERO), .pushTag n, .instr (.op .JUMPI)] ++
    (t.expand (n + 2)).1 ++ [.pushTag (n + 1), .instr (.op .JUMP)]

/-- The tags of an `if`: the false branch's label right after `iteHead`,
the end label at its last item, wherever it is placed among items with
distinct tags. -/
theorem ite_tagIndex (c : List Instr) (t e : Block) (n : Nat) (pre post : List (Item Nat Empty))
    (hnd : (tags (pre ++ ((Block.ite c t e).expand n).1 ++ post)).Nodup) :
    tagIndex (pre ++ ((Block.ite c t e).expand n).1 ++ post) n =
        some (pre.length + (iteHead c t n).length) ∧
      tagIndex (pre ++ ((Block.ite c t e).expand n).1 ++ post) (n + 1) =
        some (pre.length + ((Block.ite c t e).expand n).1.length - 1) := by
  have hsplit : ((Block.ite c t e).expand n).1 =
      iteHead c t n ++ .tag n :: ((e.expand (t.expand (n + 2)).2).1 ++ [.tag (n + 1)]) := by
    simp only [expand, iteHead, List.append_assoc, List.cons_append, List.nil_append]
  have hsplit' : ((Block.ite c t e).expand n).1 =
      (iteHead c t n ++ .tag n :: (e.expand (t.expand (n + 2)).2).1) ++ [.tag (n + 1)] := by
    rw [hsplit, List.append_assoc, List.cons_append]
  constructor
  · apply tagIndex_unique hnd
    rw [hsplit]
    exact getElem?_mid _ _ _ _ _
  · apply tagIndex_unique hnd
    rw [hsplit']
    exact getElem?_mid_last _ _ _ _

/-- **`if` jumps.** In any assembled code containing an `if`'s expansion
(after items `pre`), every push of its false label — the conditional jump
taken when the condition is zero — pushes the absolute offset of the false
branch's `JUMPDEST`, and every push of its end label the absolute offset of
its last byte. -/
theorem ite_jumps (c : List Instr) (t e : Block) (n base : Nat)
    (link : Empty → Option (Vector UInt8 20)) (pre post : List (Item Nat Empty))
    {out : Assembled Empty}
    (h : assemble base link (pre ++ ((Block.ite c t e).expand n).1 ++ post) = some out)
    {k : Nat} :
    ((pre ++ ((Block.ite c t e).expand n).1 ++ post)[k]? = some (.pushTag n) →
      ∃ imm, out.code[k]? = some (.push (asmWidths base
          (pre ++ ((Block.ite c t e).expand n).1 ++ post) n) imm) ∧
        ofBytesBE imm.toList = base + offset out.code (pre.length + (iteHead c t n).length)) ∧
    ((pre ++ ((Block.ite c t e).expand n).1 ++ post)[k]? = some (.pushTag (n + 1)) →
      ∃ imm, out.code[k]? = some (.push (asmWidths base
          (pre ++ ((Block.ite c t e).expand n).1 ++ post) (n + 1)) imm) ∧
        ofBytesBE imm.toList =
          base + offset out.code (pre.length + ((Block.ite c t e).expand n).1.length - 1)) := by
  obtain ⟨hok, _, _⟩ := assemble_eq h
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hfalse, hend⟩ := ite_tagIndex c t e n pre post hok.1.1
  exact ⟨pushTag_value h hfalse, pushTag_value h hend⟩

end Block

end Solidity.Backend
