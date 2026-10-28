import Batteries.Data.RBMap
import Lean.Elab.Tactic.Omega

/-! Lookup specifications for the pinned upstream storage map erase operation.
No upstream implementation is changed. Rebalancing preserves membership. -/
namespace Solidity.Evm.StorageSlots
open Batteries
open RBNode RBColor

private theorem mem_setRed (x : α) (t : RBNode α) : x ∈ t.setRed ↔ x ∈ t := by
  rw [← RBNode.mem_toList, RBNode.setRed_toList, RBNode.mem_toList]

private theorem mem_balance1 (x : α) (l : RBNode α) (v : α) (r : RBNode α) :
    x ∈ RBNode.balance1 l v r ↔ x = v ∨ x ∈ l ∨ x ∈ r := by
  unfold RBNode.balance1
  split <;> simp only [RBNode.mem_node] <;> simp only [or_assoc, or_left_comm, or_comm]

private theorem mem_balance2 (x : α) (l : RBNode α) (v : α) (r : RBNode α) :
    x ∈ RBNode.balance2 l v r ↔ x = v ∨ x ∈ l ∨ x ∈ r := by
  unfold RBNode.balance2
  split <;> simp only [RBNode.mem_node] <;> simp only [or_assoc, or_left_comm]

private theorem mem_balLeft (x : α) (l : RBNode α) (v : α) (r : RBNode α) :
    x ∈ RBNode.balLeft l v r ↔ x = v ∨ x ∈ l ∨ x ∈ r := by
  unfold RBNode.balLeft
  split <;> (try split) <;>
    simp only [RBNode.mem_node, mem_balance2, mem_setRed, or_assoc, or_left_comm]

private theorem mem_balRight (x : α) (l : RBNode α) (v : α) (r : RBNode α) :
    x ∈ RBNode.balRight l v r ↔ x = v ∨ x ∈ l ∨ x ∈ r := by
  unfold RBNode.balRight
  split <;> (try split) <;>
    simp only [RBNode.mem_node, mem_balance1, mem_setRed, or_assoc, or_left_comm, or_comm]

private theorem append_rr_members (x : α) (a b c d : RBNode α) (v w : α) :
    x ∈ RBNode.append (.node .red a v b) (.node .red c w d) ↔
      x = v ∨ x = w ∨ x ∈ a ∨ x ∈ RBNode.append b c ∨ x ∈ d := by
  rw [RBNode.append.eq_3]
  split <;> simp_all only [RBNode.mem_node, or_assoc, or_left_comm, or_comm]

private theorem append_bb_members (x : α) (a b c d : RBNode α) (v w : α) :
    x ∈ RBNode.append (.node .black a v b) (.node .black c w d) ↔
      x = v ∨ x = w ∨ x ∈ a ∨ x ∈ RBNode.append b c ∨ x ∈ d := by
  rw [RBNode.append.eq_4]
  split <;> simp_all only [RBNode.mem_node, mem_balLeft, or_assoc, or_left_comm, or_comm]

private theorem mem_append (x : α) : ∀ (l r : RBNode α),
    x ∈ RBNode.append l r ↔ x ∈ l ∨ x ∈ r
  | .nil, r => by simp only [RBNode.append.eq_1, RBNode.mem_nil, false_or]
  | .node color a v b, .nil => by
    rw [RBNode.append.eq_2 _ (by intro h; cases h)]
    simp only [RBNode.mem_nil, or_false]
  | .node .red a v b, .node .red c w d => by
    rw [append_rr_members, mem_append x b c]
    simp only [RBNode.mem_node, or_assoc, or_left_comm]
  | .node .black a v b, .node .black c w d => by
    rw [append_bb_members, mem_append x b c]
    simp only [RBNode.mem_node, or_assoc, or_left_comm]
  | .node .black a v b, .node .red c w d => by
    rw [RBNode.append.eq_5, RBNode.mem_node, mem_append x (.node .black a v b) c]
    simp only [RBNode.mem_node, or_assoc, or_left_comm]
  | .node .red a v b, .node .black c w d => by
    rw [RBNode.append.eq_6, RBNode.mem_node, mem_append x b (.node .black c w d)]
    simp only [RBNode.mem_node, or_assoc, or_left_comm]
termination_by l r => l.size + r.size
decreasing_by all_goals simp_wf; omega

private theorem keep_left {p q r n : Prop} (hp : p → n) (hr : r → n) :
    (p ∨ (q ∧ n) ∨ r) ↔ (p ∨ q ∨ r) ∧ n := by
  constructor
  · rintro (h | h | h)
    · exact ⟨Or.inl h, hp h⟩
    · exact ⟨Or.inr (Or.inl h.1), h.2⟩
    · exact ⟨Or.inr (Or.inr h), hr h⟩
  · rintro ⟨h, hn⟩
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, hn⟩)
    · exact Or.inr (Or.inr h)

private theorem keep_right {p q r n : Prop} (hp : p → n) (hq : q → n) :
    (p ∨ q ∨ (r ∧ n)) ↔ (p ∨ q ∨ r) ∧ n := by
  constructor
  · rintro (h | h | h)
    · exact ⟨Or.inl h, hp h⟩
    · exact ⟨Or.inr (Or.inl h), hq h⟩
    · exact ⟨Or.inr (Or.inr h.1), h.2⟩
  · rintro ⟨h, hn⟩
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hn⟩)

private theorem drop_root {p q r n : Prop} (hp : p → ¬ n) (hq : q → n) (hr : r → n) :
    (q ∨ r) ↔ (p ∨ q ∨ r) ∧ n := by
  constructor
  · rintro (h | h)
    · exact ⟨Or.inr (Or.inl h), hq h⟩
    · exact ⟨Or.inr (Or.inr h), hr h⟩
  · rintro ⟨h, hn⟩
    rcases h with h | h | h
    · exact False.elim (hp h hn)
    · exact Or.inl h
    · exact Or.inr h

private theorem mem_del {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [RBNode.IsStrictCut cmp cut] (x : α) (t : RBNode α)
    (ht : t.Ordered cmp) : x ∈ t.del cut ↔ x ∈ t ∧ cut x ≠ .eq := by
  induction t with
  | nil => simp only [RBNode.del, RBNode.mem_nil, false_and]
  | node color l v r ihl ihr =>
    rcases ht with ⟨hlv, hvr, hl, hr⟩
    cases hv : cut v with
    | lt =>
      have hnroot : x = v → cut x ≠ .eq := by
        rintro rfl
        rw [hv]
        decide
      have hnright : x ∈ r → cut x ≠ .eq := by
        intro hx
        have he : cut x = .lt := RBNode.IsCut.lt_trans ((RBNode.All_def.mp hvr x hx).1) hv
        rw [he]
        decide
      have he : x ∈ (RBNode.node color l v r).del cut ↔
          x = v ∨ x ∈ l.del cut ∨ x ∈ r := by
        rw [RBNode.del, hv]
        cases hc : l.isBlack <;> simp only [mem_balLeft, RBNode.mem_node]
      rw [he, ihl hl, RBNode.mem_node]
      exact keep_left hnroot hnright
    | gt =>
      have hnroot : x = v → cut x ≠ .eq := by
        rintro rfl
        rw [hv]
        decide
      have hnleft : x ∈ l → cut x ≠ .eq := by
        intro hx
        have he : cut x = .gt := RBNode.IsCut.gt_trans ((RBNode.All_def.mp hlv x hx).1) hv
        rw [he]
        decide
      have he : x ∈ (RBNode.node color l v r).del cut ↔
          x = v ∨ x ∈ l ∨ x ∈ r.del cut := by
        rw [RBNode.del, hv]
        cases hc : r.isBlack <;> simp only [mem_balRight, RBNode.mem_node]
      rw [he, ihr hr, RBNode.mem_node]
      exact keep_right hnroot hnleft
    | eq =>
      have hnroot : x = v → cut x = .eq := by rintro rfl; exact hv
      have hnleft : x ∈ l → cut x ≠ .eq := by
        intro hx
        have hcmp : cmp v x = .gt := Std.OrientedCmp.gt_iff_lt.mpr (RBNode.All_def.mp hlv x hx).1
        have he : cut x = .gt := (RBNode.IsStrictCut.exact hv).symm.trans hcmp
        rw [he]
        decide
      have hnright : x ∈ r → cut x ≠ .eq := by
        intro hx
        have he : cut x = .lt := (RBNode.IsStrictCut.exact hv).symm.trans (RBNode.All_def.mp hvr x hx).1
        rw [he]
        decide
      rw [RBNode.del, hv, mem_append, RBNode.mem_node]
      exact drop_root (fun hx hn => hn (hnroot hx)) hnleft hnright

/-- Erase removes exactly the matching entry; rotations preserve every other
entry. The premise is the map's actual ordered-tree invariant. -/
theorem mem_erase {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [RBNode.IsStrictCut cmp cut] (x : α) (t : RBNode α)
    (ht : t.Ordered cmp) : x ∈ t.erase cut ↔ x ∈ t ∧ cut x ≠ .eq := by
  unfold RBNode.erase
  rw [← RBNode.mem_toList, RBNode.setBlack_toList, RBNode.mem_toList]
  exact mem_del x t ht

theorem mem_toList_erase {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (t : RBMap α β cmp) (key : α) (entry : α × β) :
    entry ∈ (t.erase key).toList ↔ entry ∈ t.toList ∧ cmp key entry.1 ≠ .eq := by
  change entry ∈ (t.1.erase (fun e => cmp key e.1)).toList ↔
    entry ∈ t.1.toList ∧ cmp key entry.1 ≠ .eq
  rw [RBNode.mem_toList, RBNode.mem_toList]
  exact mem_erase entry t.1 t.2.out.1

/-- Actual map lookup after erase, including absent keys. No functional-store
law is assumed of the upstream implementation. -/
theorem find_some_erase {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (t : RBMap α β cmp) (key query : α) (value : β) :
    (t.erase key).find? query = some value ↔
      t.find? query = some value ∧ cmp key query ≠ .eq := by
  simp only [RBMap.find?_some, mem_toList_erase]
  constructor
  · rintro ⟨k, ⟨hm, hn⟩, he⟩
    refine ⟨⟨k, hm, he⟩, ?_⟩
    rwa [Std.TransCmp.congr_right he]
  · rintro ⟨⟨k, hm, he⟩, hn⟩
    refine ⟨k, ⟨hm, ?_⟩, he⟩
    rwa [← Std.TransCmp.congr_right he]

/-- Total lookup form, useful for the upstream zero-store/erase branch. -/
theorem find_erase {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (t : RBMap α β cmp) (key query : α) :
    (t.erase key).find? query = if cmp key query = .eq then none else t.find? query := by
  apply Option.ext
  intro value
  rw [find_some_erase]
  by_cases h : cmp key query = .eq
  · rw [if_pos h]
    constructor
    · intro hh
      exact False.elim (hh.2 h)
    · intro hh
      cases hh
  · rw [if_neg h]
    exact ⟨And.left, fun hh => ⟨hh, h⟩⟩

/-- info: 'Solidity.Evm.StorageSlots.mem_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_erase
/-- info: 'Solidity.Evm.StorageSlots.find_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms find_erase

end Solidity.Evm.StorageSlots

