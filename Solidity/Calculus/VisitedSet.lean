/-!
# A visited set with logarithmic membership

The decisions of `Calculus/LinearDecision.lean` and
`Calculus/PresburgerDecision.lean` walk a finite graph of formulas and must
know whether a formula was seen before.  A list makes that linear in the
states found, and the walk quadratic.  `HSet` is a binary search tree keyed
by a hash (a `Nat`, so the kernel reduces it), each key holding the
elements that hash to it: membership is a walk down the tree, then a
comparison with the few elements of one bucket.

Only soundness is proved: `contains` says `true` only of an element the
set holds (`HSet.mem_of_contains`), and `insert` adds exactly its element
(`HSet.mem_insert`).  A `false` that should be `true` (a bad hash cannot
cause one, the keys are compared exactly) would cost a repeated state, not
a wrong answer, so the ordering invariant is not stated.  Hashes are
pseudo-random, so the tree stays shallow without rebalancing.
-/

namespace Solidity.Linear

/-- Elements bucketed by a hash key, in a binary search tree on the key. -/
inductive HSet (α : Type) where
  | leaf
  | node (l : HSet α) (k : Nat) (b : List α) (r : HSet α)
  deriving Inhabited

namespace HSet

variable {α : Type}

/-- Held somewhere in the tree. -/
def Mem (a : α) : HSet α → Prop
  | .leaf => False
  | .node l _ b r => Mem a l ∨ a ∈ b ∨ Mem a r

/-- Look `a` up under the key `k`. -/
def contains [DecidableEq α] (k : Nat) (a : α) : HSet α → Bool
  | .leaf => false
  | .node l k' b r =>
    if k < k' then contains k a l else if k' < k then contains k a r else decide (a ∈ b)

/-- Add `a` under the key `k`. -/
def insert (k : Nat) (a : α) : HSet α → HSet α
  | .leaf => .node .leaf k [a] .leaf
  | .node l k' b r =>
    if k < k' then .node (insert k a l) k' b r
    else if k' < k then .node l k' b (insert k a r)
    else .node l k' (a :: b) r

/-- Every element. -/
def toList : HSet α → List α
  | .leaf => []
  | .node l _ b r => l.toList ++ b ++ r.toList

theorem mem_toList {a : α} : ∀ {t : HSet α}, a ∈ t.toList ↔ t.Mem a
  | .leaf => by simp only [toList, List.not_mem_nil, Mem]
  | .node l _ b r => by simp only [toList, List.mem_append, mem_toList, Mem, or_assoc]

/-- An element under the key `k` that `p` accepts. -/
def find? (k : Nat) (p : α → Bool) : HSet α → Option α
  | .leaf => none
  | .node l k' b r =>
    if k < k' then find? k p l else if k' < k then find? k p r else b.find? p

theorem find?_some {k : Nat} {p : α → Bool} {a : α} : ∀ {t : HSet α}, t.find? k p = some a →
    t.Mem a ∧ p a = true
  | .leaf, h => by simp only [find?, reduceCtorEq] at h
  | .node l k' b r, h => by
    simp only [find?] at h
    split at h
    · exact ⟨.inl (find?_some h).1, (find?_some h).2⟩
    · split at h
      · exact ⟨.inr (.inr (find?_some h).1), (find?_some h).2⟩
      · exact ⟨.inr (.inl (List.mem_of_find?_eq_some h)), List.find?_some h⟩

theorem mem_of_contains [DecidableEq α] {k : Nat} {a : α} : ∀ {t : HSet α}, t.contains k a = true → t.Mem a
  | .leaf, h => by simp only [contains, Bool.false_eq_true] at h
  | .node l k' b r, h => by
    simp only [contains] at h
    split at h
    · exact .inl (mem_of_contains h)
    · split at h
      · exact .inr (.inr (mem_of_contains h))
      · exact .inr (.inl (of_decide_eq_true h))

theorem mem_insert {k : Nat} {a x : α} : ∀ {t : HSet α}, (t.insert k a).Mem x ↔ x = a ∨ t.Mem x
  | .leaf => by simp only [insert, Mem, List.mem_singleton, or_false, false_or]
  | .node l k' b r => by
    simp only [insert]
    split
    · simp only [Mem, mem_insert]; grind
    · split
      · simp only [Mem, mem_insert]; grind
      · simp only [Mem, List.mem_cons]; grind

end HSet

/-! ## A depth-first walk

`walk` visits the states reachable from a worklist, a state seen once
(`HSet`, keyed by `hash`), and stops at the first node `ok` refuses.  The
nodes carry what their states do not (an assignment reconstruction, a
proof); `st` reads a node's state.  If the walk closes, every state it
holds is a checked node's, all of whose children it holds
(`walk_closed`).  The fuel is not proved to suffice: a caller falls back
to a search whose bound is proved. -/

section Walk

variable {σ N : Type} [DecidableEq σ] (st : N → σ) (hash : σ → Nat) (kids : N → List N)
  (ok : N → Bool)

/-- How a walk ends. -/
inductive Walk (σ N : Type) where
  | closed (V : HSet σ)
  | refuted (n : N)
  | out

/-- Push the nodes whose state is not seen yet. -/
def pushNew : List N → HSet σ → List N → HSet σ × List N
  | [], V, W => (V, W)
  | c :: cs, V, W =>
    if V.contains (hash (st c)) (st c) then pushNew cs V W
    else pushNew cs (V.insert (hash (st c)) (st c)) (c :: W)

/-- **The walk**, depth first, stopping at the first node `ok` refuses. -/
def walk : Nat → HSet σ → List N → Walk σ N
  | 0, _, _ => .out
  | _ + 1, V, [] => .closed V
  | fuel + 1, V, n :: W =>
    if ok n then
      let p := pushNew st hash (kids n) V W
      walk fuel p.1 p.2
    else .refuted n

theorem pushNew_spec : ∀ (cs : List N) (V : HSet σ) (W : List N),
    (∀ s, V.Mem s → (pushNew st hash cs V W).1.Mem s) ∧
    (∀ c ∈ cs, (pushNew st hash cs V W).1.Mem (st c)) ∧
    (∀ r ∈ (pushNew st hash cs V W).2, r ∈ W ∨ r ∈ cs) ∧
    (∀ r ∈ W, r ∈ (pushNew st hash cs V W).2) ∧
    (∀ s, (pushNew st hash cs V W).1.Mem s → V.Mem s ∨ ∃ r ∈ (pushNew st hash cs V W).2, st r = s)
  | [], V, W => ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil, fun _ h => Or.inl h,
      fun _ h => h, fun _ h => Or.inl h⟩
  | c :: cs, V, W => by
    simp only [pushNew]
    split
    · next hc =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := pushNew_spec cs V W
      refine ⟨h1, fun c' hc' => ?_, fun r hr => ?_, h4, h5⟩
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact h1 _ (HSet.mem_of_contains hc)
        · exact h2 c' hc'
      · rcases h3 r hr with h | h
        · exact .inl h
        · exact .inr (.tail _ h)
    · obtain ⟨h1, h2, h3, h4, h5⟩ := pushNew_spec cs (V.insert (hash (st c)) (st c)) (c :: W)
      refine ⟨fun s hs => h1 s (HSet.mem_insert.2 (.inr hs)), fun c' hc' => ?_, fun r hr => ?_,
        fun r hr => h4 r (.tail _ hr), fun s hs => ?_⟩
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact h1 _ (HSet.mem_insert.2 (.inl rfl))
        · exact h2 c' hc'
      · rcases h3 r hr with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr (.head _)
          · exact .inl h
        · exact .inr (.tail _ h)
      · rcases h5 s hs with h | h
        · rcases HSet.mem_insert.1 h with rfl | h
          · exact .inr ⟨c, h4 c (.head _), rfl⟩
          · exact .inl h
        · exact .inr h

/-- A state done: some checked node's, all of whose children are seen. -/
def Done (V : HSet σ) (s : σ) : Prop := ∃ n, st n = s ∧ ok n = true ∧ ∀ c ∈ kids n, V.Mem (st c)

/-- The walk's invariant: the worklist is seen, and a seen state is waiting
or done. -/
def WalkInv (V : HSet σ) (W : List N) : Prop :=
  (∀ n ∈ W, V.Mem (st n)) ∧ ∀ s, V.Mem s → (∃ n ∈ W, st n = s) ∨ Done st kids ok V s

omit [DecidableEq σ] in
/-- The invariant at the start: one node, its state alone seen. -/
theorem walkInv_initial (n : N) : WalkInv st kids ok (HSet.leaf.insert (hash (st n)) (st n)) [n] := by
  refine ⟨fun r hr => ?_, fun s hs => ?_⟩
  · rw [List.mem_singleton.1 hr]; exact HSet.mem_insert.2 (.inl rfl)
  · rcases HSet.mem_insert.1 hs with rfl | hs
    · exact .inl ⟨n, .head _, rfl⟩
    · exact hs.elim

/-- **What a closed walk returns**: it keeps what was seen, and every state
it holds is done. -/
theorem walk_closed : ∀ (fuel : Nat) (V : HSet σ) (W : List N) (V' : HSet σ),
    walk st hash kids ok fuel V W = .closed V' → WalkInv st kids ok V W →
    (∀ s, V.Mem s → V'.Mem s) ∧ ∀ s, V'.Mem s → Done st kids ok V' s
  | 0, _, _, _, h, _ => by simp only [walk, reduceCtorEq] at h
  | _ + 1, V, [], V', h, hI => by
    simp only [walk, Walk.closed.injEq] at h
    subst h
    refine ⟨fun _ h => h, fun s hs => (hI.2 s hs).resolve_left ?_⟩
    simp only [List.not_mem_nil, false_and, exists_false, not_false_eq_true]
  | fuel + 1, V, n :: W, V', h, hI => by
    simp only [walk] at h
    split at h
    · next hz =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := pushNew_spec st hash (kids n) V W
      have mono : ∀ s, Done st kids ok V s → Done st kids ok (pushNew st hash (kids n) V W).1 s :=
        fun s ⟨m, hm, hk, hs⟩ => ⟨m, hm, hk, fun c hc => h1 _ (hs c hc)⟩
      have ih := walk_closed fuel _ _ V' h ⟨fun r' hr' => ?_, fun s hs => ?_⟩
      · exact ⟨fun s hs => ih.1 s (h1 s hs), ih.2⟩
      · rcases h3 r' hr' with h' | h'
        · exact h1 _ (hI.1 r' (.tail _ h'))
        · exact h2 r' h'
      · rcases h5 s hs with h' | h'
        · rcases hI.2 s h' with ⟨r'', hr'', rfl⟩ | hd
          · rcases List.mem_cons.1 hr'' with rfl | hr''
            · exact .inr ⟨r'', rfl, hz, h2⟩
            · exact .inl ⟨r'', h4 r'' hr'', rfl⟩
          · exact .inr (mono s hd)
        · exact .inl h'
    · cases h

/-- A refuting walk stops at a node `ok` refuses. -/
theorem walk_refuted : ∀ (fuel : Nat) (V : HSet σ) (W : List N) (r : N),
    walk st hash kids ok fuel V W = .refuted r → ok r = false
  | 0, _, _, _, h => by simp only [walk, reduceCtorEq] at h
  | _ + 1, V, [], _, h => by simp only [walk, reduceCtorEq] at h
  | fuel + 1, V, r' :: W, r, h => by
    simp only [walk] at h
    split at h
    · exact walk_refuted fuel _ _ r h
    · next hz => simp only [Walk.refuted.injEq] at h; subst h; simpa only [Bool.not_eq_true] using hz

/-! A walk whose check threads a cache (a memo of an expensive test): with
a cache `Good` keeps, and a check that agrees with `ok` on it, it is the
walk (`walkC_eq`). -/

variable {Cache : Type} (okC : Cache → N → Bool × Cache)

/-- The walk, its check threading a cache. -/
def walkC : Nat → Cache → HSet σ → List N → Walk σ N
  | 0, _, _, _ => .out
  | _ + 1, _, V, [] => .closed V
  | fuel + 1, c, V, n :: W =>
    if (okC c n).1 then
      let p := pushNew st hash (kids n) V W
      walkC fuel (okC c n).2 p.1 p.2
    else .refuted n

theorem walkC_eq (Good : Cache → Prop)
    (hok : ∀ c n, Good c → (okC c n).1 = ok n ∧ Good (okC c n).2) :
    ∀ (fuel : Nat) (c : Cache) (V : HSet σ) (W : List N), Good c →
      walkC st hash kids okC fuel c V W = walk st hash kids ok fuel V W
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, [], _ => rfl
  | fuel + 1, c, V, n :: W, hc => by
    simp only [walkC, walk, (hok c n hc).1]
    split
    · exact walkC_eq Good hok fuel _ _ _ (hok c n hc).2
    · rfl

end Walk

end Solidity.Linear
