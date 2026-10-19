import Solidity.Calculus.RewriteLaws
import Solidity.Calculus.TermSize
import Solidity.Theory.Typed.Leaves
import Solidity.Calculus.CloseLemmas

/-!
# A storage write of a whole value, expanded to its words

Lean only: four exact rewrites of a storage term, each a write of a value
spelled as the writes of its words (`Theory/Typed/Leaves.lean`), so that
the closer, which reads a word back from a `save` of that word, sees one:

| link | term ⇝ term | by |
|---|---|---|
| `delAtExpand` | `delAt(s, p)` ⇝ `save(…save(s, p.l₁, 0)…, p.lₙ, 0)` | `Storage.delete_expand` |
| `copyExpand` | `save(s, p, find(s, q))` ⇝ `save(…save(s, p.l₁, select(s, q.l₁))…, p.lₙ, select(s, q.lₙ))` | `Storage.write_find_expand` |
| `pushExpand` | `push(s, p, v)` ⇝ `save(pushSlot(s, p), p[p.length]@s, v)` | `Storage.push_prim` |
| `popExpand` | `pop(s, p)` ⇝ `shrink(save(s, p[p.length - 1]@s, 0), p)` | `Storage.pop_prim` |

`p.lᵢ` are the leaves of the written type (`Ty.leaves`), a member by `.f`
(unchecked, as the program's) and a fixed array's element by `p[i]@s`, its
bound checked in `s` (`atIn`): the storage the write lands on, where an
in-range index of a fixed array always passes.  The index of a push is the
unchecked slot past the end, `p[p.length]@s` (`nextIn`), the index of a pop
the last live element, `p[p.length - 1]@s`, its `- 1` reverting on an empty
array, as the pop does.

**When each fires** (`Tm.expand?`).  A `delete`, a copy at a type of finite
shape (`Ty.finiteShape`: no dynamic array outside a mapping) with between
one and `expandBound` words (`Ty.expandable`, counted without listing them,
`Ty.leafCountAt`, so a `uint[2^200]` is refused in one multiplication); the
copy only at a reference type, and only from the storage it is written to;
a push and a pop only of an array of words.  No argument pushes
(`Tm.pushFree`), so no side is ever out of gas, but the push's own: a full
array is out of gas on both sides (`Tm.exhB_pushExpand`).

**Why it is exact** (`Tm.eval_expand?`): every term reads alike before and
after in every typed state, including where it reverts, so the rewrite of an
update's right-hand sides is an equivalence under either modality
(`holds_upd_expand_iff`, by `Upd.rwBy_afterT`).

**How much it grows** (`Tm.spineSaves_expand?`): at most `expandBound` more
`save`s on the storage spine; a fixed array's element path repeats `s`.

These functions run once a link and use `match` on the indexed families,
under the exemption of `Calculus/RewriteScoped.lean`'s walks (proposal 104).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (structDef lookupBy)

variable {C : Contract}

/-! ## Which types expand -/

/-- The most words one expansion writes. -/
def expandBound : Nat := 64

/-- `Ty.leaves`' length with fuel `k`, by arithmetic: a fixed array's is its
length times its element's. -/
def Ty.leafCountAt : Nat → Ty → Nat
  | 0, _ => 0
  | _ + 1, .prim _ => 1
  | k + 1, .ref (.struct s) => ((structDef s).map fun fT => Ty.leafCountAt k fT.2).sum
  | k + 1, .ref (.fixed E n) => n * Ty.leafCountAt k E
  | _ + 1, .ref (.array _) => 0
  | _ + 1, .ref (.mapping _ _) => 0

/-- A type a `delete` or a copy at expands at: of finite shape, with between
one and `expandBound` words. -/
def Ty.expandable (T : Ty) : Bool :=
  T.finiteShape && Nat.blt 0 (Ty.leafCountAt (rankBound T + 1) T) &&
    Nat.ble (Ty.leafCountAt (rankBound T + 1) T) expandBound

theorem sum_replicate_nat (c : Nat) : (n : Nat) → (List.replicate n c).sum = n * c
  | 0 => by simp only [List.replicate, List.sum_nil, Nat.zero_mul]
  | n + 1 => by
    rw [List.replicate_succ, List.sum_cons, sum_replicate_nat c n, Nat.succ_mul, Nat.add_comm]

/-- `Ty.leafCountAt` counts `Ty.leavesAt`. -/
theorem Ty.length_leavesAt : (k : Nat) → (T : Ty) → (Ty.leavesAt k T).length = Ty.leafCountAt k T
  | 0, _ => rfl
  | _ + 1, .prim _ => rfl
  | k + 1, .ref (.struct s) => by
    simp only [Ty.leavesAt, Ty.leafCountAt, List.length_flatMap, List.length_map,
      Ty.length_leavesAt k, List.map_attach_eq_pmap, List.pmap_eq_map]
  | k + 1, .ref (.fixed E n) => by
    simp only [Ty.leavesAt, Ty.leafCountAt, List.length_flatMap, List.length_map,
      Ty.length_leavesAt k, List.map_const', List.length_range, sum_replicate_nat]
  | _ + 1, .ref (.array _) => rfl
  | _ + 1, .ref (.mapping _ _) => rfl

/-- What an expandable type is: of finite shape, with between one and
`expandBound` leaves. -/
theorem Ty.expandable_spec {T : Ty} (h : T.expandable = true) :
    T.Finite ∧ T.leaves ≠ [] ∧ T.leafCount ≤ expandBound := by
  simp only [Ty.expandable, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  have hc : T.leafCount = Ty.leafCountAt (rankBound T + 1) T := Ty.length_leavesAt _ T
  refine ⟨Ty.finite_of_finiteShape h.1.1, fun he => ?_, hc ▸ h.2⟩
  have h0 : T.leafCount = 0 := by simp only [Ty.leafCount, he, List.length_nil]
  omega

/-! ## The terms written -/

section Terms

variable {Γ : Ctx}

/-- The path `p` followed by `l`: a member by `.f`, an index by `p[i]@s`. -/
def Tm.leafPath (s : Tm C Γ .st) : {T U : Ty} → Tm C Γ (.path T) → Path T U → Tm C Γ (.path U)
  | _, _, p, .nil => p
  | _, _, p, .field h l => Tm.leafPath s (.app1 (.field h) p) l
  | _, _, p, .atF i l => Tm.leafPath s (.app3 (.atIn (.arr .fixed)) s p (.app0 (.lit i))) l
  | _, _, p, .at i l => Tm.leafPath s (.app3 (.atIn (.arr .dyn)) s p (.app0 (.lit i))) l
  | _, _, p, .key k l => Tm.leafPath s (.app3 (.atIn .map) s p (.app0 (.lit k))) l

/-- `acc` with each leaf of `ls` below `p` saved, the first innermost, the
value `val l` at the leaf `l`. -/
def Tm.saveLeaves (s : Tm C Γ .st) {T : Ty} (p : Tm C Γ (.path T))
    (val : (l : Leaf T) → Tm C Γ (.sv (.prim l.1))) : List (Leaf T) → Tm C Γ .st → Tm C Γ .st
  | [], acc => acc
  | l :: ls, acc => Tm.saveLeaves s p val ls (.app3 .save acc (Tm.leafPath s p l.2) (val l))

/-- `sval(dflt)`: a word's default. -/
def Tm.dfltWord (P : PrimTy) : Tm C Γ (.sv (.prim P)) := .app1 .sval (.app0 (.lit (PrimTy.dflt P)))

/-- `delAt(s, p)` expanded: each leaf saved at its default. -/
def Tm.delAtLeaves (s : Tm C Γ .st) {T : Ty} (p : Tm C Γ (.path T)) : Tm C Γ .st :=
  Tm.saveLeaves s p (fun l => Tm.dfltWord l.1) T.leaves s

/-- `save(s, p, find(s, q))` expanded: each leaf saved at the source's word,
read in `s`. -/
def Tm.copyLeaves (s : Tm C Γ .st) {T : Ty} (p q : Tm C Γ (.path T)) : Tm C Γ .st :=
  Tm.saveLeaves s p (fun l => .app1 .sval (.app2 .find s (Tm.leafPath s q l.2))) T.leaves s

/-- `push(s, p, sval(x))` expanded: one more slot, the word saved at it. -/
def Tm.pushWord (s : Tm C Γ .st) {P : PrimTy} (p : Tm C Γ (.path (.ref (.array (.prim P)))))
    (x : Tm C Γ (.val P)) : Tm C Γ .st :=
  .app3 .save (.app2 .pushSlot s p) (.app2 .nextIn s p) (.app1 .sval x)

/-- `len(s, p) - 1`. -/
def Tm.lastIdx (s : Tm C Γ .st) {E : Ty} (p : Tm C Γ (.path (.ref (.array E)))) :
    Tm C Γ (.val .uint) :=
  .app2 (.binop .sub rfl) (.app2 .len s p) (.app0 (.lit ⟨1, rfl⟩))

/-- `pop(s, p)` expanded: the last word reset, then the length shrunk. -/
def Tm.popWord (s : Tm C Γ .st) {P : PrimTy} (p : Tm C Γ (.path (.ref (.array (.prim P))))) :
    Tm C Γ .st :=
  .app2 .shrink (.app3 .save s (.app3 (.atIn (.arr .dyn)) s p (Tm.lastIdx s p)) (Tm.dfltWord P)) p

end Terms

/-! ## The rewrites -/

/-- The four expansions, one a chain link each. -/
inductive ExpandKind where
  | delAt
  | copy
  | push
  | pop
  deriving DecidableEq, Repr

section Expand

variable {Γ : Ctx}

/-- `delAtExpand`: `delAt(s, p)` at an expandable type. -/
def Tm.delAtExpand? : Tm C Γ .st → Option (Tm C Γ .st)
  | .app2 (@Op2.delAt _ T) s p =>
    if (T.expandable && s.pushFree && p.pushFree) = true then some (Tm.delAtLeaves s p) else none
  | _ => none

/-- `sval(x)`'s word, at its type. -/
def Tm.asSval? : {k : Srt} → Tm C Γ k → Option ((P : PrimTy) × Tm C Γ (.val P))
  | _, .app1 (@Op1.sval _ P) x => some ⟨P, x⟩
  | _, _ => none

/-- `find(s, q)`'s storage and path, at its type. -/
def Tm.asSfind? : {k : Srt} → Tm C Γ k → Option ((T : Ty) × Tm C Γ .st × Tm C Γ (.path T))
  | _, .app2 (@Op2.sfind _ T) s q => some ⟨T, s, q⟩
  | _, _ => none

/-- `save(s, p, v)`'s arguments, at their type. -/
def Tm.asSave? : {k : Srt} → Tm C Γ k →
    Option ((T : Ty) × Tm C Γ .st × Tm C Γ (.path T) × Tm C Γ (.sv T))
  | _, .app3 (@Op3.save _ T) s p v => some ⟨T, s, p, v⟩
  | _, _ => none

/-- `push(s, p, v)`'s arguments, at their type. -/
def Tm.asPush? : {k : Srt} → Tm C Γ k →
    Option ((E : Ty) × Tm C Γ .st × Tm C Γ (.path (.ref (.array E))) × Tm C Γ (.sv E))
  | _, .app3 (@Op3.push _ E) s p v => some ⟨E, s, p, v⟩
  | _, _ => none

/-- `copyExpand`: `save(s, p, find(s, q))` at an expandable type that is no
word. -/
def Tm.copyExpand? (t : Tm C Γ .st) : Option (Tm C Γ .st) :=
  match t.asSave? with
  | some ⟨T, s, p, v⟩ =>
    match v.asSfind? with
    | some ⟨T', s', q⟩ =>
      if h : T' = T then
        if (!T.isPrimitive && T.expandable && s.beqR s' && s.pushFree && p.pushFree &&
            q.pushFree) = true then
          some (Tm.copyLeaves s p (h ▸ q))
        else none
      else none
    | none => none
  | none => none

/-- `pushExpand`: `push(s, p, sval(x))` of a word. -/
def Tm.pushExpand? (t : Tm C Γ .st) : Option (Tm C Γ .st) :=
  match t.asPush? with
  | some ⟨E, s, p, v⟩ =>
    match v.asSval? with
    | some ⟨P, x⟩ =>
      if h : E = .prim P then
        if (s.pushFree && p.pushFree && x.pushFree) = true then some (Tm.pushWord s (h ▸ p) x)
        else none
      else none
    | none => none
  | none => none

/-- `popExpand`: `pop(s, p)` of a word. -/
def Tm.popExpand? : Tm C Γ .st → Option (Tm C Γ .st)
  | .app2 (@Op2.pop _ (.prim _)) s p =>
    if (s.pushFree && p.pushFree) = true then some (Tm.popWord s p) else none
  | _ => none

/-- The expansion of the kind `k`. -/
def Tm.expandK? : ExpandKind → Tm C Γ .st → Option (Tm C Γ .st)
  | .delAt => Tm.delAtExpand?
  | .copy => Tm.copyExpand?
  | .push => Tm.pushExpand?
  | .pop => Tm.popExpand?

/-- **The expansion of a storage term at its head**, the first kind that
fires. -/
def Tm.expand? (t : Tm C Γ .st) : Option (Tm C Γ .st) :=
  (t.delAtExpand? <|> t.copyExpand?) <|> (t.pushExpand? <|> t.popExpand?)

/-- The expansion of the kind `k` at any sort: at a storage term's head. -/
def Tm.pickExpand (k : ExpandKind) : {s : Srt} → Tm C Γ s → Option (Tm C Γ s)
  | .st, t => Tm.expandK? k t
  | _, _ => none

end Expand

/-! ## The paths to the leaves, read -/

section LeafPath

variable {Γ : Ctx} (σ : State C Γ)

theorem Tm.eval_atIn {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (s : Tm C Γ .st)
    (p : Tm C Γ (.path (.ref R))) (i : Tm C Γ (.val k)) :
    (Tm.app3 (.atIn it) s p i).eval σ =
      (s.eval σ).bind fun st => (p.eval σ).bind fun r => (i.eval σ).bind fun j => st.atT it r j :=
  rfl

/-- Where `p[i]@s` returns, it returns `p`'s reference indexed. -/
theorem Tm.eval_atIn_lit {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (s : Tm C Γ .st)
    (p : Tm C Γ (.path (.ref R))) (i : k.Denote) {r : SRef C (.ref R)} (hp : p.eval σ = some r)
    {r₀ : SRef C V} (h : (Tm.app3 (.atIn it) s p (.app0 (.lit i))).eval σ = some r₀) :
    r₀ = r.index it i := by
  rw [Tm.eval_atIn, hp] at h
  cases hs : s.eval σ with
  | none => rw [hs] at h; cases h
  | some st =>
    rw [hs] at h
    simp only [Option.bind_some, Tm.eval_app0] at h
    change (st.atT it r i) = some r₀ at h
    simp only [Storage.atT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, _, h⟩ := h
    exact h.symm

/-- A path from nowhere leads nowhere. -/
theorem Tm.eval_leafPath_none (s : Tm C Γ .st) : {T U : Ty} → (p : Tm C Γ (.path T)) →
    (l : Path T U) → p.eval σ = none → (Tm.leafPath s p l).eval σ = none
  | _, _, _, .nil, hp => hp
  | _, _, p, .field h l, hp => Tm.eval_leafPath_none s _ l (by
      rw [Tm.eval_app1, Close.Op1.eval_field, hp]; rfl)
  | _, _, p, .atF i l, hp => Tm.eval_leafPath_none s _ l (by
      rw [Tm.eval_atIn, hp]; cases s.eval σ <;> rfl)
  | _, _, p, .at i l, hp => Tm.eval_leafPath_none s _ l (by
      rw [Tm.eval_atIn, hp]; cases s.eval σ <;> rfl)
  | _, _, p, .key k l, hp => Tm.eval_leafPath_none s _ l (by
      rw [Tm.eval_atIn, hp]; cases s.eval σ <;> rfl)

/-- Where a path to a leaf returns, it returns the reference followed by the
leaf's path. -/
theorem Tm.eval_leafPath_sub (s : Tm C Γ .st) : {T U : Ty} → (p : Tm C Γ (.path T)) →
    (l : Path T U) → {r : SRef C T} → p.eval σ = some r → {r' : SRef C U} →
    (Tm.leafPath s p l).eval σ = some r' → r' = r.append l
  | _, _, _, .nil, r, hp, r', h => by
    rw [Tm.leafPath, hp] at h
    cases h
    exact (SRef.append_nil r).symm
  | _, _, p, .field h l, r, hp, r', hr => by
    have hp' : (Tm.app1 (.field h) p).eval σ = some (r.append (.field h .nil)) := by
      rw [Tm.eval_app1, Close.Op1.eval_field, hp]; rfl
    rw [Tm.eval_leafPath_sub s _ l hp' hr, SRef.append_append, Path.append_field, Path.append_nil]
  | _, _, p, .atF i l, r, hp, r', hr => by
    have hr₀ : ∀ r₀, (Tm.app3 (.atIn (.arr .fixed)) s p (.app0 (.lit i))).eval σ = some r₀ →
        r₀ = r.append (.atF i .nil) := fun r₀ h => Tm.eval_atIn_lit σ (.arr .fixed) s p i hp h |>.trans (by simp only [SRef.index, Path.index_fixed])
    rw [Tm.leafPath] at hr
    cases h₀ : (Tm.app3 (.atIn (.arr .fixed)) s p (.app0 (.lit i))).eval σ with
    | none => rw [Tm.eval_leafPath_none σ s _ l h₀] at hr; cases hr
    | some r₀ =>
      rw [Tm.eval_leafPath_sub s _ l h₀ hr, hr₀ r₀ h₀, SRef.append_append, Path.append_atF, Path.append_nil]
  | _, _, p, .at i l, r, hp, r', hr => by
    have hr₀ : ∀ r₀, (Tm.app3 (.atIn (.arr .dyn)) s p (.app0 (.lit i))).eval σ = some r₀ →
        r₀ = r.append (.at i .nil) := fun r₀ h => Tm.eval_atIn_lit σ (.arr .dyn) s p i hp h |>.trans (by simp only [SRef.index, Path.index_dyn])
    rw [Tm.leafPath] at hr
    cases h₀ : (Tm.app3 (.atIn (.arr .dyn)) s p (.app0 (.lit i))).eval σ with
    | none => rw [Tm.eval_leafPath_none σ s _ l h₀] at hr; cases hr
    | some r₀ =>
      rw [Tm.eval_leafPath_sub s _ l h₀ hr, hr₀ r₀ h₀, SRef.append_append, Path.append_at, Path.append_nil]
  | _, _, p, .key k l, r, hp, r', hr => by
    have hr₀ : ∀ r₀, (Tm.app3 (.atIn .map) s p (.app0 (.lit k))).eval σ = some r₀ →
        r₀ = r.append (.key k .nil) := fun r₀ h => Tm.eval_atIn_lit σ .map s p k hp h |>.trans (by simp only [SRef.index, Path.index_map])
    rw [Tm.leafPath] at hr
    cases h₀ : (Tm.app3 (.atIn .map) s p (.app0 (.lit k))).eval σ with
    | none => rw [Tm.eval_leafPath_none σ s _ l h₀] at hr; cases hr
    | some r₀ =>
      rw [Tm.eval_leafPath_sub s _ l h₀ hr, hr₀ r₀ h₀, SRef.append_append, Path.append_key, Path.append_nil]

/-- A direct path to something there returns the reference followed by it. -/
theorem Tm.eval_leafPath_some (s : Tm C Γ .st) {st : Storage C} (hs : s.eval σ = some st) :
    {T U : Ty} → (p : Tm C Γ (.path T)) → (l : Path T U) → l.direct = true →
    {r : SRef C T} → p.eval σ = some r → (st.find (r.append l)).isSome = true →
    (Tm.leafPath s p l).eval σ = some (r.append l)
  | _, _, _, .nil, _, r, hp, _ => by rw [Tm.leafPath, hp, SRef.append_nil]
  | _, _, p, .field h l, hd, r, hp, hf => by
    have hp' : (Tm.app1 (.field h) p).eval σ = some (r.append (.field h .nil)) := by
      rw [Tm.eval_app1, Close.Op1.eval_field, hp]; rfl
    have he : r.append (.field h l) = (r.append (.field h .nil)).append l := by
      rw [SRef.append_append, Path.append_field, Path.append_nil]
    rw [he] at hf ⊢
    exact Tm.eval_leafPath_some s hs _ l hd hp' hf
  | _, _, p, .atF i l, hd, r, hp, hf => by
    have he : r.append (.atF i l) = (r.append (.atF i .nil)).append l := by
      rw [SRef.append_append, Path.append_atF, Path.append_nil]
    rw [he] at hf ⊢
    have hp' : (Tm.app3 (.atIn (.arr .fixed)) s p (.app0 (.lit i))).eval σ =
        some (r.append (.atF i .nil)) := by
      have hf₁ : (st.find (r.append (.atF i .nil))).isSome = true := by
        rw [Storage.find_appendM] at hf
        cases h : st.find (r.append (.atF i .nil)) with
        | none => rw [h] at hf; cases hf
        | some _ => rfl
      rw [Storage.find_appendM] at hf₁
      rw [Tm.eval_atIn, hs, hp]
      cases hv : st.find r with
      | none => rw [hv] at hf₁; cases hf₁
      | some v =>
        cases v with
        | fixed e =>
          rw [hv, Option.bind_some, SVal.findM_atF'] at hf₁
          have hi : i.1.toNat < e.toList.length := by
            cases h : e.toList[i.1.toNat]? with
            | none => rw [h] at hf₁; cases hf₁
            | some _ => exact (List.getElem?_eq_some_iff.1 h).1
          rw [SVec.length_toList] at hi
          show Storage.atT st _ r i = _
          simp only [Storage.atT, Storage.checkIndex, hv, Option.bind_eq_bind, Option.bind_some]
          show (if i.1.toNat < _ then some () else none).bind
            (fun _ => some (r.index (IndexTy.arr ArrTy.fixed) i)) = _
          rw [if_pos hi, Option.bind_some, SRef.index, Path.index_fixed]
    exact Tm.eval_leafPath_some s hs _ l hd hp' hf
  | _, _, _, .at _ _, hd, _, _, _ => by simp only [Path.direct, Bool.false_eq_true] at hd
  | _, _, _, .key _ _, hd, _, _, _ => by simp only [Path.direct, Bool.false_eq_true] at hd

end LeafPath

/-! ## The saves of the leaves, read -/

/-- A word written below a reference that finds nothing reverts. -/
theorem Storage.write_append_none {T U : Ty} {st : Storage C} {r : SRef C T}
    (hf : st.find r = none) (q : Path T U) (w : SVal U) (hw : w.isPrim = true) :
    st.write (r.append q) w = none := by
  have hq : st.find (r.append q) = none := by rw [Storage.find_appendM, hf]; rfl
  unfold Storage.write
  rw [if_pos hw]
  cases h : st.save (r.append q) w with
  | none => rfl
  | some _ =>
    have := Storage.find_of_save h
    rw [hq] at this
    cases this

section Saves

variable {Γ : Ctx} (σ : State C Γ)

variable (s : Tm C Γ .st) {T : Ty} (p : Tm C Γ (.path T))
  (val : (l : Leaf T) → Tm C Γ (.sv (.prim l.1)))

/-- Saves on a storage that reverts revert. -/
theorem Tm.eval_saveLeaves_none : (ls : List (Leaf T)) → (acc : Tm C Γ .st) → acc.eval σ = none →
    (Tm.saveLeaves s p val ls acc).eval σ = none
  | [], _, h => h
  | _ :: ls, _, h => Tm.eval_saveLeaves_none ls _ (by rw [Tm.eval_save, h]; rfl)

/-- A leaf's save on `s` below a reference that finds nothing reverts. -/
theorem Tm.eval_saveLeaf_none {st : Storage C} {r : SRef C T} (hs : s.eval σ = some st)
    (hp : p.eval σ = some r) (hf : st.find r = none) (l : Leaf T) :
    (Tm.app3 .save s (Tm.leafPath s p l.2) (val l)).eval σ = none := by
  rw [Tm.eval_save, hs, Option.bind_some]
  cases hl : (Tm.leafPath s p l.2).eval σ with
  | none => rfl
  | some r' =>
    rw [Tm.eval_leafPath_sub σ s p l.2 hp hl, Option.bind_some]
    cases (val l).eval σ with
    | none => rfl
    | some w => exact Storage.write_append_none hf l.2 w rfl

/-- **The saves of the leaves below a reference that finds a value are the
writes of their words**, one after the other. -/
theorem Tm.eval_saveLeaves {st : Storage C} {r : SRef C T} (hs : s.eval σ = some st)
    (hp : p.eval σ = some r) {x : SVal T} (hx : st.find r = some x)
    (vo : (l : Leaf T) → Option (SVal (.prim l.1))) :
    (ls : List (Leaf T)) → (∀ l ∈ ls, l.2.direct = true ∧ l.2.out = false) →
    (∀ l ∈ ls, (val l).eval σ = vo l) → (acc : Tm C Γ .st) →
    (Tm.saveLeaves s p val ls acc).eval σ =
      (acc.eval σ).bind fun a => ls.foldlM (fun a l => (vo l).bind fun w => a.write (r.append l.2) w) a
  | [], _, _, acc => by
    simp only [Tm.saveLeaves, List.foldlM_nil]
    cases acc.eval σ <;> rfl
  | l :: ls, hd, hv, acc => by
    have hl : (Tm.leafPath s p l.2).eval σ = some (r.append l.2) := by
      refine Tm.eval_leafPath_some σ s hs p l.2 (hd l List.mem_cons_self).1 hp ?_
      rw [Storage.find_appendM, hx, Option.bind_some]
      exact SVal.findM_direct x l.2 (hd l List.mem_cons_self).1 (hd l List.mem_cons_self).2
    rw [Tm.saveLeaves, Tm.eval_saveLeaves hs hp hx vo ls
      (fun l' h' => hd l' (List.mem_cons_of_mem _ h')) (fun l' h' => hv l' (List.mem_cons_of_mem _ h')),
      Tm.eval_save, hl, hv l List.mem_cons_self]
    cases acc.eval σ with
    | none => rfl
    | some a => simp only [Option.bind_some, List.foldlM_cons, Option.bind_eq_bind]

/-- A save of a value that reverts reverts. -/
theorem Tm.eval_save_val_none {U : Ty} (acc : Tm C Γ .st) (q : Tm C Γ (.path U)) (v : Tm C Γ (.sv U))
    (h : v.eval σ = none) : (Tm.app3 .save acc q v).eval σ = none := by
  rw [Tm.eval_save, h]
  cases acc.eval σ with
  | none => rfl
  | some _ =>
    cases q.eval σ with
    | none => rfl
    | some _ => rfl

end Saves

/-! ## Each expansion reads as the term it expands -/

section Exact

variable {Γ : Ctx} (σ : State C Γ)

theorem Ty.leaves_direct {T : Ty} : ∀ l ∈ T.leaves, l.2.direct = true ∧ l.2.out = false :=
  fun l h => Ty.leavesAt_direct _ T l h

/-- **`delAtExpand` is exact**: `delAt(s, p)` reads as the saves of its
leaves' defaults (`Storage.delete_expand`). -/
theorem Tm.eval_delAtLeaves {T : Ty} (hT : T.Finite) (hne : T.leaves ≠ []) (s : Tm C Γ .st)
    (p : Tm C Γ (.path T)) : (Tm.delAtLeaves s p).eval σ = (Tm.app2 .delAt s p).eval σ := by
  obtain ⟨l, ls, e⟩ := List.exists_cons_of_ne_nil hne
  rw [Tm.eval_app2, Close.Op2.eval_delAt]
  unfold Tm.delAtLeaves
  cases hs : s.eval σ with
  | none => exact Tm.eval_saveLeaves_none σ s p _ _ s hs
  | some st =>
    cases hp : p.eval σ with
    | none =>
      rw [e]
      exact Tm.eval_saveLeaves_none σ s p _ ls _
        (by rw [Tm.eval_save, hs, Tm.eval_leafPath_none σ s p l.2 hp]; rfl)
    | some r =>
      simp only [Option.bind_some]
      cases hx : st.find r with
      | none =>
        have hd : st.delete r = none := by
          simp only [Storage.delete, hx, Option.bind_eq_bind, Option.bind_none]
        rw [hd, e]
        exact Tm.eval_saveLeaves_none σ s p _ ls _ (Tm.eval_saveLeaf_none σ s p (fun l => Tm.dfltWord l.1) hs hp hx l)
      | some x =>
        rw [Tm.eval_saveLeaves σ s p _ hs hp hx (fun l => some (.prim (PrimTy.dflt l.1))) T.leaves
          Ty.leaves_direct (fun _ _ => rfl) s, hs, Option.bind_some, Storage.delete_expand hT hne]
        simp only [Option.bind_some]

/-- **`copyExpand` is exact**: `save(s, p, find(s, q))` reads as the saves of
the source's words, read in `s` (`Storage.write_find_expand`). -/
theorem Tm.eval_copyLeaves {T : Ty} (hP : T.isPrimitive = false) (hT : T.Finite)
    (hne : T.leaves ≠ []) (s : Tm C Γ .st) (p q : Tm C Γ (.path T)) :
    (Tm.copyLeaves s p q).eval σ = (Tm.app3 .save s p (.app2 .sfind s q)).eval σ := by
  obtain ⟨l, ls, e⟩ := List.exists_cons_of_ne_nil hne
  rw [Tm.eval_save, Tm.eval_app2, Close.Op2.eval_sfind]
  unfold Tm.copyLeaves
  cases hs : s.eval σ with
  | none => exact Tm.eval_saveLeaves_none σ s p _ _ s hs
  | some st =>
    cases hp : p.eval σ with
    | none =>
      rw [e]
      exact Tm.eval_saveLeaves_none σ s p _ ls _
        (by rw [Tm.eval_save, hs, Tm.eval_leafPath_none σ s p l.2 hp]; rfl)
    | some r =>
      simp only [Option.bind_some]
      cases hq : q.eval σ with
      | none =>
        rw [e]
        refine Tm.eval_saveLeaves_none σ s p _ ls _ (Tm.eval_save_val_none σ _ _ _ ?_)
        rw [Tm.eval_app1, Close.Op1.eval_sval, Tm.eval_app2, Close.Op2.eval_find,
          Tm.eval_leafPath_none σ s q l.2 hq, hs]
        rfl
      | some rq =>
        simp only [Option.bind_some]
        cases hv : st.find rq with
        | none =>
          rw [e]
          refine Tm.eval_saveLeaves_none σ s p _ ls _ (Tm.eval_save_val_none σ _ _ _ ?_)
          rw [Tm.eval_app1, Close.Op1.eval_sval, Tm.eval_app2, Close.Op2.eval_find, hs,
            Option.bind_some]
          cases hl : (Tm.leafPath s q l.2).eval σ with
          | none => rfl
          | some r' =>
            rw [Tm.eval_leafPath_sub σ s q l.2 hq hl, Option.bind_some, Storage.find_appendM, hv]
            rfl
        | some v =>
          simp only [Option.bind_some]
          cases hx : st.find r with
          | none =>
            have hw : st.write r v = none := by
              unfold Storage.write
              rw [if_neg (by simp only [SVal.isPrim, hP, Bool.false_eq_true, not_false_eq_true])]
              simp only [hx, Option.bind_eq_bind, Option.bind_none]
            rw [hw, e]
            exact Tm.eval_saveLeaves_none σ s p _ ls _ (Tm.eval_saveLeaf_none σ s p (fun l => .app1 .sval (.app2 .find s (Tm.leafPath s q l.2))) hs hp hx l)
          | some x =>
            have hval : ∀ l' ∈ T.leaves,
                (Tm.app1 .sval (.app2 .find s (Tm.leafPath s q l'.2))).eval σ =
                  st.find (rq.append l'.2) := by
              intro l' hl'
              have hd := Ty.leaves_direct l' hl'
              have hf : st.find (rq.append l'.2) = v.findM l'.2 := by
                rw [Storage.find_appendM, hv, Option.bind_some]
              have hl : (Tm.leafPath s q l'.2).eval σ = some (rq.append l'.2) := by
                refine Tm.eval_leafPath_some σ s hs q l'.2 hd.1 hq ?_
                rw [hf]; exact SVal.findM_direct v l'.2 hd.1 hd.2
              rw [Tm.eval_app1, Close.Op1.eval_sval, Tm.eval_app2, Close.Op2.eval_find, hs, hl,
                Option.bind_some, Option.bind_some]
              cases st.find (rq.append l'.2) with
              | none => rfl
              | some w => cases w; rfl
            rw [Tm.eval_saveLeaves σ s p _ hs hp hx (fun l => st.find (rq.append l.2)) _
              Ty.leaves_direct hval s, hs, Option.bind_some,
              Storage.write_find_expand hT hne st r rq hv]
            rfl

/-- The slot past the end, `p[p.length]`: the live length as an index. -/
theorem Storage.nextT_eq_len {E : Ty} (st : Storage C) (r : SRef C (.ref (.array E))) :
    st.nextT r = (st.len r).map fun i => r.append (.at i .nil) := by
  unfold Storage.nextT Storage.len
  cases st.find r with
  | none => rfl
  | some _ => simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, SRef.index,
      Path.index_dyn]

/-- **`pushExpand` is exact**: a push of a word reads as one more slot and
the word saved at it (`Storage.push_prim`). -/
theorem Tm.eval_pushWord {P : PrimTy} (s : Tm C Γ .st) (p : Tm C Γ (.path (.ref (.array (.prim P)))))
    (x : Tm C Γ (.val P)) :
    (Tm.pushWord s p x).eval σ = (Tm.app3 .push s p (.app1 .sval x)).eval σ := by
  unfold Tm.pushWord
  rw [Tm.eval_save, Tm.eval_app2, Tm.eval_app2, Close.Op2.eval_pushSlot, Close.Op2.eval_nextIn,
    Tm.eval_app3, Close.Op3.eval_push, Tm.eval_app1, Close.Op1.eval_sval]
  cases hs : s.eval σ with
  | none => rfl
  | some st =>
    cases hp : p.eval σ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, Storage.nextT_eq_len]
      cases hx : x.eval σ with
      | none =>
        simp only [Option.map_none, Storage.push_none]
        cases st.push r some with
        | none => rfl
        | some _ =>
          cases st.len r with
          | none => rfl
          | some _ => rfl
      | some v =>
        simp only [Option.map_some, SVal.strip_prim, Storage.push_prim]
        cases hl : st.len r with
        | none =>
          cases st.push r some with
          | none => rfl
          | some _ => rfl
        | some i =>
          simp only [Option.map_some, Option.bind_some, Storage.write_word]

/-- `len(s, p) - 1` on an array of `n` live elements: `n - 1`, reverting at
`0`. -/
theorem Tm.eval_lastIdx {E : Ty} (s : Tm C Γ .st) (p : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.lastIdx s p).eval σ = (s.eval σ).bind fun st => (p.eval σ).bind fun r =>
      (st.len r).bind fun i => PrimTy.ofInt? .uint (i.1 - 1) := by
  unfold Tm.lastIdx
  rw [Tm.eval_app2, Close.Op2.eval_binop, Tm.eval_app2, Close.Op2.eval_len]
  cases s.eval σ with
  | none => rfl
  | some st =>
    cases p.eval σ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      cases st.len r with
      | none => rfl
      | some i => exact (binopT_some BinOp.sub rfl i _).trans rfl

/-- An empty array's pop reverts. -/
theorem Storage.pop_empty {E : Ty} {st : Storage C} {r : SRef C (.ref (.array E))}
    {e : SVec E 0} {sh : SList E} {hn : 0 < 2 ^ 256} (hf : st.find r = some (.array e sh hn))
    (keep : Bool) : st.pop keep r = none := by
  unfold Storage.pop
  have he : e.toList = [] := List.eq_nil_of_length_eq_zero (SVec.length_toList e)
  simp only [hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array, he, List.reverse_nil]

/-- **`popExpand` is exact**: a pop of a word reads as the last word reset,
then the length shrunk (`Storage.pop_prim`). -/
theorem Tm.eval_popWord {P : PrimTy} (s : Tm C Γ .st) (p : Tm C Γ (.path (.ref (.array (.prim P))))) :
    (Tm.popWord s p).eval σ = (Tm.app2 .pop s p).eval σ := by
  unfold Tm.popWord
  rw [Tm.eval_app2, Close.Op2.eval_shrink, Tm.eval_save, Tm.eval_atIn, Tm.eval_lastIdx,
    Tm.eval_app2, Close.Op2.eval_pop]
  cases hs : s.eval σ with
  | none => rfl
  | some st =>
    cases hp : p.eval σ with
    | none => cases (none : Option (Storage C)) <;> rfl
    | some r =>
      simp only [Option.bind_some]
      cases hf : st.find r with
      | none =>
        have hl : st.len r = none := by
          simp only [Storage.len, hf, Option.bind_eq_bind, Option.bind_none]
        simp only [hl, Option.bind_none, Storage.pop, hf, Option.bind_eq_bind]
      | some a =>
        cases a with
        | array e sh hn =>
          rename_i n
          have hl : st.len r = some (lenU n hn) := by
            simp only [Storage.len, hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array]
          rcases n with _ | k
          · have h0 : PrimTy.ofInt? .uint ((lenU 0 hn).val - 1) = none := rfl
            simp only [hl, Option.bind_some, h0, Option.bind_none, Storage.pop_empty hf]
          · have hk : k < 2 ^ 256 := by omega
            have h1 : PrimTy.ofInt? .uint ((lenU (k + 1) hn).val - 1) = some (uintOfNat k) := by
              have hv : (lenU (k + 1) hn).val - 1 = ((k : Nat) : Int) := by simp only [lenU]; omega
              rw [hv, uintOfNat_eq_lenU hk]
              simp only [PrimTy.ofInt?, lenU_inRange hk, dite_true]
              rfl
            have hat : st.atT (.arr .dyn) r (uintOfNat k) = some (r.append (.at (uintOfNat k) .nil)) := by
              simp only [Storage.atT, Storage.checkIndex, hf, Option.bind_eq_bind, Option.bind_some]
              show (if (uintOfNat k).1.toNat < k + 1 then some () else none).bind
                (fun _ => some (r.index (IndexTy.arr ArrTy.dyn) (uintOfNat k))) = _
              rw [if_pos (by rw [uintOfNat_val hk]; simp only [Int.toNat_natCast]; omega),
                Option.bind_some, SRef.index, Path.index_dyn]
            have hi : (lenU (k + 1) hn).val.toNat - 1 = k := by
              simp only [lenU, Int.toNat_natCast, Nat.add_sub_cancel]
            simp only [Storage.pop_prim, hl, Option.bind_some, h1, hat, hi]
            rfl

end Exact

/-! ## Where each fires -/

section Inversion

variable {Γ : Ctx}

theorem Tm.delAtExpand?_some {t t' : Tm C Γ .st} (h : t.delAtExpand? = some t') :
    ∃ (T : Ty) (s : Tm C Γ .st) (p : Tm C Γ (.path T)), t = .app2 .delAt s p ∧
      t' = Tm.delAtLeaves s p ∧ T.expandable = true ∧ s.pushFree = true ∧ p.pushFree = true := by
  unfold Tm.delAtExpand? at h
  split at h
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨_, _, _, rfl, rfl, hc.1.1, hc.1.2, hc.2⟩
    · cases h
  · cases h

/-- Two storage terms `beqR` accepts are one. -/
theorem Tm.eq_of_beqR_st {s s' : Tm C Γ .st} (h : s.beqR s' = true) : s = s' := by
  have he := Tm.eq_of_beqM s s' ((Tm.beqR_eq_beqM s s').symm.trans h)
  exact eq_of_heq (Sigma.mk.inj he).2

theorem Tm.asSval?_some {k : Srt} {v : Tm C Γ k} {P : PrimTy} {x : Tm C Γ (.val P)}
    (h : v.asSval? = some ⟨P, x⟩) :
    (⟨k, v⟩ : (k : Srt) × Tm C Γ k) = ⟨.sv (.prim P), .app1 .sval x⟩ := by
  unfold Tm.asSval? at h
  split at h
  · cases h; rfl
  · cases h

theorem Tm.asSfind?_some {k : Srt} {v : Tm C Γ k} {T : Ty} {s : Tm C Γ .st}
    {q : Tm C Γ (.path T)} (h : v.asSfind? = some ⟨T, s, q⟩) :
    (⟨k, v⟩ : (k : Srt) × Tm C Γ k) = ⟨.sv T, .app2 .sfind s q⟩ := by
  unfold Tm.asSfind? at h
  split at h
  · cases h; rfl
  · cases h

theorem Tm.asSave?_some {k : Srt} {t : Tm C Γ k} {T : Ty} {s : Tm C Γ .st}
    {p : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)} (h : t.asSave? = some ⟨T, s, p, v⟩) :
    (⟨k, t⟩ : (k : Srt) × Tm C Γ k) = ⟨.st, .app3 .save s p v⟩ := by
  cases t with
  | app3 o x y z =>
    cases o <;> first | (cases h; rfl) | cases h
  | _ => cases h

theorem Tm.asPush?_some {k : Srt} {t : Tm C Γ k} {E : Ty} {s : Tm C Γ .st}
    {p : Tm C Γ (.path (.ref (.array E)))} {v : Tm C Γ (.sv E)}
    (h : t.asPush? = some ⟨E, s, p, v⟩) :
    (⟨k, t⟩ : (k : Srt) × Tm C Γ k) = ⟨.st, .app3 .push s p v⟩ := by
  cases t with
  | app3 o x y z =>
    cases o with
    | push => cases h; rfl
    | @save T =>
      cases T with
      | prim _ => cases h
      | ref R => cases R <;> cases h
    | @atIn R _ _ _ => cases R <;> cases h
    | _ => cases h
  | _ => cases h

theorem Tm.copyExpand?_some {t t' : Tm C Γ .st} (h : t.copyExpand? = some t') :
    ∃ (T : Ty) (s : Tm C Γ .st) (p q : Tm C Γ (.path T)),
      t = .app3 .save s p (.app2 .sfind s q) ∧ t' = Tm.copyLeaves s p q ∧
      T.isPrimitive = false ∧ T.expandable = true ∧ s.pushFree = true ∧ p.pushFree = true ∧
      q.pushFree = true := by
  unfold Tm.copyExpand? at h
  split at h
  · rename_i T s p v ht
    obtain rfl := eq_of_heq (Sigma.mk.inj (Tm.asSave?_some ht)).2
    split at h
    · rename_i T' s' q hv
      split at h
      · rename_i hT
        subst hT
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hc
          cases Tm.eq_of_beqR_st h2
          obtain rfl := eq_of_heq (Sigma.mk.inj (Tm.asSfind?_some hv)).2
          exact ⟨_, _, _, _, rfl, rfl, h0, h1, h3, h4, h5⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem Tm.pushExpand?_some {t t' : Tm C Γ .st} (h : t.pushExpand? = some t') :
    ∃ (P : PrimTy) (s : Tm C Γ .st) (p : Tm C Γ (.path (.ref (.array (.prim P)))))
      (x : Tm C Γ (.val P)), t = .app3 .push s p (.app1 .sval x) ∧ t' = Tm.pushWord s p x ∧
      s.pushFree = true ∧ p.pushFree = true ∧ x.pushFree = true := by
  unfold Tm.pushExpand? at h
  split at h
  · rename_i E s p v ht
    obtain rfl := eq_of_heq (Sigma.mk.inj (Tm.asPush?_some ht)).2
    split at h
    · rename_i P x hv
      split at h
      · rename_i hE
        subst hE
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          obtain rfl := eq_of_heq (Sigma.mk.inj (Tm.asSval?_some hv)).2
          exact ⟨_, _, _, _, rfl, rfl, hc.1.1, hc.1.2, hc.2⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem Tm.popExpand?_some {t t' : Tm C Γ .st} (h : t.popExpand? = some t') :
    ∃ (P : PrimTy) (s : Tm C Γ .st) (p : Tm C Γ (.path (.ref (.array (.prim P))))),
      t = .app2 .pop s p ∧ t' = Tm.popWord s p ∧ s.pushFree = true ∧ p.pushFree = true := by
  unfold Tm.popExpand? at h
  split at h
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨_, _, _, rfl, rfl, hc.1, hc.2⟩
    · cases h
  · cases h

end Inversion

/-! ## The rewrite is exact, and out of gas where the term is -/

section Pick

variable {Γ : Ctx} (σ : State C Γ)

/-- **Every expansion reads as the term it expands**, in every typed state. -/
theorem Tm.eval_expandK? (k : ExpandKind) {t t' : Tm C Γ .st} (h : Tm.expandK? k t = some t') :
    t'.eval σ = t.eval σ := by
  cases k
  · obtain ⟨T, s, p, rfl, rfl, hT, -, -⟩ := Tm.delAtExpand?_some h
    obtain ⟨hF, hne, -⟩ := Ty.expandable_spec hT
    exact Tm.eval_delAtLeaves σ hF hne s p
  · obtain ⟨T, s, p, q, rfl, rfl, hP, hT, -, -, -⟩ := Tm.copyExpand?_some h
    obtain ⟨hF, hne, -⟩ := Ty.expandable_spec hT
    exact Tm.eval_copyLeaves σ hP hF hne s p q
  · obtain ⟨P, s, p, x, rfl, rfl, -, -, -⟩ := Tm.pushExpand?_some h
    exact Tm.eval_pushWord σ s p x
  · obtain ⟨P, s, p, rfl, rfl, -, -⟩ := Tm.popExpand?_some h
    exact Tm.eval_popWord σ s p

/-- The expansion that fires is one kind's. -/
theorem Tm.expand?_kind {t t' : Tm C Γ .st} (h : t.expand? = some t') :
    ∃ k, Tm.expandK? k t = some t' := by
  unfold Tm.expand? at h
  cases h1 : t.delAtExpand? with
  | some u => rw [h1] at h; exact ⟨.delAt, h1.trans h⟩
  | none =>
    cases h2 : t.copyExpand? with
    | some u => rw [h1, h2] at h; exact ⟨.copy, h2.trans h⟩
    | none =>
      cases h3 : t.pushExpand? with
      | some u => rw [h1, h2, h3] at h; exact ⟨.push, h3.trans h⟩
      | none => rw [h1, h2, h3] at h; exact ⟨.pop, h⟩

/-- **`Tm.expand?` is exact.** -/
theorem Tm.eval_expand? {t t' : Tm C Γ .st} (h : t.expand? = some t') :
    t'.eval σ = t.eval σ := by
  obtain ⟨k, hk⟩ := Tm.expand?_kind h
  exact Tm.eval_expandK? σ k hk

/-! ### Out of gas -/

theorem Tm.pushFree_leafPath (s : Tm C Γ .st) (hs : s.pushFree = true) :
    {T U : Ty} → (p : Tm C Γ (.path T)) → (l : Path T U) → p.pushFree = true →
      (Tm.leafPath s p l).pushFree = true
  | _, _, _, .nil, hp => hp
  | _, _, _, .field _ l, hp => Tm.pushFree_leafPath s hs _ l (by simp only [Tm.pushFree, hp])
  | _, _, _, .atF _ l, hp => Tm.pushFree_leafPath s hs _ l
      (by simp only [Tm.pushFree, Op3.pushFree, hs, hp, Bool.and_self])
  | _, _, _, .at _ l, hp => Tm.pushFree_leafPath s hs _ l
      (by simp only [Tm.pushFree, Op3.pushFree, hs, hp, Bool.and_self])
  | _, _, _, .key _ l, hp => Tm.pushFree_leafPath s hs _ l
      (by simp only [Tm.pushFree, Op3.pushFree, hs, hp, Bool.and_self])

theorem Tm.pushFree_saveLeaves (s : Tm C Γ .st) (hs : s.pushFree = true) {T : Ty}
    (p : Tm C Γ (.path T)) (hp : p.pushFree = true) (val : (l : Leaf T) → Tm C Γ (.sv (.prim l.1)))
    (hv : ∀ l, (val l).pushFree = true) :
    (ls : List (Leaf T)) → (acc : Tm C Γ .st) → acc.pushFree = true →
      (Tm.saveLeaves s p val ls acc).pushFree = true
  | [], _, ha => ha
  | l :: ls, _, ha => Tm.pushFree_saveLeaves s hs p hp val hv ls _ (by
      simp only [Tm.pushFree, Op3.pushFree, ha, Tm.pushFree_leafPath s hs p l.2 hp, hv l,
        Bool.and_self])

/-- A push of a word is out of gas exactly where its expansion is: at a full
array, its value returning. -/
theorem Tm.exhB_pushWord {P : PrimTy} (s : Tm C Γ .st)
    (p : Tm C Γ (.path (.ref (.array (.prim P))))) (x : Tm C Γ (.val P)) (hs : s.pushFree = true)
    (hp : p.pushFree = true) (hx : x.pushFree = true) :
    (Tm.pushWord s p x).exhB σ = (Tm.app3 .push s p (.app1 .sval x)).exhB σ := by
  unfold Tm.pushWord
  simp only [Tm.exhB, Tm.exhB_of_pushFree σ s hs, Tm.exhB_of_pushFree σ p hp,
    Tm.exhB_of_pushFree σ x hx]
  have e := Tm.eval_pushWord σ s p x
  unfold Tm.pushWord at e
  rw [e]
  have h1 : ∀ a b c, Op3.exhB (H := σ.H) (Op3.save (C := C) (T := .prim P)) a b c = false :=
    fun _ _ _ => rfl
  have h2 : ∀ a b, Op2.exhB (H := σ.H) (Op2.nextIn (C := C) (E := .prim P)) a b = false :=
    fun _ _ => rfl
  simp only [h1, h2, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
  rw [Tm.eval_app3, Close.Op3.eval_push, Tm.eval_app2, Close.Op2.eval_nextIn, Tm.eval_app1,
    Close.Op1.eval_sval]
  cases hs' : s.eval σ with
  | none => rfl
  | some st =>
    cases hp' : p.eval σ with
    | none => rfl
    | some r =>
      cases hx' : x.eval σ with
      | none => simp only [Option.map_none, Option.isSome_none, Bool.and_false]; rfl
      | some v =>
        show _ = st.full r
        have h3 : Op2.exhB (H := σ.H) (Op2.pushSlot (C := C) (E := .prim P)) (some st) (some r) =
            st.full r := rfl
        rw [h3]
        simp only [Option.bind_some, Option.map_some, Option.isSome_some, Bool.and_true]
        cases hf : st.full r with
        | false => simp only [Bool.false_and, Bool.and_false]
        | true =>
          have hfind : (st.find r).isSome = true := by
            unfold Storage.full at hf
            cases h : st.find r with
            | none => rw [h] at hf; cases hf
            | some _ => rfl
          simp only [Storage.push_of_full hf, Option.isNone_none, Storage.nextT, Option.isSome_map,
            hfind, Bool.and_self]

/-- **Every expansion is out of gas exactly where the term it expands is.** -/
theorem Tm.exhB_expandK? (k : ExpandKind) {t t' : Tm C Γ .st} (h : Tm.expandK? k t = some t') :
    t'.exhB σ = t.exhB σ := by
  cases k
  · obtain ⟨T, s, p, rfl, rfl, -, hs, hp⟩ := Tm.delAtExpand?_some h
    unfold Tm.delAtLeaves
    rw [Tm.exhB_of_pushFree σ _ (Tm.pushFree_saveLeaves s hs p hp (fun l => Tm.dfltWord l.1)
        (fun _ => rfl) _ s hs),
      Tm.exhB_of_pushFree σ _ (by simp only [Tm.pushFree, Op2.pushFree, hs, hp, Bool.and_self])]
  · obtain ⟨T, s, p, q, rfl, rfl, -, -, hs, hp, hq⟩ := Tm.copyExpand?_some h
    unfold Tm.copyLeaves
    rw [Tm.exhB_of_pushFree σ _ (Tm.pushFree_saveLeaves s hs p hp
        (fun l => .app1 .sval (.app2 .find s (Tm.leafPath s q l.2))) (fun l => by
        simp only [Tm.pushFree, Op2.pushFree, hs, Tm.pushFree_leafPath s hs q l.2 hq,
          Bool.and_self]) _ s hs),
      Tm.exhB_of_pushFree σ _ (by simp only [Tm.pushFree, Op2.pushFree, Op3.pushFree, hs, hp, hq,
        Bool.and_self])]
  · obtain ⟨P, s, p, x, rfl, rfl, hs, hp, hx⟩ := Tm.pushExpand?_some h
    exact Tm.exhB_pushWord σ s p x hs hp hx
  · obtain ⟨P, s, p, rfl, rfl, hs, hp⟩ := Tm.popExpand?_some h
    rw [Tm.exhB_of_pushFree σ _ (by simp only [Tm.popWord, Tm.lastIdx, Tm.dfltWord, Tm.pushFree,
        Op2.pushFree, Op3.pushFree, hs, hp, Bool.and_self]),
      Tm.exhB_of_pushFree σ _ (by simp only [Tm.pushFree, Op2.pushFree, hs, hp, Bool.and_self])]

end Pick

/-! ## The rewrite of a line past the program -/

section Rewrite

variable {Γ : Ctx}

/-- The expansion of the kind `k` is exact at every sort. -/
theorem Tm.pickExpand_eq (k : ExpandKind) (σ : State C Γ) : PickEq (Tm.pickExpand k) σ := by
  intro s t t' h
  cases s with
  | st => exact Tm.eval_expandK? σ k h
  | _ => cases h

/-- The expansion of the kind `k` is out of gas where the term is. -/
theorem Tm.pickExpand_exh (k : ExpandKind) (σ : State C Γ) : PickExh (Tm.pickExpand k) σ := by
  intro s t t' h
  cases s with
  | st => exact Tm.exhB_expandK? σ k h
  | _ => cases h

/-- **An expansion in an update's right-hand sides, under either modality**,
is an equivalence. -/
theorem holds_upd_expand_iff (k : ExpandKind) {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ}
    {φ : Fml C Δ} (σ : State C Γ) :
    holds σ (.upd m (Upd.rwBy (Tm.pickExpand k) U) φ) ↔ holds σ (.upd m U φ) :=
  Upd.rwBy_afterT σ (Tm.pickExpand_eq k σ) (Tm.pickExpand_exh k σ) m U _

/-- The expansions of the kind `k` in `{U}_m φ`, where one fires. -/
def Fml.updExpand (k : ExpandKind) {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  if Upd.hasBy (Tm.pickExpand k) U then some (.upd m (Upd.rwBy (Tm.pickExpand k) U) φ) else none

end Rewrite

/-- **`delAtExpand`, `copyExpand`, `pushExpand`, `popExpand` past the
program**: every storage term of the kind `k` in the right-hand sides of the
update at position `i`, expanded, under either modality. -/
def FmlRw.expandPast (k : ExpandKind) (i : Nat) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.updExpand k m U φ) (fun {_ _ _ _ _ _} h σ hψ => by
    dsimp only [Fml.updExpand] at h
    split at h
    · cases h; exact (holds_upd_expand_iff k σ).1 hψ
    · cases h) i

/-- The chain link of each kind (`~[delAtExpand]~>`, …). -/
def ExpandKind.linkName : ExpandKind → Lean.Name
  | .delAt => `delAtExpand
  | .copy => `copyExpand
  | .push => `pushExpand
  | .pop => `popExpand

/-- The constructor's name, to build the rewrite as a term. -/
def ExpandKind.constName : ExpandKind → Lean.Name
  | .delAt => ``ExpandKind.delAt
  | .copy => ``ExpandKind.copy
  | .push => ``ExpandKind.push
  | .pop => ``ExpandKind.pop

/-- The kind a chain link names. -/
def ExpandKind.ofLink? (n : Lean.Name) : Option ExpandKind :=
  [ExpandKind.delAt, .copy, .push, .pop].find? (·.linkName == n)

/-! ## How much an expansion grows -/

section Size

variable {Γ : Ctx}

/-- A binary symbol whose first argument is the storage it changes. -/
def Op2.spineN {a b s : Srt} : Op2 C a b s → Nat
  | .delAt | .pushSlot | .pop | .shrink | .extend => 1
  | _ => 0

/-- A ternary symbol whose first argument is the storage it changes. -/
def Op3.spineN {a b c s : Srt} : Op3 C a b c s → Nat
  | .save | .push => 1
  | _ => 0

/-- `save` itself. -/
def Op3.saveN {a b c s : Srt} : Op3 C a b c s → Nat
  | .save => 1
  | _ => 0

/-- The `save`s on a storage term's spine: down its first arguments while
they are the storage changed. -/
def Tm.spineSaves : {s : Srt} → Tm C Γ s → Nat
  | _, .app2 o x _ => o.spineN * x.spineSaves
  | _, .app3 o x _ _ => o.saveN + o.spineN * x.spineSaves
  | _, _ => 0

theorem Tm.spineSaves_saveLeaves (s : Tm C Γ .st) {T : Ty} (p : Tm C Γ (.path T))
    (val : (l : Leaf T) → Tm C Γ (.sv (.prim l.1))) :
    (ls : List (Leaf T)) → (acc : Tm C Γ .st) →
      (Tm.saveLeaves s p val ls acc).spineSaves = acc.spineSaves + ls.length
  | [], _ => rfl
  | l :: ls, acc => by
    rw [Tm.saveLeaves, Tm.spineSaves_saveLeaves s p val ls, List.length_cons]
    show 1 + 1 * acc.spineSaves + ls.length = _
    omega

/-- **A `delete` expanded has one `save` more per word.** -/
theorem Tm.spineSaves_delAtLeaves (s : Tm C Γ .st) {T : Ty} (p : Tm C Γ (.path T)) :
    (Tm.delAtLeaves s p).spineSaves = (Tm.app2 .delAt s p).spineSaves + T.leafCount := by
  rw [Tm.delAtLeaves, Tm.spineSaves_saveLeaves]
  show _ = 1 * s.spineSaves + _
  rw [Nat.one_mul]; rfl

/-- **An expansion adds at most `expandBound` `save`s to the spine.** -/
theorem Tm.spineSaves_expand? {t t' : Tm C Γ .st} (h : t.expand? = some t') :
    t'.spineSaves ≤ t.spineSaves + expandBound := by
  obtain ⟨k, hk⟩ := Tm.expand?_kind h
  cases k
  · obtain ⟨T, s, p, rfl, rfl, hT, -, -⟩ := Tm.delAtExpand?_some hk
    rw [Tm.spineSaves_delAtLeaves]
    exact Nat.add_le_add_left (Ty.expandable_spec hT).2.2 _
  · obtain ⟨T, s, p, q, rfl, rfl, -, hT, -, -, -⟩ := Tm.copyExpand?_some hk
    rw [Tm.copyLeaves, Tm.spineSaves_saveLeaves]
    have hb := (Ty.expandable_spec hT).2.2
    show s.spineSaves + T.leafCount ≤ (1 + 1 * s.spineSaves) + expandBound
    omega
  · obtain ⟨P, s, p, x, rfl, rfl, -, -, -⟩ := Tm.pushExpand?_some hk
    show 1 + 1 * (1 * s.spineSaves) ≤ (0 + 1 * s.spineSaves) + expandBound
    simp only [expandBound]
    omega
  · obtain ⟨P, s, p, rfl, rfl, -, -⟩ := Tm.popExpand?_some hk
    show 1 * (1 + 1 * s.spineSaves) ≤ 1 * s.spineSaves + expandBound
    simp only [expandBound]
    omega

end Size

end Solidity

