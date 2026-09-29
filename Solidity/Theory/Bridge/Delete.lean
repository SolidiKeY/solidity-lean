import Solidity.Theory.Bridge.Save

/-!
# Bridge: `delete` is `delAt` on `abs`

Up to `StValue.Equiv`, not literally: the Theory deletes lazily (`delSt`,
read member by member by `keepsOnDelete`), the interpreter eagerly
(`SVal.defaultOf`).  They keep the same things — a mapping whole, a fixed
array's length, an array's slots past its end — and reset the rest, so every
read agrees.

The proof of `abs_defaultOf` is one selector at a time (`equiv_delNode`): a
deleted node shows its kind, and each member is `selectOnDelNode`'s, which
the reads of `abs` (`select_abs_fields`, `select_abs_array`) compute without
unfolding the slot layout again (design R6).  It recurses on the value by
size, since `SVal` nests through lists; no `decide` runs over `defaultOf`
(design R5).
-/

namespace Solidity
namespace Theory

open Semantics StValue

/-! ## `defaultOf`'s helpers as list functions -/

/-- `defaultOf`'s element helper is `map defaultOf`: the nested helper exists
only for structural recursion, and the proofs read it as the map. -/
private theorem defaultOfElems_eq_map :
    ∀ l : List SVal, SVal.defaultOf.defaultOfElems l = l.map SVal.defaultOf
  | [] => rfl
  | v :: l => by
      simp only [SVal.defaultOf.defaultOfElems, List.map_cons, defaultOfElems_eq_map l]

/-- A member of a deleted struct is the delete of the member: how
`abs_defaultOf` reads a field of `defaultOf` without unfolding the fields'
helper. -/
private theorem lookupBy_defaultOfFields (f : Name) :
    ∀ fs : List (Name × SVal),
      lookupBy f (SVal.defaultOf.defaultOfFields fs) = (lookupBy f fs).map SVal.defaultOf
  | [] => rfl
  | (g, v) :: fs => by
      simp only [SVal.defaultOf.defaultOfFields, lookupBy]
      split
      · rfl
      · exact lookupBy_defaultOfFields f fs

/-- A field `lookupBy` finds is in the list: what lets an induction by size
over a struct's fields (`abs_defaultOf_aux` here, `CopyBridge.sval_ind`) reach
the member a read selects.  Public because `Theory/Bridge/Copy.lean` needs it
too; `lookupBy_eq_some_mem` (`Semantics/Properties.lean`) is the same fact, in
a module the bridge does not import. -/
theorem mem_of_lookupBy {f : Name} {v : SVal} :
    ∀ {fs : List (Name × SVal)}, lookupBy f fs = some v → (f, v) ∈ fs
  | [], h => by cases h
  | (g, w) :: fs, h => by
      simp only [lookupBy] at h
      split at h
      · cases h
        rename_i hfg
        rw [hfg]
        exact List.Mem.head _
      · exact List.Mem.tail _ (mem_of_lookupBy h)

/-! ## A deleted node, one selector at a time -/

/-- A deleted node against a node of the same kind whose every member is what
`selectOnDelNode` reads. -/
private theorem equiv_delNode {S T : Struct} (hk : S.kind = T.kind)
    (h : ∀ a : Seg, StValue.Equiv
      (if keepsOnDelete S.kind (lenOf S) a then selectSt S a else delValue (selectSt S a))
      (selectSt T a)) :
    StValue.Equiv (delValue (.st S)) (.st T) := by
  intro q
  cases q with
  | nil =>
      show Seen.node (delNode S).kind = Seen.node T.kind
      rw [kind_delNode, hk]
  | cons a q =>
      show ((selectSt (delNode S) a).readAt q).seen = ((selectSt T a).readAt q).seen
      rw [selectOnDelNode]
      exact h a q

/-- An array's slot `i` after the delete: an element (inside the old length)
is reset, a slot past the end is kept; `defaultOf` resets the elements into
the same slots, whether it keeps them live (fixed) or moves them past the end
(dynamic). -/
private theorem equiv_delete_slot (es sh : List SVal) (i : Int)
    (ih : ∀ w ∈ es, StValue.Equiv (delValue w.abs) w.defaultOf.abs) :
    StValue.Equiv
      (if !inRange (es.length : Int) i then
          (if h : 0 ≤ i ∧ i.toNat < (es ++ sh).length then ((es ++ sh).get ⟨i.toNat, h.2⟩).abs
           else .st .mtSt)
        else delValue
          (if h : 0 ≤ i ∧ i.toNat < (es ++ sh).length then ((es ++ sh).get ⟨i.toNat, h.2⟩).abs
           else .st .mtSt))
      (if h : 0 ≤ i ∧ i.toNat < (es.map SVal.defaultOf ++ sh).length then
          ((es.map SVal.defaultOf ++ sh).get ⟨i.toNat, h.2⟩).abs
       else .st .mtSt) := by
  have hlen : (es.map SVal.defaultOf ++ sh).length = (es ++ sh).length := by
    simp only [List.length_append, List.length_map]
  by_cases hr : 0 ≤ i ∧ i < (es.length : Int)
  · have hin : inRange (es.length : Int) i = true := by
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; exact hr
    have hn : i.toNat < es.length := by omega
    have h1 : 0 ≤ i ∧ i.toNat < (es ++ sh).length := by
      simp only [List.length_append]; omega
    have h2 : 0 ≤ i ∧ i.toNat < (es.map SVal.defaultOf ++ sh).length := by rw [hlen]; exact h1
    rw [hin, Bool.not_true, if_neg Bool.false_ne_true, dif_pos h1, dif_pos h2]
    simp only [List.get_eq_getElem, List.getElem_append_left (as := es) hn,
      List.getElem_append_left (as := es.map SVal.defaultOf) (by rw [List.length_map]; exact hn),
      List.getElem_map]
    exact ih _ (List.getElem_mem hn)
  · have hin : inRange (es.length : Int) i = false := by
      simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [hin, Bool.not_false, if_pos rfl]
    by_cases h1 : 0 ≤ i ∧ i.toNat < (es ++ sh).length
    · have h2 : 0 ≤ i ∧ i.toNat < (es.map SVal.defaultOf ++ sh).length := by rw [hlen]; exact h1
      have hn : es.length ≤ i.toNat := by omega
      rw [dif_pos h1, dif_pos h2]
      simp only [List.get_eq_getElem, List.getElem_append_right (as := es) hn,
        List.getElem_append_right (as := es.map SVal.defaultOf) (by rw [List.length_map]; exact hn),
        List.length_map]
      exact Equiv.refl _
    · have h2 : ¬ (0 ≤ i ∧ i.toNat < (es.map SVal.defaultOf ++ sh).length) := by
        rw [hlen]; exact h1
      rw [dif_neg h1, dif_neg h2]
      exact Equiv.refl _

/-! ## The bridge -/

/-- `abs_defaultOf`, by recursion on the value's size: a struct's fields and
an array's elements are the recursive calls. -/
private theorem abs_defaultOf_aux (v : SVal) :
    StValue.Equiv (delValue v.abs) v.defaultOf.abs := by
  match v with
  | .prim (.int x) => exact Equiv.refl _
  | .prim (.bool b) => exact Equiv.refl _
  | .struct fs =>
      have ih : ∀ p ∈ fs, StValue.Equiv (delValue p.2.abs) p.2.defaultOf.abs :=
        fun p _ => abs_defaultOf_aux p.2
      have hk : (SVal.abs.fields fs).kind = some .struct := by
        have h0 := SVal.abs_kind (.struct fs)
        simp only [SVal.abs, StValue.seen, Seen.node.injEq] at h0
        exact h0
      have hk' : (SVal.abs.fields (SVal.defaultOf.defaultOfFields fs)).kind = some .struct := by
        have h0 := SVal.abs_kind (.struct (SVal.defaultOf.defaultOfFields fs))
        simp only [SVal.abs, StValue.seen, Seen.node.injEq] at h0
        exact h0
      simp only [SVal.abs, SVal.defaultOf]
      refine equiv_delNode (hk.trans hk'.symm) fun a => ?_
      rw [hk, keepsOnDelete_structLike rfl, if_neg Bool.false_ne_true,
        SVal.select_abs_fields, SVal.select_abs_fields]
      cases a with
      | field f =>
          simp only [lookupBy_defaultOfFields]
          cases hf : lookupBy f fs with
          | none => exact Equiv.refl _
          | some w => exact ih (f, w) (mem_of_lookupBy hf)
      | «at» i => exact Equiv.refl _
  | .array es sh fx =>
      have ih : ∀ w ∈ es, StValue.Equiv (delValue w.abs) w.defaultOf.abs :=
        fun w _ => abs_defaultOf_aux w
      have hA : ∀ (e s : List SVal) (f : Bool), ∃ S : Struct,
          (SVal.array e s f).abs = .st S ∧ S.kind = some (.arr f) ∧
          lenOf S = e.length ∧
            ∀ a : Seg, selectSt S a = selectSt (asStruct (SVal.array e s f).abs) a := by
        intro e s f
        refine ⟨asStruct (SVal.array e s f).abs, by simp only [SVal.abs, asStruct], ?_, ?_,
          fun _ => rfl⟩
        · have h0 := SVal.abs_kind (.array e s f)
          simp only [SVal.abs, StValue.seen, Seen.node.injEq] at h0
          exact h0
        · rw [lenOf, SVal.select_abs_array]; rfl
      rw [SVal.defaultOf.eq_def]
      obtain ⟨S, hS, hkS, hlS, hsS⟩ := hA es sh fx
      cases fx with
      | false =>
          obtain ⟨T, hT, hkT, -, hsT⟩ := hA [] (SVal.defaultOf.defaultOfElems es ++ sh) false
          simp only [hS, hT]
          refine equiv_delNode (hkS.trans hkT.symm) fun a => ?_
          rw [hkS, hlS, hsS, hsT, SVal.select_abs_array, SVal.select_abs_array]
          cases a with
          | field f =>
              by_cases hf : f = "length" <;>
                simp only [keepsOnDelete, hf, Bool.false_eq_true, if_false, if_true] <;>
                exact Equiv.refl _
          | «at» i =>
              rw [List.nil_append, defaultOfElems_eq_map]
              exact equiv_delete_slot es sh i ih
      | true =>
          obtain ⟨T, hT, hkT, -, hsT⟩ := hA (SVal.defaultOf.defaultOfElems es) sh true
          simp only [hS, hT]
          refine equiv_delNode (hkS.trans hkT.symm) fun a => ?_
          rw [hkS, hlS, hsS, hsT, SVal.select_abs_array, SVal.select_abs_array]
          cases a with
          | field f =>
              by_cases hf : f = "length" <;>
                simp only [keepsOnDelete, hf, beq_self_eq_true, beq_iff_eq,
                  if_false, if_true, defaultOfElems_eq_map, List.length_map] <;>
                exact Equiv.refl _
          | «at» i =>
              rw [defaultOfElems_eq_map]
              exact equiv_delete_slot es sh i ih
  | .map es d =>
      have hk : (SVal.abs.entries es (Struct.mapSt d.abs)).kind = some .map := by
        have h0 := SVal.abs_kind (.map es d)
        simp only [SVal.abs, StValue.seen, Seen.node.injEq] at h0
        exact h0
      simp only [SVal.abs, SVal.defaultOf]
      refine equiv_delNode rfl fun a => ?_
      rw [hk]
      exact Equiv.refl _
termination_by sizeOf v
decreasing_by
  · rename_i hm
    obtain ⟨f, w⟩ := p
    have h1 : sizeOf (f, w) < sizeOf fs := List.sizeOf_lt_of_mem hm
    simp only [SVal.struct.sizeOf_spec, Prod.mk.sizeOf_spec] at h1 ⊢
    omega
  · rename_i hm
    have h1 : sizeOf w < sizeOf es := List.sizeOf_lt_of_mem hm
    simp only [SVal.array.sizeOf_spec]
    omega

/-- The lazy delete shows what `defaultOf` computes. -/
theorem _root_.Solidity.Semantics.SVal.abs_defaultOf (v : SVal) :
    StValue.Equiv (delValue v.abs) v.defaultOf.abs :=
  abs_defaultOf_aux v

/-- `delete p;` (`STerm.delAt`'s evaluation) is `delAt` at the path: the value
the delete reads is `cur.abs` (`abs_findStorage`), the save writes
`cur.defaultOf`'s `abs` where `delAt` writes `delValue cur.abs`
(`abs_saveStorage`), and the two agree up to `Equiv` (`abs_defaultOf`). -/
theorem _root_.Solidity.Semantics.State.abs_delete {σ τ : State} {r : Name} {segs : List Seg}
    {cur : SVal} (h1 : σ.findStorage r segs = .ok cur)
    (h2 : σ.saveStorage r segs cur.defaultOf = .ok τ) :
    Struct.Equiv (delAt σ.abs (rootPath r segs)) τ.abs := by
  rw [State.abs_saveStorage h2, delAt, State.abs_findStorage h1]
  exact Struct.Equiv.save (Equiv.refl _) (SVal.abs_defaultOf cur) _

end Theory
end Solidity
