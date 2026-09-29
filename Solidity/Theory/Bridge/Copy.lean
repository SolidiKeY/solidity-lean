import Solidity.Theory.Bridge.CopyArray
import Solidity.Theory.Bridge.Delete

/-!
# Bridge: a copy is `copyTo` on `abs`

Up to `StValue.Equiv`.  `copyVal` lays the new value over the old one lazily
(`copyAt`, read by `copyRead`); `SVal.overlay` computes the result.  A word is
stored as it is, so the word case of `writeStorage` is the literal
`abs_saveStorage` (`copyTo_prim`).

`abs_overlay` is one induction on the new value: the struct and mapping arms
and the shape mismatches (which land as on fresh storage, `abs_strip`) are
here, and the array-over-array arm is `abs_overlay_array`
(`Theory/Bridge/CopyArray.lean`), fed the induction hypothesis and
`abs_defaultOf`.

Both inductions go one selector at a time (`equiv_of_members`): the two sides
show the same kind, and each member is equivalent again — by the induction
hypothesis on a member the interpreter recurses into, and otherwise by a
closed fact about the lazy leaf (a copy of nothing is nothing,
`equiv_copyAt_mt`; a copy onto another shape ignores the old node,
`equiv_copyAt_other`).  The induction is on the value's size (`sval_ind`),
because a struct's member is found by `lookupBy`, not by structural descent.
The helpers are private and sit in `CopyBridge`, out of the way of the other
bridge files' names.
-/

namespace Solidity
namespace Theory

open Semantics StValue

namespace CopyBridge

/-! ## The induction and the list helpers -/

/-- Induction on a storage value with the hypotheses the copy needs: every
field of a struct and every live element of an array. -/
private theorem sval_ind {P : SVal → Prop} (hprim : ∀ p : PrimVal, P (.prim p))
    (hstruct : ∀ fs : List (Name × SVal), (∀ (f : Name) (v : SVal), (f, v) ∈ fs → P v) →
      P (.struct fs))
    (harray : ∀ (es sh : List SVal) (fx : Bool), (∀ v ∈ es, P v) → P (.array es sh fx))
    (hmap : ∀ (es : List (Int × SVal)) (d : SVal), P (.map es d)) : ∀ v : SVal, P v
  | .prim p => hprim p
  | .struct fs => hstruct fs (fun f v _ => sval_ind hprim hstruct harray hmap v)
  | .array es sh fx => harray es sh fx (fun v _ => sval_ind hprim hstruct harray hmap v)
  | .map es d => hmap es d
termination_by v => sizeOf v
decreasing_by
  · rename_i hm
    have := List.sizeOf_lt_of_mem hm
    simp only [Prod.mk.sizeOf_spec, SVal.struct.sizeOf_spec] at this ⊢; omega
  · rename_i hm
    have := List.sizeOf_lt_of_mem hm
    simp only [SVal.array.sizeOf_spec]; omega

/-- `strip`'s element helper is `map strip`, as `defaultOfElems_eq_map` is
for the delete: the nested helper exists only for structural recursion. -/
private theorem stripElems_eq_map :
    ∀ l : List SVal, SVal.strip.stripElems l = l.map SVal.strip
  | [] => rfl
  | v :: l => by
      simp only [SVal.strip.stripElems, List.map_cons, stripElems_eq_map l]

/-- A member of a stripped struct is the strip of the member, so `abs_strip`
reads one field at a time. -/
private theorem lookupBy_stripFields (f : Name) :
    ∀ fs : List (Name × SVal),
      lookupBy f (SVal.strip.stripFields fs) = (lookupBy f fs).map SVal.strip
  | [] => rfl
  | (g, v) :: fs => by
      simp only [SVal.strip.stripFields, lookupBy]
      split
      · rfl
      · exact lookupBy_stripFields f fs

/-- A member of an overlaid struct is the new member laid over the old one of
the same name, or stripped where the old struct has none — the two arms
`abs_overlay` matches against `selectOnCopyAt`. -/
private theorem lookupBy_overlayFields (f : Name) (ofs : List (Name × SVal)) :
    ∀ nfs : List (Name × SVal),
      lookupBy f (SVal.overlay.overlayFields ofs nfs) =
        (lookupBy f nfs).map (fun v => match lookupBy f ofs with
          | some o => o.overlay v
          | none => v.strip)
  | [] => rfl
  | (g, v) :: nfs => by
      simp only [SVal.overlay.overlayFields, lookupBy]
      split
      · rename_i hfg
        subst hfg
        rfl
      · exact lookupBy_overlayFields f ofs nfs

/-! ## Kinds of `abs` -/

/-- `abs` of a struct is a struct node: the kind `copyRead` and
`keepsOnDelete` dispatch on, read off `SVal.abs_kind`. -/
private theorem kind_struct (fs : List (Name × SVal)) :
    (asStruct (SVal.struct fs).abs).kind = some .struct :=
  Seen.node.inj (SVal.abs_kind (.struct fs))

/-- `abs` of an array is an array node, fixed or dynamic as the value is. -/
private theorem kind_array (es sh : List SVal) (fx : Bool) :
    (asStruct (SVal.array es sh fx).abs).kind = some (.arr fx) :=
  Seen.node.inj (SVal.abs_kind (.array es sh fx))

/-- `abs` of a mapping is a mapping node. -/
private theorem kind_map (es : List (Int × SVal)) (d : SVal) :
    (asStruct (SVal.map es d).abs).kind = some .map :=
  Seen.node.inj (SVal.abs_kind (.map es d))

/-! ## `Equiv` one selector at a time -/

/-- `Equiv` unfolded once: the same `seen`, and every member equivalent. -/
private theorem equiv_of_members {v w : StValue} (h0 : v.seen = w.seen)
    (h1 : ∀ a : Seg, StValue.Equiv (selectSt (asStruct v) a) (selectSt (asStruct w) a)) :
    StValue.Equiv v w := by
  intro q
  cases q with
  | nil => exact h0
  | cons a q => exact h1 a q

/-- Nothing copied over a node is nothing: every member is again nothing
copied over the old member. -/
private theorem equiv_copyAt_mt (s : Struct) :
    StValue.Equiv (.st (.copyAt s .mtSt)) (.st .mtSt) := by
  intro q
  induction q generalizing s with
  | nil => rfl
  | cons a q ih => exact ih _

/-- A node copied onto a node of another shape does not read the old node. -/
private theorem equiv_copyAt_other {O N : Struct}
    (h : NodeKind.sameShape O.kind N.kind = false) :
    StValue.Equiv (.st (.copyAt O N)) (.st (.copyAt .mtSt N)) :=
  equiv_of_members rfl (fun a => by
    rw [asStruct_st, asStruct_st, selectOnCopyOther h]
    exact StValue.Equiv.refl _)

/-- …stated on the interpreter's values: the copy is the new value stripped. -/
private theorem equiv_copy_other {o n : SVal}
    (h : NodeKind.sameShape (asStruct o.abs).kind (asStruct n.abs).kind = false)
    (hn : n.abs = .st (asStruct n.abs)) :
    StValue.Equiv (copyVal o.abs n.abs) (stripVal n.abs) := by
  rw [stripVal, hn]
  exact equiv_copyAt_other h

end CopyBridge

open CopyBridge

/-- A value laid on fresh slots: `stripVal` shows what `SVal.strip` computes. -/
theorem _root_.Solidity.Semantics.SVal.abs_strip (n : SVal) :
    StValue.Equiv (stripVal n.abs) n.strip.abs := by
  refine sval_ind (P := fun n => StValue.Equiv (stripVal n.abs) n.strip.abs) ?_ ?_ ?_ ?_ n
  · intro p
    exact StValue.Equiv.refl _
  · intro fs ih
    refine equiv_of_members ?_ (fun a => ?_)
    · show Seen.node (asStruct (SVal.struct fs).abs).kind =
        Seen.node (asStruct (SVal.struct (SVal.strip.stripFields fs)).abs).kind
      rw [kind_struct, kind_struct]
    · show StValue.Equiv (selectSt (.copyAt .mtSt (asStruct (SVal.struct fs).abs)) a)
        (selectSt (SVal.abs.fields (SVal.strip.stripFields fs)) a)
      rw [selectOnCopyAt, kind_struct]
      simp only [copyRead, Struct.kind, NodeKind.isStructLike, if_true]
      show StValue.Equiv (copyVal (st .mtSt) (selectSt (SVal.abs.fields fs) a))
        (selectSt (SVal.abs.fields (SVal.strip.stripFields fs)) a)
      rw [SVal.select_abs_fields, SVal.select_abs_fields]
      cases a with
      | field f =>
          dsimp only
          rw [lookupBy_stripFields]
          cases hl : lookupBy f fs with
          | none => exact equiv_copyAt_mt _
          | some v => exact ih f v (mem_of_lookupBy hl)
      | «at» i => exact equiv_copyAt_mt _
  · intro es sh fx ih
    refine equiv_of_members ?_ (fun a => ?_)
    · show Seen.node (asStruct (SVal.array es sh fx).abs).kind =
        Seen.node (asStruct (SVal.array (SVal.strip.stripElems es) [] fx).abs).kind
      rw [kind_array, kind_array]
    · show StValue.Equiv (selectSt (.copyAt .mtSt (asStruct (SVal.array es sh fx).abs)) a)
        (selectSt (asStruct (SVal.array (SVal.strip.stripElems es) [] fx).abs) a)
      have hl : lenOf (asStruct (SVal.array es sh fx).abs) = (es.length : Int) := by
        unfold lenOf
        rw [SVal.select_abs_array]
        simp only [if_true]
        rfl
      rw [selectOnCopyAt, kind_array, hl, SVal.select_abs_array (SVal.strip.stripElems es),
        SVal.select_abs_array es sh fx, stripElems_eq_map]
      cases a with
      | field f =>
          simp only [copyRead, List.length_map]
          by_cases hf : f = "length"
          · rw [if_pos hf, if_pos hf]
            exact StValue.Equiv.refl _
          · rw [if_neg hf, if_neg hf]
            exact StValue.Equiv.refl _
      | «at» i =>
          simp only [copyRead, Struct.kind, NodeKind.isArr, Bool.false_and, Bool.false_eq_true,
            if_false]
          by_cases hr : inRange (es.length : Int) i = true
          · have hi : 0 ≤ i ∧ i.toNat < es.length := by
              simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
              omega
            have h1 : 0 ≤ i ∧ i.toNat < (es ++ sh).length :=
              ⟨hi.1, by rw [List.length_append]; omega⟩
            have h2 : 0 ≤ i ∧ i.toNat < (List.map SVal.strip es ++ []).length :=
              ⟨hi.1, by rw [List.append_nil, List.length_map]; exact hi.2⟩
            rw [if_pos hr, dif_pos h1, dif_pos h2]
            simp only [List.get_eq_getElem, List.append_nil, List.getElem_map,
              List.getElem_append_left hi.2]
            exact ih _ (List.getElem_mem _)
          · have h2 : ¬ (0 ≤ i ∧ i.toNat < (List.map SVal.strip es ++ []).length) := by
              rw [List.append_nil, List.length_map]
              intro h
              apply hr
              simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
              omega
            rw [if_neg hr, dif_neg h2]
            exact StValue.Equiv.refl _
  · intro es d
    refine equiv_of_members ?_ (fun a => ?_)
    · show Seen.node (asStruct (SVal.map es d).abs).kind =
        Seen.node (asStruct (SVal.map es d).abs).kind
      rfl
    · show StValue.Equiv (selectSt (.copyAt .mtSt (asStruct (SVal.map es d).abs)) a)
        (selectSt (asStruct (SVal.map es d).abs) a)
      rw [selectOnCopyAt, kind_map]
      simp only [copyRead, Struct.kind, reduceCtorEq, if_false]
      exact StValue.Equiv.refl _

/-- A value copied over another: `copyVal` shows what `SVal.overlay` computes. -/
theorem _root_.Solidity.Semantics.SVal.abs_overlay (o n : SVal) :
    StValue.Equiv (copyVal o.abs n.abs) (o.overlay n).abs := by
  revert o
  refine sval_ind (P := fun n => ∀ o : SVal,
    StValue.Equiv (copyVal o.abs n.abs) (o.overlay n).abs) ?_ ?_ ?_ ?_ n
  · intro p o
    cases o <;> exact StValue.Equiv.refl _
  · intro nfs ih o
    cases o with
    | prim q => exact SVal.abs_strip (.struct nfs)
    | struct ofs =>
        refine equiv_of_members ?_ (fun a => ?_)
        · show Seen.node (asStruct (SVal.struct nfs).abs).kind =
            Seen.node (asStruct (SVal.struct (SVal.overlay.overlayFields ofs nfs)).abs).kind
          rw [kind_struct, kind_struct]
        · show StValue.Equiv
            (selectSt (.copyAt (asStruct (SVal.struct ofs).abs)
              (asStruct (SVal.struct nfs).abs)) a)
            (selectSt (SVal.abs.fields (SVal.overlay.overlayFields ofs nfs)) a)
          rw [selectOnCopyAt, kind_struct, kind_struct]
          simp only [copyRead, NodeKind.isStructLike, if_true]
          show StValue.Equiv (copyVal (selectSt (SVal.abs.fields ofs) a)
              (selectSt (SVal.abs.fields nfs) a))
            (selectSt (SVal.abs.fields (SVal.overlay.overlayFields ofs nfs)) a)
          rw [SVal.select_abs_fields, SVal.select_abs_fields, SVal.select_abs_fields]
          cases a with
          | «at» i => exact equiv_copyAt_mt _
          | field f =>
              dsimp only
              rw [lookupBy_overlayFields]
              cases hn : lookupBy f nfs with
              | none => exact equiv_copyAt_mt _
              | some v =>
                  cases ho : lookupBy f ofs with
                  | none => exact SVal.abs_strip v
                  | some o => exact ih f v (mem_of_lookupBy hn) o
    | array oel osh ofx =>
        refine (equiv_copy_other (n := .struct nfs) ?_ rfl).trans (SVal.abs_strip _)
        rw [kind_array, kind_struct]; rfl
    | map oe od =>
        refine (equiv_copy_other (n := .struct nfs) ?_ rfl).trans (SVal.abs_strip _)
        rw [kind_map, kind_struct]; rfl
  · intro nel nsh nfx ih o
    cases o with
    | prim q => exact SVal.abs_strip (.array nel nsh nfx)
    | struct ofs =>
        refine (equiv_copy_other (n := .array nel nsh nfx) ?_ rfl).trans (SVal.abs_strip _)
        rw [kind_struct, kind_array]; rfl
    | array oel osh ofx =>
        exact SVal.abs_overlay_array oel osh ofx nel nsh nfx (fun o v hv => ih v hv o)
          (fun o _ => SVal.abs_defaultOf o)
    | map oe od =>
        refine (equiv_copy_other (n := .array nel nsh nfx) ?_ rfl).trans (SVal.abs_strip _)
        rw [kind_map, kind_array]; rfl
  · intro ne nd o
    cases o with
    | prim q => exact SVal.abs_strip (.map ne nd)
    | struct ofs =>
        refine (equiv_copy_other (n := .map ne nd) ?_ rfl).trans (SVal.abs_strip _)
        rw [kind_struct, kind_map]; rfl
    | array oel osh ofx =>
        refine (equiv_copy_other (n := .map ne nd) ?_ rfl).trans (SVal.abs_strip _)
        rw [kind_array, kind_map]; rfl
    | map oe od =>
        refine equiv_of_members ?_ (fun a => ?_)
        · show Seen.node (asStruct (SVal.map ne nd).abs).kind =
            Seen.node (asStruct (SVal.map oe od).abs).kind
          rw [kind_map, kind_map]
        · show StValue.Equiv
            (selectSt (.copyAt (asStruct (SVal.map oe od).abs) (asStruct (SVal.map ne nd).abs)) a)
            (selectSt (asStruct (SVal.map oe od).abs) a)
          rw [selectOnCopyAt, kind_map, kind_map]
          simp only [copyRead, if_true]
          exact StValue.Equiv.refl _

/-- An assignment's storage write (`STerm.save`'s evaluation) is `copyTo`. -/
theorem _root_.Solidity.Semantics.State.abs_writeStorage {σ τ : State} {r : Name}
    {segs : List Seg} {w : SVal} (h : σ.writeStorage r segs w = .ok τ) :
    Struct.Equiv (copyTo σ.abs (rootPath r segs) w.abs) τ.abs := by
  cases w
  case prim p =>
    rw [State.abs_saveStorage (σ := σ) (w := .prim p) h]
    exact StValue.Equiv.refl _
  all_goals
    cases hf : σ.findStorage r segs with
    | error e => simp only [State.writeStorage, hf] at h; cases h
    | ok cur =>
        simp only [State.writeStorage, hf] at h
        rw [State.abs_saveStorage h]
        unfold copyTo
        rw [State.abs_findStorage hf]
        exact Struct.Equiv.save (StValue.Equiv.refl _) (SVal.abs_overlay cur _) _

end Theory
end Solidity
