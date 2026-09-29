import Solidity.Theory.Abs

/-!
# Bridge: an array copied over an array

The one arm of `SVal.overlay` that needs index arithmetic, split out of
`Theory/Bridge/Copy.lean` because it is the longest proof of the bridge.
`copyAt` reads a slot lazily by where it falls against the two lengths
(`copyRead`); `overlay` builds the result eagerly — the new elements over the
old slots (`overlayElems` over `oel ++ osh`, `stripElems` past them), then
the old live slots past the new length cleared
(`defaultOfElems (oel.drop nel.length)`), then the old slots past both
lengths (`osh.drop (nel.length - oel.length)`).

The two agree up to `StValue.Equiv`, and only given that each element does:
an element copied over a slot is `copyVal` on one side and `overlay` on the
other (`ih`), and a live slot cleared is `delValue` on one side and
`defaultOf` on the other (`hdel`).  Those are `abs_overlay` and
`abs_defaultOf` on the elements, which `Theory/Bridge/Copy.lean` supplies
from its induction and from `Theory/Bridge/Delete.lean`; taking them as
premises is what keeps this file off both (no import cycle with the copy bridge,
whose induction needs this lemma).  `ih` is stated for every old value
because a new element past the old slots lands as on fresh storage, which is
`ih` at a primitive: `copyVal (prim _) n = stripVal n` and
`(prim _).overlay n = n.strip`.
-/

namespace Solidity
namespace Theory

open Semantics StValue

/-! ## The element lists, one index at a time

Every list the interpreter builds is read by `getElem?`, so that the three
regions of the result (`overlayElems`, the cleared `defaultOfElems ∘ drop`,
the kept `osh.drop`) meet the append and drop lemmas of core, and the index
arithmetic between them is `omega`'s. -/

/-- `stripElems` keeps the length. -/
private theorem length_stripElems :
    ∀ (l : List SVal), (SVal.strip.stripElems l).length = l.length
  | [] => by rw [SVal.strip.stripElems]
  | v :: rest => by
      rw [SVal.strip.stripElems, List.length_cons, List.length_cons, length_stripElems rest]

/-- `stripElems` is `strip` slot by slot. -/
private theorem getElem?_stripElems : ∀ (l : List SVal) (k : Nat),
    (SVal.strip.stripElems l)[k]? = l[k]?.map SVal.strip
  | [], _ => by rw [SVal.strip.stripElems]; rfl
  | v :: rest, 0 => by rw [SVal.strip.stripElems]; rfl
  | v :: rest, k + 1 => by
      rw [SVal.strip.stripElems, List.getElem?_cons_succ, List.getElem?_cons_succ,
        getElem?_stripElems rest k]

/-- The overlaid elements are as many as the new ones. -/
private theorem length_overlayElems : ∀ (os nel : List SVal),
    (SVal.overlay.overlayElems os nel).length = nel.length
  | o :: os, v :: rest => by
      rw [SVal.overlay.overlayElems, List.length_cons, List.length_cons,
        length_overlayElems os rest]
  | [], rest => by rw [SVal.overlay.overlayElems, length_stripElems]
  | _ :: _, [] => by rw [SVal.overlay.overlayElems]

/-- A new element is laid over the old slot at its index, or on fresh storage
past the old slots. -/
private theorem getElem?_overlayElems : ∀ (os nel : List SVal) (k : Nat),
    (SVal.overlay.overlayElems os nel)[k]? =
      nel[k]?.map (fun n => match os[k]? with | some o => o.overlay n | none => n.strip)
  | o :: os, v :: rest, 0 => by rw [SVal.overlay.overlayElems]; rfl
  | o :: os, v :: rest, k + 1 => by
      rw [SVal.overlay.overlayElems, List.getElem?_cons_succ, List.getElem?_cons_succ,
        List.getElem?_cons_succ, getElem?_overlayElems os rest k]
  | [], rest, k => by
      rw [SVal.overlay.overlayElems, getElem?_stripElems]
      rfl
  | _ :: _, [], k => by rw [SVal.overlay.overlayElems]; rfl

/-- `defaultOfElems` keeps the length. -/
private theorem length_defaultOfElems : ∀ (l : List SVal),
    (SVal.defaultOf.defaultOfElems l).length = l.length
  | [] => by rw [SVal.defaultOf.defaultOfElems]
  | v :: rest => by
      rw [SVal.defaultOf.defaultOfElems, List.length_cons, List.length_cons,
        length_defaultOfElems rest]

/-- `defaultOfElems` is `defaultOf` slot by slot. -/
private theorem getElem?_defaultOfElems : ∀ (l : List SVal) (k : Nat),
    (SVal.defaultOf.defaultOfElems l)[k]? = l[k]?.map SVal.defaultOf
  | [], _ => by rw [SVal.defaultOf.defaultOfElems]; rfl
  | v :: rest, 0 => by rw [SVal.defaultOf.defaultOfElems]; rfl
  | v :: rest, k + 1 => by
      rw [SVal.defaultOf.defaultOfElems, List.getElem?_cons_succ, List.getElem?_cons_succ,
        getElem?_defaultOfElems rest k]

/-! ## A slot of `abs`, read by its `Nat` index -/

/-- What `abs` shows at a slot that may be absent. -/
private def absOpt : Option SVal → StValue
  | some v => v.abs
  | none => .st .mtSt

/-- `select_abs_array`'s slot read, at a non-negative index. -/
private theorem absOpt_dite (l : List SVal) (k : Nat) :
    (if h : 0 ≤ (k : Int) ∧ (k : Int).toNat < l.length then (l.get ⟨(k : Int).toNat, h.2⟩).abs
      else .st .mtSt) = absOpt l[k]? := by
  by_cases hk : k < l.length
  · rw [dif_pos ⟨Int.natCast_nonneg k, by simpa only [Int.toNat_natCast] using hk⟩,
      List.getElem?_eq_getElem hk]
    simp only [Int.toNat_natCast, List.get_eq_getElem, absOpt]
  · rw [dif_neg (fun h => hk (by simpa only [Int.toNat_natCast] using h.2)),
      List.getElem?_eq_none (by omega)]
    rfl

/-- …and at a negative one, where no slot is. -/
private theorem absOpt_dite_neg (l : List SVal) {i : Int} (hi : i < 0) :
    (if h : 0 ≤ i ∧ i.toNat < l.length then (l.get ⟨i.toNat, h.2⟩).abs
      else .st .mtSt) = .st .mtSt :=
  dif_neg (fun h => by omega)

/-- `inRange` at a `Nat` index is `<`. -/
private theorem inRange_nat (n k : Nat) : inRange (n : Int) (k : Int) = decide (k < n) := by
  simp only [inRange, Int.ofNat_zero_le, decide_true, Int.ofNat_lt, Bool.true_and]

/-- No negative index is in range. -/
private theorem inRange_neg (n : Int) {i : Int} (hi : i < 0) : inRange n i = false := by
  simp only [inRange, Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, Int.not_lt]
  omega

/-- Two values show the same if they show the same at the top and one selector
down: `readAt` goes through `asStruct` on either side. -/
private theorem equiv_of_select {v w : StValue} (h0 : v.seen = w.seen)
    (h : ∀ a, Equiv (selectSt (asStruct v) a) (selectSt (asStruct w) a)) : Equiv v w
  | [] => h0
  | a :: q => h a q

/-- A word under an array copy lands as on fresh storage. -/
private theorem prim_overlay (p : PrimVal) (n : SVal) : (SVal.prim p).overlay n = n.strip := by
  cases n <;> simp only [SVal.overlay]

/-- One slot of the copy, at a non-negative index. -/
private theorem overlay_slot (oel osh nel nsh : List SVal) (ofx nfx : Bool) (k : Nat)
    (ih : ∀ (o : SVal), ∀ n ∈ nel, StValue.Equiv (copyVal o.abs n.abs) (o.overlay n).abs)
    (hdel : ∀ o ∈ oel, StValue.Equiv (delValue o.abs) o.defaultOf.abs) :
    Equiv (copyRead (some (.arr ofx)) (some (.arr nfx)) (oel.length : Int) (nel.length : Int)
        (.at (k : Int)) (absOpt (oel ++ osh)[k]?) (absOpt (nel ++ nsh)[k]?))
      (absOpt (SVal.overlay.overlayElems (oel ++ osh) nel ++
        (SVal.defaultOf.defaultOfElems (oel.drop nel.length) ++
          osh.drop (nel.length - oel.length)))[k]?) := by
  simp only [copyRead, inRange_nat, NodeKind.isArr, if_true, Bool.true_and]
  by_cases h1 : k < nel.length
  · -- a new element, over the old slot or on a fresh one
    rw [if_pos (decide_eq_true h1)]
    have hl : k < (SVal.overlay.overlayElems (oel ++ osh) nel).length := by
      rw [length_overlayElems]; exact h1
    rw [List.getElem?_append_left h1, List.getElem?_append_left hl, getElem?_overlayElems,
      List.getElem?_eq_getElem h1]
    have hmem : nel[k] ∈ nel := List.getElem_mem h1
    cases ho : (oel ++ osh)[k]? with
    | some o => exact ih o _ hmem
    | none =>
        have h : StValue.Equiv (copyVal (SVal.prim (.int 0)).abs nel[k].abs)
            ((SVal.prim (.int 0)).overlay nel[k]).abs := ih (.prim (.int 0)) _ hmem
        rw [prim_overlay] at h
        exact h
  · have hR1 : (SVal.overlay.overlayElems (oel ++ osh) nel).length ≤ k := by
      rw [length_overlayElems]; omega
    rw [if_neg (by simpa only [decide_eq_true_eq, Nat.not_lt] using h1),
      List.getElem?_append_right hR1, length_overlayElems]
    by_cases h2 : k < oel.length
    · -- an old live slot past the new length: cleared
      rw [if_pos (decide_eq_true h2)]
      have hD : k - nel.length < (SVal.defaultOf.defaultOfElems (oel.drop nel.length)).length := by
        rw [length_defaultOfElems, List.length_drop]; omega
      rw [List.getElem?_append_left hD, getElem?_defaultOfElems, List.getElem?_drop,
        List.getElem?_append_left h2, show nel.length + (k - nel.length) = k by omega,
        List.getElem?_eq_getElem h2]
      exact hdel _ (List.getElem_mem h2)
    · -- past both lengths: kept
      rw [if_neg (by simpa only [decide_eq_true_eq, Nat.not_lt] using h2)]
      have hD : (SVal.defaultOf.defaultOfElems (oel.drop nel.length)).length ≤ k - nel.length := by
        rw [length_defaultOfElems, List.length_drop]; omega
      rw [List.getElem?_append_right hD, List.getElem?_drop, length_defaultOfElems,
        List.length_drop, List.getElem?_append_right (by omega : oel.length ≤ k),
        show nel.length - oel.length + (k - nel.length - (oel.length - nel.length)) =
          k - oel.length by omega]
      exact Equiv.refl _

/-! ## The array node

What `abs` of an array shows at the top, read off `abs_kind` and
`select_abs_array` rather than by unfolding the layout (design R6). -/

/-- An array's `abs` is a node. -/
private theorem abs_array_st (es sh : List SVal) (fx : Bool) :
    (SVal.array es sh fx).abs = .st (asStruct (SVal.array es sh fx).abs) := by
  rw [SVal.abs]; rfl

/-- An array's node has the array's kind. -/
private theorem kind_abs_array (es sh : List SVal) (fx : Bool) :
    (asStruct (SVal.array es sh fx).abs).kind = some (.arr fx) := by
  have h : (SVal.array es sh fx).abs.seen = .node (some (.arr fx)) := SVal.abs_kind _
  rw [abs_array_st] at h
  exact Seen.node.inj h

/-- An array's node reads its live length. -/
private theorem lenOf_abs_array (es sh : List SVal) (fx : Bool) :
    lenOf (asStruct (SVal.array es sh fx).abs) = es.length := by
  unfold lenOf
  rw [SVal.select_abs_array]
  simp only [if_true, asInt]

/-- One member of a copy onto a node. -/
private theorem select_copyVal_st (o : StValue) (n : Struct) (a : Seg) :
    selectSt (asStruct (copyVal o (.st n))) a =
      copyRead (asStruct o).kind n.kind (lenOf (asStruct o)) (lenOf n) a
        (selectSt (asStruct o) a) (selectSt n a) := rfl

/-! ## The lemma -/

/-- An array copied over an array: the Theory's lazy copy shows what
`SVal.overlay` computes, given that every element copied and every element
cleared does. -/
theorem _root_.Solidity.Semantics.SVal.abs_overlay_array (oel osh : List SVal) (ofx : Bool)
    (nel nsh : List SVal) (nfx : Bool)
    (ih : ∀ (o : SVal), ∀ n ∈ nel, StValue.Equiv (copyVal o.abs n.abs) (o.overlay n).abs)
    (hdel : ∀ o ∈ oel, StValue.Equiv (delValue o.abs) o.defaultOf.abs) :
    StValue.Equiv (copyVal (SVal.array oel osh ofx).abs (SVal.array nel nsh nfx).abs)
      ((SVal.array oel osh ofx).overlay (.array nel nsh nfx)).abs := by
  have hov : (SVal.array oel osh ofx).overlay (.array nel nsh nfx) =
      SVal.array (SVal.overlay.overlayElems (oel ++ osh) nel)
        (SVal.defaultOf.defaultOfElems (oel.drop nel.length) ++
          osh.drop (nel.length - oel.length)) nfx := by
    rw [SVal.overlay]
  rw [hov]
  apply equiv_of_select
  · rw [seen_copyVal, SVal.abs_kind, SVal.abs_kind]
  · intro a
    rw [abs_array_st nel nsh nfx, select_copyVal_st, kind_abs_array, kind_abs_array,
      lenOf_abs_array, lenOf_abs_array, SVal.select_abs_array, SVal.select_abs_array,
      SVal.select_abs_array, length_overlayElems]
    rcases a with f | i
    · -- the length is the new one, any other field absent
      by_cases hf : f = "length" <;> simp only [copyRead, hf, if_true, if_false] <;>
        exact Equiv.refl _
    · rcases Int.lt_or_le i 0 with hi | hi
      · simp only [copyRead, inRange_neg _ hi, absOpt_dite_neg _ hi, NodeKind.isArr,
          Bool.false_eq_true, if_false, Bool.and_false, if_true]
        exact Equiv.refl _
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        dsimp only
        rw [absOpt_dite, absOpt_dite, absOpt_dite]
        exact overlay_slot oel osh nel nsh ofx nfx k ih hdel


end Theory
end Solidity
