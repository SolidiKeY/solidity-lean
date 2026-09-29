import Solidity.Theory.Bridge.Delete

/-!
# Bridge: `push` and `pop` on `abs`

A push and a shrink are literal equations: `pushAt` appends the element and
consumes the first slot past the end, and `pushT` writes the element at that
slot's index (`lenAt`) and then the length — the same chain, since `abs` lays
the live slots and the shadow out as one run of indices (`slots_append`),
and a write past every slot is appended innermost, over the leaf.  The slot
a bare `push()` lands on is `fillSlot`: the default at a primitive element
type or where no slot ever was (`abs` never gives kind `none`, so kind `none`
is exactly "no slot"), the recycled slot otherwise.  A pop is up to
`StValue.Equiv`, because it deletes the last element (`abs_defaultOf`).

The Theory's operations do not check the interpreter's preconditions (an
array, a non-empty one for a pop): each lemma takes them from the `.ok`
hypothesis.

The proofs go in two steps.  First the Theory side is collapsed to one
`save` at the array's path of one rewritten node (`pushT_eq`, `shrinkT_eq`,
`popT_eq`): two writes below one path are one write of the node they make.
Then that node is compared with the `abs` of the array the interpreter
saves (`push_node`, `shrink_node`, `pop_node`), and `abs_saveStorage` closes
the gap between the two saves.
-/

namespace Solidity
namespace Theory

open Semantics StValue

/-! ## Two writes below one path are one write -/

/-- A write one member below `p` is a write at `p` of the node it makes. -/
private theorem save_snoc (s : Struct) {p : List Seg} (hp : p ≠ []) (a : Seg) (w : StValue) :
    save s (p ++ [a]) w = save s p (st (storeAt (asStruct (findSt s p)) a w)) := by
  induction p generalizing s with
  | nil => exact absurd rfl hp
  | cons b rest ih =>
      cases rest with
      | nil => rfl
      | cons c rest' =>
          rw [List.cons_append, save_cons s b (List.append_ne_nil_of_left_ne_nil
            (List.cons_ne_nil c rest') _), save_cons_cons, ih _ (List.cons_ne_nil _ _)]
          rfl

/-- The second of two writes at one member wins. -/
private theorem storeAt_storeAt (s : Struct) (a : Seg) (v w : StValue) :
    storeAt (storeAt s a v) a w = storeAt s a w := by
  induction s using Struct.inductionOn with
  | h1 s0 b v0 ih =>
      by_cases hb : b = a
      · simp only [storeAt, if_pos hb]
      · simp only [storeAt, if_neg hb, ih]
  | _ => simp only [storeAt, if_true]

/-- The second of two writes at one path wins. -/
private theorem save_save (s : Struct) {p : List Seg} (hp : p ≠ []) (v w : StValue) :
    save (save s p v) p w = save s p w := by
  induction p generalizing s with
  | nil => exact absurd rfl hp
  | cons a rest ih =>
      cases rest with
      | nil => exact storeAt_storeAt s a v w
      | cons b rest' =>
          rw [save_cons_cons, save_cons_cons, save_cons_cons, selectSt_storeAt, if_pos rfl,
            asStruct_st, ih _ (List.cons_ne_nil _ _), storeAt_storeAt]

/-- `pushT` is one write at the array's path. -/
private theorem pushT_eq (s : Struct) {p : List Seg} (hp : p ≠ []) (w : StValue) :
    pushT s p w = save s p (st (storeAt (storeAt (asStruct (findSt s p)) (.at (lenAt s p)) w)
      lengthSeg (int (lenAt s p + 1)))) := by
  rw [pushT, save_snoc s hp, save_snoc _ hp, find_save_same _ hp, asStruct_st, save_save _ hp]

/-- `shrinkT` is one write at the array's path. -/
private theorem shrinkT_eq (s : Struct) {p : List Seg} (hp : p ≠ []) :
    shrinkT s p = save s p (st (storeAt (asStruct (findSt s p)) lengthSeg (int (lenAt s p - 1)))) :=
  save_snoc s hp _ _

/-- `popT` is one write at the array's path. -/
private theorem popT_eq (s : Struct) {p : List Seg} (hp : p ≠ []) :
    popT s p = save s p (st (storeAt (storeAt (asStruct (findSt s p)) (.at (lenAt s p - 1))
      (delValue (selectSt (asStruct (findSt s p)) (.at (lenAt s p - 1)))))
      lengthSeg (int (lenAt s p - 1)))) := by
  rw [popT, delAt, find_append s p (List.cons_ne_nil _ []), save_snoc s hp, save_snoc _ hp,
    find_save_same _ hp, asStruct_st, save_save _ hp]
  rfl

/-! ## The array node -/

/-- `abs` of an array, one level unfolded. -/
private theorem abs_array (es sh : List SVal) (fx : Bool) :
    (SVal.array es sh fx).abs = st (.storeSt (SVal.abs.slots 0 es
      (SVal.abs.slots es.length sh (Struct.arrSt fx))) lengthSeg (int (es.length : Int))) := by
  rw [SVal.abs]

/-- A push's node: the element written at the old length over the first slot
past the end (or appended over the leaf where there is none), then the
length. -/
private theorem push_node (es sh : List SVal) (fx : Bool) (x : SVal) :
    st (storeAt (storeAt (asStruct (SVal.array es sh fx).abs) (.at (es.length : Int)) x.abs)
      lengthSeg (int ((es.length : Int) + 1))) = (SVal.array (es ++ [x]) sh.tail fx).abs := by
  have hfr : ∀ k, k < es.length → (Seg.at (es.length : Int)) ≠ .at ((0 + k : Nat) : Int) := by
    intro k hk h; injection h with h; omega
  rw [abs_array, abs_array, asStruct_st, storeAt, if_neg (by nofun), storeAt, if_pos rfl,
    SVal.storeAt_slots_frame 0 es _ _ _ hfr, SVal.slots_append, Nat.zero_add]
  have h1 : ((es.length + 1 : Nat) : Int) = (es.length : Int) + 1 := by omega
  rw [List.length_append, List.length_singleton, h1]
  cases sh with
  | nil => simp only [SVal.abs.slots, storeAt, List.tail]
  | cons c rest => simp only [SVal.abs.slots, storeAt, List.tail, if_true]

/-- `abs` never gives kind `none`, so `fillSlot` recycles a slot as it is. -/
private theorem fillSlot_abs (d : StValue) (c : SVal) : fillSlot false d c.abs = c.abs := by
  have hk : c.abs.seen = _ := SVal.abs_kind c
  cases hc : c.abs with
  | prim p => rfl
  | st s =>
      rw [hc] at hk
      have hs : s.kind ≠ none := by
        intro h
        cases c <;> simp only [seen, h] at hk <;> cases hk
      exact fillSlot_recycled d hs

/-- The slot a bare `push()` lands on, read at the old length, is the one
`pushSlot` takes. -/
private theorem slot_node (es sh : List SVal) (fx : Bool) (E : Ty) :
    fillSlot E.isPrimitive (defaultForTy E).abs
      (selectSt (asStruct (SVal.array es sh fx).abs) (.at (es.length : Int))) =
      (pushSlot E sh).1.abs := by
  rw [abs_array, asStruct_st, selectOnStore, if_neg (by nofun), SVal.select_slots]
  dsimp only
  rw [dif_neg (by omega)]
  cases sh with
  | nil =>
      cases E.isPrimitive <;>
        simp only [SVal.abs.slots, selectSt, pushSlot, fillSlot, Struct.kind, Bool.false_eq_true,
          if_false, if_true]
  | cons c rest =>
      simp only [SVal.abs.slots, selectOnStore, pushSlot]
      cases E.isPrimitive
      · exact fillSlot_abs _ c
      · rfl

/-- The last element's index, as `lenAt` gives it. -/
private theorem len_pred (init : List SVal) (last : SVal) :
    (((init ++ [last]).length : Nat) : Int) - 1 = (init.length : Int) := by
  rw [List.length_append, List.length_singleton]
  omega

/-- A shrink's node: the length alone lowered, so the last element becomes the
first slot past the end, in place. -/
private theorem shrink_node (init sh : List SVal) (fx : Bool) (last : SVal) :
    storeAt (asStruct (SVal.array (init ++ [last]) sh fx).abs) lengthSeg
      (int ((((init ++ [last]).length : Nat) : Int) - 1)) =
      asStruct (SVal.array init (last :: sh) fx).abs := by
  rw [len_pred, abs_array, abs_array, asStruct_st, asStruct_st, storeAt, if_pos rfl,
    SVal.slots_append, Nat.zero_add, List.length_append, List.length_singleton]
  simp only [SVal.abs.slots]

/-- A write at the first slot past the end replaces it in place. -/
private theorem write_shadow (init sh : List SVal) (fx : Bool) (c : SVal) (v : StValue) :
    storeAt (asStruct (SVal.array init (c :: sh) fx).abs) (.at (init.length : Int)) v =
      .storeSt (SVal.abs.slots 0 init (.storeSt (SVal.abs.slots (init.length + 1) sh
        (Struct.arrSt fx)) (.at (init.length : Int)) v)) lengthSeg (int (init.length : Int)) := by
  have hfr : ∀ k, k < init.length → (Seg.at (init.length : Int)) ≠ .at ((0 + k : Nat) : Int) := by
    intro k hk h; injection h with h; omega
  rw [abs_array, asStruct_st, storeAt, if_neg (by nofun), SVal.storeAt_slots_frame 0 init _ _ _ hfr]
  simp only [SVal.abs.slots, storeAt, if_true]

/-- A pop's node: the last element deleted in place, then the length lowered —
the interpreter's `defaultOf` of it up to `Equiv` (`abs_defaultOf`). -/
private theorem pop_node (init sh : List SVal) (fx : Bool) (last : SVal) :
    Struct.Equiv
      (storeAt (storeAt (asStruct (SVal.array (init ++ [last]) sh fx).abs)
        (.at ((((init ++ [last]).length : Nat) : Int) - 1))
        (delValue (selectSt (asStruct (SVal.array (init ++ [last]) sh fx).abs)
          (.at ((((init ++ [last]).length : Nat) : Int) - 1)))))
        lengthSeg (int ((((init ++ [last]).length : Nat) : Int) - 1)))
      (asStruct (SVal.array init (last.defaultOf :: sh) fx).abs) := by
  have hsel : selectSt (asStruct (SVal.array (init ++ [last]) sh fx).abs)
      (.at (init.length : Int)) = last.abs := by
    rw [abs_array, asStruct_st, selectOnStore, if_neg (by nofun), SVal.slots_append,
      Nat.zero_add, SVal.select_slots]
    dsimp only
    rw [dif_neg (by omega)]
    simp only [SVal.abs.slots, selectOnStore, if_true]
  have hcomm : ∀ (w : StValue), storeAt (storeAt (asStruct (SVal.array (init ++ [last]) sh fx).abs)
      (.at (init.length : Int)) w) lengthSeg (int (init.length : Int)) =
      storeAt (storeAt (asStruct (SVal.array (init ++ [last]) sh fx).abs) lengthSeg
        (int (init.length : Int))) (.at (init.length : Int)) w := by
    intro w
    rw [abs_array, asStruct_st]
    simp only [storeAt, if_true, if_neg (show lengthSeg ≠ Seg.at (init.length : Int) by nofun)]
  have hrhs : asStruct (SVal.array init (last.defaultOf :: sh) fx).abs =
      storeAt (asStruct (SVal.array init (last :: sh) fx).abs) (.at (init.length : Int))
        last.defaultOf.abs := by
    rw [write_shadow, abs_array, asStruct_st]
    simp only [SVal.abs.slots]
  rw [len_pred, hsel, hcomm, ← len_pred init last, shrink_node, len_pred, hrhs]
  exact Struct.Equiv.storeAt (StValue.Equiv.refl _) (SVal.abs_defaultOf last) _

/-! ## The interpreter's side -/

/-- `pushSlot` consumes the first slot past the end, if any. -/
private theorem pushSlot_snd (E : Ty) (sh : List SVal) : (pushSlot E sh).2 = sh.tail := by
  cases sh <;> rfl

/-- What a completed `pushAt` did: found an array, computed the element from
the slot `pushSlot` takes, and saved the array with it appended. -/
private theorem pushAt_ok {σ τ : State} {E : Ty} {r : Name} {segs : List Seg}
    {val : SVal → Res SVal} (h : pushAt σ E r segs val = .ok τ) :
    ∃ (es sh : List SVal) (fx : Bool) (x : SVal),
      σ.findStorage r segs = .ok (.array es sh fx) ∧ val (pushSlot E sh).1 = .ok x ∧
      σ.saveStorage r segs (.array (es ++ [x]) sh.tail fx) = .ok τ := by
  unfold pushAt at h
  cases hf : σ.findStorage r segs with
  | error e => rw [hf] at h; cases h
  | ok v =>
      rw [hf] at h
      cases v with
      | array es sh fx =>
          rcases hps : pushSlot E sh with ⟨slot, sh'⟩
          have h1 : (pushSlot E sh).1 = slot := by rw [hps]
          have h2 : sh' = sh.tail := by rw [← pushSlot_snd E sh, hps]
          dsimp only [bind, Except.bind] at h
          rw [hps] at h
          cases hv : val slot with
          | error e => rw [hv] at h; cases h
          | ok x =>
              rw [hv] at h
              exact ⟨es, sh, fx, x, rfl, h1 ▸ hv, h2 ▸ h⟩
      | _ => cases h

/-- A push's `abs`, from what the interpreter found and saved. -/
private theorem abs_push_core {σ τ : State} {r : Name} {segs : List Seg} {es sh : List SVal}
    {fx : Bool} (x : SVal) (hf : σ.findStorage r segs = .ok (.array es sh fx))
    (hs : σ.saveStorage r segs (.array (es ++ [x]) sh.tail fx) = .ok τ) :
    τ.abs = pushT σ.abs (rootPath r segs) x.abs := by
  rw [State.abs_saveStorage hs, pushT_eq _ (List.cons_ne_nil _ _), State.abs_findStorage hf,
    State.abs_lenAt_of_array hf, push_node]

/-- What a completed `pushPlaceAt` did: `pushAt` with the slot itself as the
element, answering the old length. -/
private theorem pushPlaceAt_ok {σ τ : State} {E : Ty} {r : Name} {segs : List Seg} {k : Int}
    (h : pushPlaceAt σ E r segs = .ok (τ, k)) :
    ∃ (es sh : List SVal) (fx : Bool),
      σ.findStorage r segs = .ok (.array es sh fx) ∧
      σ.saveStorage r segs (.array (es ++ [(pushSlot E sh).1]) sh.tail fx) = .ok τ ∧
      k = es.length := by
  unfold pushPlaceAt at h
  cases hf : σ.findStorage r segs with
  | error e => rw [hf] at h; cases h
  | ok v =>
      rw [hf] at h
      cases v with
      | array es sh fx =>
          rcases hps : pushSlot E sh with ⟨slot, sh'⟩
          have h1 : (pushSlot E sh).1 = slot := by rw [hps]
          have h2 : sh' = sh.tail := by rw [← pushSlot_snd E sh, hps]
          dsimp only [bind, Except.bind] at h
          rw [hps] at h
          dsimp only at h
          cases hsv : σ.saveStorage r segs (SVal.array (es ++ [slot]) sh' fx) with
          | error e => rw [hsv] at h; cases h
          | ok σ' =>
              rw [hsv] at h
              cases h
              exact ⟨es, sh, fx, rfl, h1 ▸ h2 ▸ hsv, rfl⟩
      | _ => cases h

/-- What a completed `popAt` did: found a non-empty array and saved it with
the last element moved past the end, cleared unless `keep`. -/
private theorem popAt_ok {σ τ : State} {keep : Bool} {r : Name} {segs : List Seg}
    (h : popAt σ keep r segs = .ok τ) :
    ∃ (init : List SVal) (last : SVal) (sh : List SVal) (fx : Bool),
      σ.findStorage r segs = .ok (.array (init ++ [last]) sh fx) ∧
      σ.saveStorage r segs
        (.array init ((if keep then last else last.defaultOf) :: sh) fx) = .ok τ := by
  unfold popAt at h
  cases hf : σ.findStorage r segs with
  | error e => rw [hf] at h; cases h
  | ok v =>
      rw [hf] at h
      cases v with
      | array es sh fx =>
          dsimp only [bind, Except.bind] at h
          cases hrev : es.reverse with
          | nil => rw [hrev] at h; cases h
          | cons last restRev =>
              rw [hrev] at h
              have hes : es = restRev.reverse ++ [last] := by
                rw [← List.reverse_reverse es, hrev, List.reverse_cons]
              subst hes
              exact ⟨restRev.reverse, last, sh, fx, rfl, h⟩
      | _ => cases h

/-- `findSt` at one selector is `selectSt`. -/
private theorem findSt_single (s : Struct) (a : Seg) : findSt s [a] = selectSt s a := rfl

/-- The slot a bare `push()` lands on, from what the interpreter found. -/
private theorem fillSlot_found {σ : State} {r : Name} {segs : List Seg} {es sh : List SVal}
    {fx : Bool} (E : Ty) (hf : σ.findStorage r segs = .ok (.array es sh fx)) :
    fillSlot E.isPrimitive (defaultForTy E).abs
      (findSt σ.abs (rootPath r segs ++ [.at (lenAt σ.abs (rootPath r segs))])) =
      (pushSlot E sh).1.abs := by
  rw [find_append σ.abs _ (List.cons_ne_nil _ []), State.abs_findStorage hf,
    State.abs_lenAt_of_array hf, findSt_single, slot_node]

/-! ## The bridge -/

/-- A push of a value that does not depend on the slot (`STerm.push`'s
evaluation). -/
theorem _root_.Solidity.Semantics.State.abs_pushAt_const {σ τ : State} {E : Ty} {r : Name}
    {segs : List Seg} (w : SVal) (h : pushAt σ E r segs (fun _ => .ok w) = .ok τ) :
    τ.abs = pushT σ.abs (rootPath r segs) w.abs := by
  obtain ⟨es, sh, fx, x, hf, hv, hs⟩ := pushAt_ok h
  cases hv
  exact abs_push_core w hf hs

/-- A bare `push()` (`STerm.pushSlot`'s evaluation). -/
theorem _root_.Solidity.Semantics.State.abs_pushAt_slot {σ τ : State} {E : Ty} {r : Name}
    {segs : List Seg} (h : pushAt σ E r segs pure = .ok τ) :
    τ.abs = pushSlotT E.isPrimitive (defaultForTy E).abs σ.abs (rootPath r segs) := by
  obtain ⟨es, sh, fx, x, hf, hv, hs⟩ := pushAt_ok h
  cases hv
  rw [pushSlotT, fillSlot_found E hf]
  exact abs_push_core _ hf hs

/-- `p.push()` as a place (`STerm.extend`'s evaluation), and the index it
lands at. -/
theorem _root_.Solidity.Semantics.State.abs_pushPlaceAt {σ τ : State} {E : Ty} {r : Name}
    {segs : List Seg} {k : Int} (h : pushPlaceAt σ E r segs = .ok (τ, k)) :
    τ.abs = pushSlotT E.isPrimitive (defaultForTy E).abs σ.abs (rootPath r segs) ∧
      k = lenAt σ.abs (rootPath r segs) := by
  obtain ⟨es, sh, fx, hf, hs, hk⟩ := pushPlaceAt_ok h
  refine ⟨?_, by rw [hk, State.abs_lenAt_of_array hf]⟩
  rw [pushSlotT, fillSlot_found E hf]
  exact abs_push_core _ hf hs

/-- A pop that keeps the element (`STerm.shrink`'s evaluation). -/
theorem _root_.Solidity.Semantics.State.abs_shrink {σ τ : State} {r : Name} {segs : List Seg}
    (h : popAt σ true r segs = .ok τ) : τ.abs = shrinkT σ.abs (rootPath r segs) := by
  obtain ⟨init, last, sh, fx, hf, hs⟩ := popAt_ok h
  rw [if_pos rfl] at hs
  rw [State.abs_saveStorage hs, shrinkT_eq _ (List.cons_ne_nil _ _), State.abs_findStorage hf,
    State.abs_lenAt_of_array hf, shrink_node, abs_array init, asStruct_st]

/-- A pop (`STerm.pop`'s evaluation). -/
theorem _root_.Solidity.Semantics.State.abs_pop {σ τ : State} {r : Name} {segs : List Seg}
    (h : popAt σ false r segs = .ok τ) :
    Struct.Equiv (popT σ.abs (rootPath r segs)) τ.abs := by
  obtain ⟨init, last, sh, fx, hf, hs⟩ := popAt_ok h
  rw [if_neg Bool.false_ne_true] at hs
  have hn : Struct.Equiv _ _ := pop_node init sh fx last
  rw [abs_array init, asStruct_st] at hn
  rw [State.abs_saveStorage hs, popT_eq _ (List.cons_ne_nil _ _), State.abs_findStorage hf,
    State.abs_lenAt_of_array hf, abs_array init]
  exact Struct.Equiv.save (StValue.Equiv.refl _) hn _

end Theory
end Solidity

