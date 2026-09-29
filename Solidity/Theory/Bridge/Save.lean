import Solidity.Theory.Bridge.Find

/-!
# Bridge: the interpreter's save is the collapsing `save` on `abs`

A literal equation.  `SVal.save` replaces a member in place with `setBy`, or
appends it at the end where the key is absent; `storeAt` replaces a binding
in place, or appends it innermost over the kinded leaf — the same position
(`storeAt_abs_fields`, `storeAt_abs_entries`).  An array rewrites its slots
and re-splits them into live and past-the-end at the same length, which
`slots_append` puts back in one chain (`storeAt_slots`).
-/

namespace Solidity
namespace Theory

open Semantics StValue

/-- `save` at a non-empty path, without splitting the tail: what it stores at
the first segment is the written value itself at the last one, and the saved
member cast back to a node otherwise.  Stated this way so the induction below
takes one step per segment, whatever the tail. -/
private theorem save_cons_stored (s : Struct) (a : Seg) (rest : List Seg) (x : StValue) :
    save s (a :: rest) x =
      storeAt s a (if rest = [] then x else .st (save (asStruct (selectSt s a)) rest x)) := by
  cases rest with
  | nil => rw [if_pos rfl]; rfl
  | cons b q => rw [if_neg (List.cons_ne_nil b q)]; rfl

/-- An array's slots split at `n`, live and past the end, are its slots in
one chain: the re-split `SVal.save` makes after writing a slot. -/
private theorem slots_take_drop (l : List SVal) {n : Nat} (hn : n ≤ l.length) (b : Struct) :
    SVal.abs.slots 0 (l.take n) (SVal.abs.slots n (l.drop n) b) = SVal.abs.slots 0 l b := by
  have e : SVal.abs.slots 0 (l.take n ++ l.drop n) b =
      SVal.abs.slots 0 (l.take n) (SVal.abs.slots (0 + (l.take n).length) (l.drop n) b) :=
    SVal.slots_append 0 (l.take n) (l.drop n) b
  rw [List.take_append_drop, Nat.zero_add, List.length_take, Nat.min_eq_left hn] at e
  exact e.symm

/-- A write at a slot in range, read as the array `SVal.save` rebuilds: the
length member is untouched, and the slot is replaced in place. -/
private theorem abs_array_set (es sh : List SVal) (fx : Bool) {i : Int}
    (hi : 0 ≤ i ∧ i.toNat < (es ++ sh).length) (u : SVal) :
    StValue.st (storeAt (asStruct (SVal.array es sh fx).abs) (.at i) u.abs) =
      (SVal.array (((es ++ sh).set i.toNat u).take es.length)
        (((es ++ sh).set i.toNat u).drop es.length) fx).abs := by
  have hT : (((es ++ sh).set i.toNat u).take es.length).length = es.length := by
    rw [List.length_take, List.length_set, List.length_append]; omega
  have hn : es.length ≤ ((es ++ sh).set i.toNat u).length := by
    rw [List.length_set, List.length_append]; omega
  have hk : (((0 + i.toNat : Nat) : Int)) = i := by omega
  have e1 : SVal.abs.slots 0 (es ++ sh) (Struct.arrSt fx) =
      SVal.abs.slots 0 es (SVal.abs.slots (0 + es.length) sh (Struct.arrSt fx)) :=
    SVal.slots_append 0 es sh (Struct.arrSt fx)
  rw [Nat.zero_add] at e1
  show StValue.st (storeAt (.storeSt (SVal.abs.slots 0 es (SVal.abs.slots es.length sh
      (Struct.arrSt fx))) lengthSeg (.prim (.int (es.length : Int)))) (.at i) u.abs) =
    StValue.st (.storeSt (SVal.abs.slots 0 (((es ++ sh).set i.toNat u).take es.length)
      (SVal.abs.slots (((es ++ sh).set i.toNat u).take es.length).length
        (((es ++ sh).set i.toNat u).drop es.length) (Struct.arrSt fx))) lengthSeg
      (.prim (.int ((((es ++ sh).set i.toNat u).take es.length).length : Int))))
  rw [hT, slots_take_drop _ hn, ← e1, storeAt,
    if_neg (by simp only [reduceCtorEq, not_false_eq_true]), ← hk,
    SVal.storeAt_slots 0 (es ++ sh) _ hi.2 u, hk]

/-- The value a completed save stores in place of `v`: the written value at
`[]`, and the Theory's `save` of `v.abs` as a node otherwise.  The induction
carries the `if` rather than `abs_save`'s cast: a save at a non-empty path
never gives a primitive, so casting it to a node and back loses nothing, and
this is the form `save_cons_stored` stores one level up. -/
private theorem abs_save_stored {v v' w : SVal} {q : List Seg} (h : v.save q w = .ok v') :
    (if q = [] then w.abs else StValue.st (save (asStruct v.abs) q w.abs)) = v'.abs := by
  induction q generalizing v v' with
  | nil =>
      simp only [SVal.save, Except.ok.injEq] at h
      subst h
      rw [if_pos rfl]
  | cons a rest ih =>
      rw [if_neg (List.cons_ne_nil a rest), save_cons_stored]
      cases v with
      | prim p => cases a <;> simp only [SVal.save, reduceCtorEq] at h
      | struct fs =>
          cases a with
          | «at» i => simp only [SVal.save, reduceCtorEq] at h
          | field n =>
              simp only [SVal.save] at h
              split at h
              · next u hu =>
                  cases hs : u.save rest w with
                  | error e => simp only [hs, bind, Except.bind, reduceCtorEq] at h
                  | ok upd =>
                      simp only [hs, bind, Except.bind, Except.ok.injEq] at h
                      subst h
                      show StValue.st (storeAt (SVal.abs.fields fs) (.field n)
                          (if rest = [] then w.abs else
                            .st (save (asStruct (selectSt (SVal.abs.fields fs) (.field n)))
                              rest w.abs))) = .st (SVal.abs.fields (setBy n upd fs))
                      rw [SVal.select_abs_fields]
                      simp only [hu]
                      rw [ih hs, SVal.storeAt_abs_fields]
              · simp only [reduceCtorEq] at h
      | array es sh fx =>
          cases a with
          | field n => simp only [SVal.save, reduceCtorEq] at h
          | «at» i =>
              simp only [SVal.save] at h
              split at h
              · next hi =>
                  cases hs : ((es ++ sh).get ⟨i.toNat, hi.2⟩).save rest w with
                  | error e => simp only [hs, bind, Except.bind, reduceCtorEq] at h
                  | ok upd =>
                      simp only [hs, bind, Except.bind, Except.ok.injEq] at h
                      subst h
                      rw [SVal.select_abs_array]
                      simp only [dif_pos hi]
                      rw [ih hs]
                      exact abs_array_set es sh fx hi upd
              · simp only [reduceCtorEq] at h
      | map es d =>
          cases a with
          | field n => simp only [SVal.save, reduceCtorEq] at h
          | «at» i =>
              simp only [SVal.save] at h
              rw [SVal.select_abs_map]
              split at h
              · next u hu =>
                  cases hs : u.save rest w with
                  | error e => simp only [hs, bind, Except.bind, reduceCtorEq] at h
                  | ok upd =>
                      simp only [hs, bind, Except.bind, Except.ok.injEq] at h
                      subst h
                      simp only [hu]
                      rw [ih hs]
                      show StValue.st (storeAt (SVal.abs.entries es (Struct.mapSt d.abs)) (.at i)
                        upd.abs) = .st (SVal.abs.entries (setBy i upd es) (Struct.mapSt d.abs))
                      rw [SVal.storeAt_abs_entries]
              · next hu =>
                  cases hs : d.save rest w with
                  | error e => simp only [hs, bind, Except.bind, reduceCtorEq] at h
                  | ok upd =>
                      simp only [hs, bind, Except.bind, Except.ok.injEq] at h
                      subst h
                      simp only [hu]
                      rw [ih hs]
                      show StValue.st (storeAt (SVal.abs.entries es (Struct.mapSt d.abs)) (.at i)
                        upd.abs) = .st (SVal.abs.entries (setBy i upd es) (Struct.mapSt d.abs))
                      rw [SVal.storeAt_abs_entries]

/-- A save the interpreter completes is the Theory's `save` of the value's
`abs`, read as a node. -/
theorem _root_.Solidity.Semantics.SVal.abs_save {v v' w : SVal} {q : List Seg} (hq : q ≠ [])
    (h : v.save q w = .ok v') : save (asStruct v.abs) q w.abs = asStruct v'.abs := by
  have e : (if q = [] then w.abs else StValue.st (save (asStruct v.abs) q w.abs)) = v'.abs :=
    abs_save_stored h
  rw [if_neg hq] at e
  exact congrArg asStruct e

/-- …at a state variable, from the storage node. -/
theorem _root_.Solidity.Semantics.State.abs_saveStorage {σ τ : State} {r : Name} {segs : List Seg}
    {w : SVal} (h : σ.saveStorage r segs w = .ok τ) :
    τ.abs = save σ.abs (rootPath r segs) w.abs := by
  unfold State.saveStorage at h
  split at h
  · next v hv =>
      cases hs : v.save segs w with
      | error e => simp only [hs, bind, Except.bind, reduceCtorEq] at h
      | ok upd =>
          simp only [hs, bind, Except.bind, Except.ok.injEq] at h
          subst h
          show SVal.abs.fields (setBy r upd σ.storage) =
            save (SVal.abs.fields σ.storage) (.field r :: segs) w.abs
          rw [save_cons_stored, SVal.select_abs_fields]
          simp only [hv]
          rw [abs_save_stored hs, SVal.storeAt_abs_fields]
  · simp only [reduceCtorEq] at h

end Theory
end Solidity
