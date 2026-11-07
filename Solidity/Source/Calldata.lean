import Solidity.Source.Decode

/-!
# `calldata` references in the source semantics (lane FU2-B)

Dispatch keeps a `calldata` parameter (`bytes`, `string`, or a dynamic
array of one-word values) as a reference into the frame's call data
(`Val.cdRef off len`, `Fr.cd`), after solc's entry checks (`cdTail`: the
length word within the data, a length below `2^64`, the elements within the
data; each failure reverts with no data). The elements are read and
validated only when accessed (`Loc.cd`, `readLoc`): an element that is no
value of its type reverts at the read, not at entry. `x.length` reads the
reference; `x[i]` past the length panics with `0x32`; a slice `x[s:e]`
(`sliceR`, solc's `calldata_array_index_range_access`) reverts with no data
on `e < s` or a length below `e`; a copy into memory (`cdToMem`) validates
every element.

This module proves, for that fragment:

- **progress of entry decoding**: a `calldata` argument's reference is
  built without `stuck` (`cdTail_ok`, `decodeArg_cd_ok`), and with
  `decodeArg_ok` every type dispatch decodes (`STy.entryDecodable`) is
  covered (`decodeArg_entry_ok`, `decodeArgs_entry_ok`);
- **reads**: an element read, a byte read and a slice are never `stuck`
  (`readLoc_cd_ok`, `cdByte_ok`, `sliceR_ok`);
- **copies keep the memory invariant** (`cdToMem_ok`), including the
  statically encoded element copies at the head stride (`cdStaticToMem_ok`,
  `cdToMem_static_ok`, G18.05);
- **the evaluation arms on `calldata` locals** (closed):
  `evalE_cdLength_ok` (`x.length`), `evalE_cdIndex_ok` (`x[j]`),
  `evalE_cdSlice_ok` (`x[s:e]`) keep `MemOK` and halt only without `stuck`.

A `calldata` reference agrees with every heap typing (`Val.RefOK`): the
call data is read only, and reads past its end return zeros (as
`calldataload`); no invariant ties a reference's offset and length to
`Fr.cd`, which entry decoding respects but the theorems do not need.

The owned `CalldataAggregates.lean` extension covers nested dynamic reads,
strings and represented inline static-array elements; its layout predicates
also admit string slices and statically encoded reference-element slices.
Direct static-array entry parameters, structs and unrepresented fixed shapes
remain open. Constructor calldata and slices of dynamically encoded base
elements remain refused. Memory-copy generalisation is separate G18.05 work.
-/

namespace Solidity.Source

open Solidity.Roadmap (Bytes Word)
open EM

variable {E : Env} {Γ : RCtx}

/-! ## Entry -/

/-- **The entry checks are never `stuck`**: they revert with no data or
give the reference's offset and length. -/
theorem cdTail_ok (data : Bytes) (i stride : Nat) : NotStuckR (cdTail data i stride) := by
  intro w hw
  simp only [cdTail] at hw
  repeat' split at hw
  all_goals cases hw

theorem cdArg_ok (D : Layout) (data : Bytes) (i stride : Nat) {τ : STy} (h : τ.loc? = some .calldata) :
    NotStuckR (cdArg D data i stride h) := by
  intro w hw
  simp only [cdArg] at hw
  cases hr : cdTail data i stride with
  | ok p => rw [hr] at hw; cases hw
  | error e => rw [hr] at hw; cases hw; exact cdTail_ok data i stride w hr

/-- A `calldata` parameter type dispatch keeps as a reference. -/
def STy.calldataArg : STy → Bool
  | .bytes .calldata | .string .calldata => true
  | .array .calldata σ none => σ.cdElement
  | _ => false

/-- **The types dispatch decodes without `stuck`**: the decoder's
(`STy.decodable`) and `calldata` references. -/
def STy.entryDecodable (E : Env) (τ : STy) : Bool := τ.decodable E || τ.calldataArg

/-- **A `calldata` argument at entry** keeps any invariant and is never
`stuck`; its reference agrees with every heap typing. -/
theorem decodeArg_cd_ok {P : EMState E Γ → Prop} (data : Bytes) (i : Nat) {τ : STy}
    (hτ : τ.calldataArg = true) :
    Hoare P (decodeArg data i τ : EM E Γ (Val E.layout τ))
      (fun v y => P y ∧ v.RefOK E y.2.heap.ty) (fun e y => P y ∧ NotStuck e) := by
  have hl : ∀ {τ : STy} (h : τ.loc? = some .calldata) (stride : Nat),
      Hoare P (lift (cdArg E.layout data i stride h) : EM E Γ (Val E.layout τ))
        (fun v y => P y ∧ v.RefOK E y.2.heap.ty) (fun e y => P y ∧ NotStuck e) := by
    intro τ h stride
    refine Hoare.conseq (Hoare.lift_ns (cdArg_ok E.layout data i stride h)) (fun _ h => h) ?_ (fun _ _ h => h)
    intro v y hy
    refine ⟨hy, ?_⟩
    cases v with
    | memRef h' _ => rw [h] at h'; cases h'
    | storRef h' _ => rw [h] at h'; cases h'
    | cdRef _ _ _ => trivial
    | _ => simp only [STy.loc?, reduceCtorEq] at h
  cases τ
  case bytes l =>
    cases l <;> simp only [STy.calldataArg, reduceCtorEq] at hτ
    exact hl rfl 1
  case string l =>
    cases l <;> simp only [STy.calldataArg, reduceCtorEq] at hτ
    exact hl rfl 1
  case array l σ k =>
    cases l <;> cases k <;> simp only [STy.calldataArg, reduceCtorEq] at hτ
    simp only [decodeArg, if_pos hτ]
    exact hl rfl σ.cdHeadBytes
  all_goals simp only [STy.calldataArg, reduceCtorEq] at hτ

/-- **Every type dispatch decodes**: `MemOK` is kept, the value agrees, no
halt is `stuck`. -/
theorem decodeArg_entry_ok {H : HeapTy} (data : Bytes) (i : Nat) {τ : STy} (hτ : τ.entryDecodable E = true) :
    Hoare (MemOK E H) (decodeArg data i τ : EM E Γ (Val E.layout τ))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun e y => MemOK E H y ∧ NotStuck e) := by
  simp only [STy.entryDecodable, Bool.or_eq_true] at hτ
  rcases hτ with h | h
  · exact decodeArg_ok data i h
  · exact decodeArg_cd_ok data i h

theorem decodeArgs_entry_ok {H : HeapTy} (data : Bytes) : ∀ (τs : List STy) (i : Nat),
    τs.all (STy.entryDecodable E) = true →
    Hoare (MemOK E H) (decodeArgs data τs i : EM E Γ (Vals E.layout τs))
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun e y => MemOK E H y ∧ NotStuck e)
  | [], _, _ => Hoare.pure' fun _ hy => ⟨hy, trivial⟩
  | τ :: τs, i, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [decodeArgs]
    refine Hoare.bind (decodeArg_entry_ok data i h.1) fun v => ?_
    refine Hoare.bind (Hoare.memGrowX (R := fun H' => v.RefOK E H')
      fun H' => decodeArgs_entry_ok (H := H') data τs (i + 1) h.2) fun vs => ?_
    exact Hoare.pure' fun _ ⟨hy, hvs, _, hv, hle⟩ => ⟨hy, hv.mono hle, hvs⟩

/-! ## Reads -/

/-- **An element read** at a one-word type is never `stuck`: an invalid
word reverts with no data, at the read. -/
theorem readLoc_cd_ok {P : EMState E Γ → Prop} (F : Fr) (off : Nat) {τ : STy} (hτ : τ.decodableElem E = true) :
    Hoare P (readLoc F (.cd off) : EM E Γ (Val E.layout τ))
      (fun v y => P y ∧ v.RefOK E y.2.heap.ty) (fun e y => P y ∧ NotStuck e) := by
  simp only [readLoc]
  exact Hoare.conseq (Hoare.lift_ns (decodeWord_ok _ hτ)) (fun _ h => h)
    (fun v _ hy => ⟨hy, Val.refOK_of_loc (STy.decodableElem_loc hτ) v⟩) (fun _ _ h => h)

/-- **A byte read** is never `stuck`: past the length, Panic `0x32`. -/
theorem cdByte_ok {D : Layout} (F : Fr) (off len k : Nat) : NotStuckR (cdByte (D := D) F off len k) := by
  intro w hw
  simp only [cdByte] at hw
  split at hw <;> cases hw

/-- **A slice of a `calldata` reference** is never `stuck`: out of order or
past the length, it reverts with no data. -/
theorem sliceR_ok {D : Layout} {τ : STy} (h : τ.loc? = some .calldata) (off len s e : Nat) (b : Bool) :
    NotStuckR (sliceR (D := D) (.cdRef h off len) s e b) := by
  intro w hw
  simp only [sliceR] at hw
  repeat' split at hw
  all_goals cases hw

/-! ## Copies into memory -/

/-- **A copy of `calldata` into memory keeps the memory invariant** and is
never `stuck`, at the targets the conversions reach. -/
theorem cdToMem_ok {H : HeapTy} (F : Fr) (off len : Nat) {τ : STy}
    (hτ : τ = .bytes .memory ∨ τ = .string .memory ∨ (∃ σ, τ = .array .memory σ none ∧ σ.decodableElem E = true) ∨
      τ.loc? = some .calldata) :
    Hoare (MemOK E H) (cdToMem F τ off len : EM E Γ (RVal E.layout τ))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  rcases hτ with rfl | rfl | ⟨σ, rfl, hσ⟩ | hc
  · simp only [cdToMem, STy.loc?, reduceCtorEq, dite_false]
    exact Hoare.bind (Hoare.conseq (allocRef_memX _ rfl (by trivial) (by trivial)
      (X := fun e y => MemOK E H y ∧ NotStuck e)) (fun y hy => ⟨hy, .bytes _⟩) (fun _ _ h => h) (fun _ _ h => h))
      fun _ => Hoare.pure' fun _ h => h
  · simp only [cdToMem, STy.loc?, reduceCtorEq, dite_false]
    exact Hoare.bind (Hoare.conseq (allocRef_memX _ rfl (by trivial) (by trivial)
      (X := fun e y => MemOK E H y ∧ NotStuck e)) (fun y hy => ⟨hy, .string _⟩) (fun _ _ h => h) (fun _ _ h => h))
      fun _ => Hoare.pure' fun _ h => h
  · cases σ
    case array l e k => simp only [STy.decodableElem, STy.wordElem, Bool.false_eq_true] at hσ
    all_goals
      simp only [cdToMem, STy.loc?, reduceCtorEq, dite_false]
      refine Hoare.bind (List.mapM_ok _ (fun _ => Hoare.lift_ns (decodeWord_ok _ hσ)) _) fun xs => ?_
      exact Hoare.bind (Hoare.conseq (allocRef_memX _ rfl (by trivial) (by exact fun _ => ⟨_, rfl⟩)
          (X := fun e y => MemOK E H y ∧ NotStuck e))
        (fun y hy => ⟨hy, .array fun _ => .val (Val.refOK_of_loc (STy.decodableElem_loc hσ) _)⟩)
        (fun _ _ h => h) (fun _ _ h => h)) fun _ => Hoare.pure' fun _ h => h
  · simp only [cdToMem, dif_pos hc]
    exact Hoare.pure' fun _ h => ⟨h, trivial⟩

/-- **A statically encoded element `cdStaticToMem` copies** (G18.05): a
one-word value the decoder reads, or a static memory array of such
elements with a statically encoded element. -/
def STy.cdCopyElem (E : Env) : STy → Bool
  | .array .memory e (some _) => decide (0 < e.cdStaticWords) && e.cdCopyElem E
  | σ => σ.decodableElem E

theorem finCons_vals {H : HeapTy} {σ : STy} {m : Nat} {x : Val E.layout σ}
    {f : Fin m → Data E.layout σ} (hx : x.RefOK E H)
    (hf : ∀ i, ∃ v, f i = Data.val v ∧ v.RefOK E H) :
    ∀ i, ∃ v, finCons (Data.val x) f i = Data.val v ∧ v.RefOK E H := by
  intro i
  unfold finCons
  split
  · exact ⟨x, rfl, hx⟩
  · exact hf _

/-- **The copied elements are bare values whose references are live**, for
any element copy keeping the memory invariant. -/
theorem cdElems_ok {σ : STy} {go : Nat → EM E Γ (Val E.layout σ)} (stride : Nat)
    (hgo : ∀ (H : HeapTy) (off : Nat), Hoare (MemOK E H) (go off)
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun e y => MemOK E H y ∧ NotStuck e)) :
    ∀ (H : HeapTy) (off m : Nat), Hoare (MemOK E H) (cdElems go stride off m)
      (fun f y => MemOK E H y ∧ ∀ i, ∃ v, f i = Data.val v ∧ v.RefOK E y.2.heap.ty)
      (fun e y => MemOK E H y ∧ NotStuck e)
  | _, _, 0 => Hoare.pure' fun _ h => ⟨h, fun i => i.elim0⟩
  | H, off, m + 1 => by
    unfold cdElems
    refine Hoare.bind (hgo H off) fun x y hxy => ?_
    obtain ⟨hy, hx⟩ := hxy
    exact Hoare.conseq (Hoare.bind (cdElems_ok stride hgo y.2.heap.ty (off + stride) m) fun f =>
        Hoare.pure' (a := finCons (Data.val x) f)
          (Q := fun g y' => MemOK E y.2.heap.ty y' ∧
            ∀ i, ∃ v, g i = Data.val v ∧ v.RefOK E y'.2.heap.ty)
          fun y' hf => ⟨hf.1, finCons_vals (hx.mono hf.1.le) hf.2⟩)
      (fun _ h => h) (fun _ _ h => ⟨h.1.weaken hy.le, h.2⟩) (fun _ _ h => ⟨h.1.weaken hy.le, h.2⟩)
      y (MemOK.self hy)

/-- **A static element copy keeps the memory invariant** and is never
`stuck` (G18.05). -/
theorem cdStaticToMem_ok (F : Fr) (σ : STy) (hσ : σ.cdCopyElem E = true) (H : HeapTy) (off : Nat) :
    Hoare (MemOK E H) (cdStaticToMem F σ off : EM E Γ (Val E.layout σ))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun e y => MemOK E H y ∧ NotStuck e) := by
  unfold cdStaticToMem
  split
  · rename_i e m
    simp only [STy.cdCopyElem, Bool.and_eq_true, decide_eq_true_eq] at hσ
    rw [if_pos hσ.1]
    refine Hoare.bind (cdElems_ok _ (fun H' o => cdStaticToMem_ok F e hσ.2 H' o) H off m) fun xs y hy => ?_
    exact allocRef_memX (Data.array _ _ xs) rfl (by trivial) (by exact fun j => (hy.2 j).imp fun _ h => h.1)
      (X := fun e y => MemOK E H y ∧ NotStuck e) y
      ⟨hy.1, .array fun j => by obtain ⟨v, hv, hr⟩ := hy.2 j; rw [hv]; exact .val hr⟩
  · rename_i notArray
    have hd : σ.decodableElem E = true := by
      unfold STy.cdCopyElem at hσ
      split at hσ
      · exact (notArray _ _ rfl).elim
      · exact hσ
    exact Hoare.conseq (Hoare.lift_ns (decodeWord_ok _ hd)) (fun _ h => h)
      (fun v _ h => ⟨h, Val.refOK_of_loc (STy.decodableElem_loc hd) v⟩) (fun _ _ h => h)

/-- **A copy of statically encoded elements keeps the memory invariant**
and is never `stuck`: a dynamic array of static arrays, or a static
array (G18.05). -/
theorem cdToMem_static_ok {H : HeapTy} (F : Fr) (off len : Nat) {τ : STy}
    (hτ : (∃ e m, τ = .array .memory (.array .memory e (some m)) none ∧
        (STy.array .memory e (some m)).cdCopyElem E = true) ∨
      (∃ σ m, τ = .array .memory σ (some m) ∧ σ.cdCopyElem E = true)) :
    Hoare (MemOK E H) (cdToMem F τ off len : EM E Γ (RVal E.layout τ))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  rcases hτ with ⟨e, m, rfl, hσ⟩ | ⟨σ, m, rfl, hσ⟩
  all_goals
    simp only [cdToMem, STy.loc?, reduceCtorEq, dite_false]
    refine Hoare.bind (cdElems_ok _ (fun H' o => cdStaticToMem_ok F _ hσ H' o) H off _) fun xs => ?_
    refine Hoare.bind ?_ fun _ => Hoare.pure' fun _ h => h
    intro y hy
    exact allocRef_memX (Data.array _ _ xs) rfl (by trivial) (by exact fun j => (hy.2 j).imp fun _ h => h.1)
      (X := fun e y => MemOK E H y ∧ NotStuck e) y
      ⟨hy.1, .array fun j => by obtain ⟨v, hv, hr⟩ := hy.2 j; rw [hv]; exact .val hr⟩

/-! ## The evaluation arms on `calldata` locals -/

/-- Every value of a `calldata` reference type is a reference. -/
theorem Val.cd_shape {τ : STy} (hτ : τ.loc? = some .calldata) (v : Val E.layout τ) :
    ∃ h off len, v = .cdRef h off len := by
  cases v with
  | memRef h _ => rw [hτ] at h; cases h
  | storRef h _ => rw [hτ] at h; cases h
  | cdRef h off len => exact ⟨h, off, len, rfl⟩
  | _ => simp only [STy.loc?, reduceCtorEq] at hτ

/-- **`x.length` on a `calldata` local** keeps `MemOK` and is never stuck. -/
theorem evalE_cdLength_ok (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy} {σ : STy}
    (x : Idx Γ (.array .calldata σ none)) (hl : STy.lengthTy (.array .calldata σ none) = some (.int IntTy.u256)) :
    Hoare (MemOK E H) (evalE G F (n + 1 + 1) (.length (.local x) hl))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  simp only [evalE]
  refine Hoare.bind (evalE_local_ok G F n x) fun av => ?_
  cases av with
  | val a =>
    obtain ⟨h, off, len, rfl⟩ := Val.cd_shape rfl a
    simp only [getV, RVal.get, lengthOf]
    exact Hoare.pure' fun _ hy => ⟨hy.1, trivial⟩

/-- **`x[j]` on a `calldata` local by an index local** keeps `MemOK` and is
never stuck: past the length, Panic `0x32`; an invalid element reverts at
the read. -/
theorem evalE_cdIndex_ok (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy} {σ : STy} {t : IntTy}
    (x : Idx Γ (.array .calldata σ none)) (j : Idx Γ (.int t)) (h : STy.isIndex (.int t) = true)
    (hσ : σ.decodableElem E = true) :
    Hoare (MemOK E H) (evalE G F (n + 1 + 1) (.indexArray (.local x) (.local j) h))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  simp only [evalE]
  refine Hoare.bind (evalE_local_ok G F n x) fun av => ?_
  cases av with
  | val a =>
    obtain ⟨hc, off, len, rfl⟩ := Val.cd_shape rfl a
    simp only [getV, RVal.get]
    rw [show (lift (pure (Val.cdRef hc off len)) : EM E Γ (Val E.layout (.array .calldata σ none))) =
      pure (Val.cdRef hc off len) from rfl, pure_bind]
    refine Hoare.bind (Hoare.bind (Hoare.locals' (Q := fun _ y => MemOK E H y) fun _ hx => hx.1)
      fun _ => Hoare.pure' (Q := fun _ y => MemOK E H y) fun _ hy => hy) fun iv => ?_
    cases iv with
    | val k =>
    cases k with
    | int v hv =>
      simp only [indexNat, RVal.amount]
      rw [show (lift (pure v.toNat) : EM E Γ Nat) = pure v.toNat from rfl, pure_bind]
      simp only [indexLoc, lengthOf, pure_bind, if_pos (STy.decodableElem_isValueTy hσ)]
      refine Hoare.bind (R := fun loc y => MemOK E H y ∧ ∃ o, loc = Loc.cd o) ?_ fun loc => ?_
      · exact Hoare.ite' (fun _ => Hoare.pure' fun _ hy => ⟨hy, _, rfl⟩)
          (fun _ => Hoare.lift' fun _ hy => show MemOK E H _ ∧ NotStuck _ from ⟨hy, trivial⟩)
      · intro y ⟨hy, o, ho⟩
        subst ho
        exact Hoare.bind (readLoc_cd_ok F o hσ) (fun _ => Hoare.pure' fun _ hy => hy) y hy
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

theorem STy.sliceable_loc {τ : STy} (h : τ.sliceable = true) : τ.loc? = some .calldata := by
  cases τ <;> simp only [STy.sliceable, reduceCtorEq] at h
  case bytes l => cases l <;> simp only [reduceCtorEq] at h; rfl
  case string l => cases l <;> simp only [reduceCtorEq] at h; rfl
  case array l σ k => cases l <;> cases k <;> simp only [reduceCtorEq] at h; rfl

/-- An index local's value as a number. -/
theorem index_local_ok (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy} {t : IntTy} {β : Type}
    (j : Idx Γ (.int t)) {k : Nat → EM E Γ β} {Q : β → EMState E Γ → Prop}
    (hk : ∀ i, Hoare (MemOK E H) (k i) Q (fun e y => MemOK E H y ∧ NotStuck e)) :
    Hoare (MemOK E H) (do let v ← evalE G F (n + 1) (.local j); let i ← indexNat v; k i) Q
      (fun e y => MemOK E H y ∧ NotStuck e) := by
  simp only [evalE]
  refine Hoare.bind (Hoare.bind (Hoare.locals' (Q := fun _ y => MemOK E H y) fun _ hx => hx)
    fun _ => Hoare.pure' (Q := fun _ y => MemOK E H y) fun _ hy => hy) fun iv => ?_
  cases iv with
  | val w =>
    cases w with
    | int v hv =>
      simp only [indexNat, RVal.amount]
      rw [show (lift (pure v.toNat) : EM E Γ Nat) = pure v.toNat from rfl, pure_bind]
      exact hk _
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

/-- **`x[s:e]` on a `calldata` local by index locals** keeps `MemOK` and is
never stuck: a start past the end or an end past the length reverts with no
data. -/
theorem evalE_cdSlice_ok (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy} {τ : STy} {t u : IntTy}
    (x : Idx Γ τ) (hτ : τ.sliceable = true) (s : Idx Γ (.int t)) (hs : STy.isIndex (.int t) = true)
    (e : Idx Γ (.int u)) (he : STy.isIndex (.int u) = true) (toEnd : Bool) :
    Hoare (MemOK E H) (evalE G F (n + 1 + 1) (.slice (.local x) hτ (.local s) hs (.local e) he toEnd))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  have hc := STy.sliceable_loc hτ
  rw [evalE]
  refine Hoare.bind (evalE_local_ok G F n x) fun av => ?_
  cases av with
  | val a =>
    obtain ⟨h, off, len, rfl⟩ := Val.cd_shape hc a
    simp only [getV, RVal.get]
    rw [show (lift (pure (Val.cdRef h off len)) : EM E Γ (Val E.layout τ)) = pure (Val.cdRef h off len) from rfl,
      pure_bind]
    refine Hoare.conseq (P := MemOK E H) ?_ (fun _ hy => hy.1) (fun _ _ h => h) (fun _ _ h => h)
    refine index_local_ok G F n s fun si => index_local_ok G F n e fun ei => ?_
    refine Hoare.bind (Hoare.lift_ns (sliceR_ok h off len si ei toEnd)) fun w => Hoare.pure' fun _ hy => ⟨hy, ?_⟩
    obtain ⟨_, _, _, rfl⟩ := Val.cd_shape hc w
    trivial
  | _ => simp only [STy.loc?, reduceCtorEq] at hc

/-- info: 'Solidity.Source.decodeArg_entry_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.decodeArg_entry_ok
/-- info: 'Solidity.Source.decodeArgs_entry_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.decodeArgs_entry_ok
/-- info: 'Solidity.Source.readLoc_cd_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readLoc_cd_ok
/-- info: 'Solidity.Source.cdToMem_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.cdToMem_ok
/-- info: 'Solidity.Source.cdStaticToMem_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.cdStaticToMem_ok
/-- info: 'Solidity.Source.cdToMem_static_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.cdToMem_static_ok
/-- info: 'Solidity.Source.evalE_cdLength_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalE_cdLength_ok
/-- info: 'Solidity.Source.evalE_cdIndex_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalE_cdIndex_ok
/-- info: 'Solidity.Source.evalE_cdSlice_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalE_cdSlice_ok

end Solidity.Source
