import Solidity.Backend.MemoryOps.SourceCalldataCopy

/-! Raw intN (and uintN) calldata-to-memory copies through the published
Source operations (G35-INT-RAW-1105). Values are computed from raw words, not
supplied as a success or representation premise: each word is range-checked
at the declared integer type before allocation, a dirty word reverts with no
data and rolls back the state, and admitted entries are tied to the frame's
argument bytes (`guarded_frame_run`). Template: `RawUint` (read-only). -/
namespace Solidity.Backend.CalldataPackets.RawInt
open Solidity.Backend.MemoryOps

abbrev ArrayTy (t : Source.IntTy) : Source.STy := .array .memory (.int t) none

/-- Validation is computed from each raw word, before allocation. -/
def values (D : Source.Layout) (t : Source.IntTy) (F : Source.Fr) (off len : Nat) :
    Source.R (List (Source.Val D (.int t))) :=
  (List.range len).mapM fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) (.int t)

def memory {D : Source.Layout} {t : Source.IntTy} (xs : List (Source.Val D (.int t))) :
    Source.Data D (ArrayTy t) :=
  .array xs.length (fun _ h => nomatch h) (fun k => .val (xs.get k))

/-- Exact range check on the declared integer interpretation: dirty high bits revert. -/
theorem decode_range (D : Source.Layout) (t : Source.IntTy) (w : Nat) :
    Source.decodeWord D w (.int t) =
      if h : t.lo ≤ Source.wordInt t (Source.toWord w) ∧
          Source.wordInt t (Source.toWord w) ≤ t.hi then
        .ok (.int _ h) else .error (.revert []) := by
  by_cases h : t.lo ≤ Source.wordInt t (Source.toWord w) ∧ Source.wordInt t (Source.toWord w) ≤ t.hi
  · simp only [Source.decodeWord,Source.decodeElemWord,Source.readInt,if_pos h,Source.mkInt,dif_pos h]
    rfl
  · simp only [Source.decodeWord,Source.decodeElemWord,Source.readInt,if_neg h,dif_neg h]

/-- Arbitrary lengths: either all raw words decode and one object is allocated,
or validation fails and the entire initial state is preserved. -/
theorem copy_run {E : Source.Env} {Γ : Source.RCtx}
    (t : Source.IntTy) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy t) off len).run y =
      match values E.layout t F off len with
      | .error e => (.error e,y)
      | .ok xs => (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy t,memory xs⟩).1})) := by
  simp only [Source.cdToMem,ArrayTy,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,source_mapM_lift_run]
  unfold values
  cases (List.range len).mapM (fun j => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) (.int t)) <;> rfl

/-- The decoder's signed branch unfolded: the 256-bit two's-complement reading
followed by the declared range test (the width-specific sign-extension test
itself is `accepted`/`accepted_sign_bits` below). -/
theorem signed_decode_range (D : Source.Layout) (t : Source.IntTy) (signed : t.signed=true) (w : Nat) :
    Source.decodeWord D w (.int t) =
      let v : Int := if 2^255 ≤ (Source.toWord w).val then
        ((Source.toWord w).val : Int)-2^256 else (Source.toWord w).val
      if h : t.lo ≤ v ∧ v ≤ t.hi then .ok (.int v h) else .error (.revert []) := by
  simpa only [Source.wordInt,signed,true_and] using decode_range D t w

/-- The existing resolved implicit conversion; no target execution assumed. -/
def copyExpr {E : Source.Env} {Γ : Source.RCtx} (t : Source.IntTy)
    (i : Source.Idx Γ (.array .calldata (.int t) none)) : Source.RExpr E Γ (ArrayTy t) :=
  .conv (.local i) (by
    apply Or.inl
    change (Source.STy.same (.int t) (.int t) && true && true && _)=true
    rw [Source.STy.same_refl]
    rfl)

theorem eval_copy {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (t : Source.IntTy) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata (.int t) none)) (off len : Nat)
    (localRef : y.1.get i=.cdRef rfl off len) :
    (Source.evalE G F (n+2) (copyExpr t i)).run y=
      (Source.cdToMem F (ArrayTy t) off len).run y := by
  rw [copyExpr,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y i _ localRef]
  change (Source.convRV F (n+1) (ArrayTy t)
    (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata (.int t) none))).run y=_
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata (.int t) none)≠ArrayTy t from by intro h;cases h)]
  rfl

/-- Entry rejection occurs before copying; admitted entries retain the exact
raw-word validation result, including dirty-input refusal. -/
theorem guarded_run {E : Source.Env} {Γ : Source.RCtx}
    (data : List UInt8) (i : Nat) (t : Source.IntTy) (F : Source.Fr) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy t) p.1 p.2).run y=
      match Source.cdTail data i 32 with
      | .error e => (.error e,y)
      | .ok (off,len) => (Source.cdToMem F (ArrayTy t) off len).run y := by
  rw [Source.Hoare.run_bind]
  cases h : Source.cdTail data i 32 with
  | error e => simp only [Source.EM.lift];rfl
  | ok p => simp only [Source.EM.lift];rfl

/-- The complete state observation is derived from raw validation, including
rollback after a late dirty element and preservation of every address other than the allocation address. -/
theorem copy_observations {E : Source.Env} {Γ : Source.RCtx}
    (t : Source.IntTy) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    let z := (Source.cdToMem F (ArrayTy t) off len).run y |>.2
    match values E.layout t F off len with
    | .error _ => z=y
    | .ok xs =>
      z.2.heap.get y.2.heap.next=some ⟨ArrayTy t,memory xs⟩ ∧
      z.2.heap.next=y.2.heap.next+1 ∧
      (∀ a,a≠y.2.heap.next → z.2.heap.get a=y.2.heap.get a) ∧
      z.1=y.1 ∧ {z.2 with heap := y.2.heap}=y.2 := by
  rw [copy_run]
  cases values E.layout t F off len with
  | error e => rfl
  | ok xs =>
    dsimp only
    refine ⟨Source.Heap.alloc_get _ _,rfl,?_,rfl,?_⟩
    · intro a different
      exact Source.Heap.alloc_other _ _ different
    · cases y.2
      rfl
/-! ## Width-specific accepted words

`accepted` is stated independently of `wordInt`/`IntTy.lo`/`IntTy.hi`: for a
signed width `b` the word is below `2^(b-1)` or at least `2^256-2^(b-1)`
(equivalently, its top `257-b` bits are all equal: `accepted_sign_bits`);
for an unsigned width it is below `2^b`. -/

def accepted (t : Source.IntTy) (w : Nat) : Prop :=
  if t.signed then w < 2^(t.bits-1) ∨ 2^256-2^(t.bits-1) ≤ w else w < 2^t.bits

instance (t : Source.IntTy) (w : Nat) : Decidable (accepted t w) := by
  unfold accepted; exact inferInstance

theorem range_iff_accepted (t : Source.IntTy) (w : Solidity.Roadmap.Word) :
    (t.lo ≤ Source.wordInt t w ∧ Source.wordInt t w ≤ t.hi) ↔ accepted t w.val := by
  obtain ⟨s,b,_,h8,h256⟩ := t
  have hw : w.val < 2^256 := w.isLt
  cases s with
  | true =>
    have hP : 2^(b-1) ≤ 2^255 := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : 1 ≤ 2^(b-1) := Nat.one_le_two_pow
    simp only [Source.IntTy.lo,Source.IntTy.hi,Source.wordInt,accepted,true_and,if_true]
    generalize 2^(b-1) = P at *
    split <;> omega
  | false =>
    have h1 : 1 ≤ 2^b := Nat.one_le_two_pow
    simp only [Source.IntTy.lo,Source.IntTy.hi,Source.wordInt,accepted,Bool.false_eq_true,false_and,if_false]
    generalize 2^b = P at *
    omega

theorem accepted_sign_bits (t : Source.IntTy) (signed : t.signed=true) (w : Nat) (hw : w < 2^256) :
    accepted t w ↔ w / 2^(t.bits-1)=0 ∨ w / 2^(t.bits-1)=2^(257-t.bits)-1 := by
  obtain ⟨s,b,_,h8,h256⟩ := t
  cases signed
  have hPQ : 2^(b-1)*2^(257-b)=2^256 := by rw [←Nat.pow_add]; congr 1; omega
  have hP : 0 < 2^(b-1) := Nat.two_pow_pos _
  have hQ : 0 < 2^(257-b) := Nat.two_pow_pos _
  simp only [accepted,if_true]
  generalize 2^(b-1) = P at *
  generalize 2^(257-b) = Q at *
  have hlt : w / P < Q := (Nat.div_lt_iff_lt_mul hP).mpr (by rw [Nat.mul_comm, hPQ]; exact hw)
  have hz : w / P = 0 ↔ w < P := by
    rw [Nat.div_eq_zero_iff]; omega
  have hm : Q-1 ≤ w / P ↔ (Q-1)*P ≤ w := Nat.le_div_iff_mul_le hP
  have hq : (Q-1)*P = 2^256-P := by rw [Nat.sub_one_mul, Nat.mul_comm, hPQ]
  rw [hq] at hm
  omega

/-- The value of an accepted word, stated without `wordInt`: a signed word in
the low band is itself, one in the high band is `w - 2^256`; an unsigned word
is itself. -/
theorem accepted_value (t : Source.IntTy) (w : Solidity.Roadmap.Word) (h : accepted t w.val) :
    Source.wordInt t w =
      if t.signed ∧ 2^(t.bits-1) ≤ w.val then (w.val : Int)-((2^256 : Nat) : Int) else (w.val : Int) := by
  obtain ⟨s,b,_,h8,h256⟩ := t
  have hw : w.val < 2^256 := w.isLt
  cases s with
  | true =>
    have hP : 2^(b-1) ≤ 2^255 := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : 1 ≤ 2^(b-1) := Nat.one_le_two_pow
    simp only [accepted,if_true] at h
    simp only [Source.wordInt,true_and]
    generalize 2^(b-1) = P at *
    split <;> split <;> omega
  | false =>
    simp only [Source.wordInt,Bool.false_eq_true,false_and,if_false]

/-- An accepted word decodes to its two's-complement (or zero-extended) value. -/
theorem decode_accepted (D : Source.Layout) (t : Source.IntTy) (w : Nat)
    (h : accepted t (Source.toWord w).val) :
    ∃ r, Source.decodeWord D w (.int t)=.ok (.int (Source.wordInt t (Source.toWord w)) r) := by
  have hr := (range_iff_accepted t (Source.toWord w)).mpr h
  exact ⟨hr,by rw [decode_range,dif_pos hr]⟩

/-- A word that is not the sign (or zero) extension of an in-width value reverts. -/
theorem decode_dirty (D : Source.Layout) (t : Source.IntTy) (w : Nat)
    (h : ¬accepted t (Source.toWord w).val) :
    Source.decodeWord D w (.int t)=.error (.revert []) := by
  have hr : ¬(t.lo ≤ Source.wordInt t (Source.toWord w) ∧ Source.wordInt t (Source.toWord w) ≤ t.hi) :=
    fun hr => h ((range_iff_accepted t (Source.toWord w)).mp hr)
  rw [decode_range,dif_neg hr]

theorem decode_ok_iff (D : Source.Layout) (t : Source.IntTy) (w : Nat) :
    (∃ v, Source.decodeWord D w (.int t)=.ok v) ↔ accepted t (Source.toWord w).val := by
  constructor
  · rintro ⟨v,hv⟩
    by_cases h : accepted t (Source.toWord w).val
    · exact h
    · rw [decode_dirty D t w h] at hv; cases hv
  · intro h
    obtain ⟨r,hr⟩ := decode_accepted D t w h
    exact ⟨_,hr⟩

private theorem mapM_ok_iff {α β ε : Type} (f : α → Except ε β) (L : List α) :
    (∃ xs, L.mapM f=.ok xs) ↔ ∀ a ∈ L, ∃ b, f a=.ok b := by
  induction L with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => ⟨[], rfl⟩⟩
  | cons a L ih =>
    rw [List.mapM_cons]
    constructor
    · rintro ⟨xs,hxs⟩
      cases ha : f a with
      | error e => rw [ha] at hxs; cases hxs
      | ok b =>
        rw [ha] at hxs
        cases hL : L.mapM f with
        | error e => rw [hL] at hxs; cases hxs
        | ok ys =>
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨b,ha⟩
          · exact ih.mp ⟨ys,hL⟩ x hx
    · intro hall
      obtain ⟨b,hb⟩ := hall a List.mem_cons_self
      obtain ⟨ys,hys⟩ := ih.mpr fun x hx => hall x (List.mem_cons_of_mem a hx)
      exact ⟨b :: ys,by rw [hb,hys];rfl⟩

theorem values_zero (D : Source.Layout) (t : Source.IntTy) (F : Source.Fr) (off : Nat) :
    values D t F off 0=.ok [] := rfl

/-- Validation reads the head word first, then the rest at the next word offset. -/
theorem values_succ (D : Source.Layout) (t : Source.IntTy) (F : Source.Fr) (off n : Nat) :
    values D t F off (n+1)=(do
      let x ← Source.decodeWord D (Source.cdWordAt F off) (.int t)
      let xs ← values D t F (off+32) n
      pure (x :: xs)) := by
  unfold values
  rw [List.range_succ_eq_map,List.mapM_cons,List.mapM_map]
  simp only [Function.comp_def,Nat.mul_zero,Nat.add_zero,Nat.mul_succ,Nat.add_comm (32*_) 32,
    ←Nat.add_assoc]

/-- Validation succeeds exactly when every raw word is width-accepted. -/
theorem values_ok_iff (D : Source.Layout) (t : Source.IntTy) (F : Source.Fr) (off len : Nat) :
    (∃ xs, values D t F off len=.ok xs) ↔
      ∀ j<len, accepted t (Source.toWord (Source.cdWordAt F (off+32*j))).val := by
  unfold values
  rw [mapM_ok_iff]
  constructor
  · intro h j hj
    exact (decode_ok_iff D t _).mp (h j (List.mem_range.mpr hj))
  · intro h j hj
    exact (decode_ok_iff D t _).mpr (h j (List.mem_range.mp hj))

/-- A rejected word at any position makes the whole validation fail. -/
theorem values_dirty (D : Source.Layout) (t : Source.IntTy) (F : Source.Fr) (off len j : Nat)
    (hj : j<len) (dirty : ¬accepted t (Source.toWord (Source.cdWordAt F (off+32*j))).val) :
    ∀ xs, values D t F off len≠.ok xs := fun xs hxs =>
  dirty ((values_ok_iff D t F off len).mp ⟨xs,hxs⟩ j hj)

/-! ## Frame binding -/

/-- Raw validation on argument bytes after the four-byte selector. -/
def dataValues (D : Source.Layout) (t : Source.IntTy) (data : List UInt8) (off len : Nat) :
    Source.R (List (Source.Val D (.int t))) :=
  (List.range len).mapM fun j =>
    Source.decodeWord D (Source.beValue (Source.fitBytes 32 (data.drop (off+32*j)))) (.int t)

theorem values_frame (D : Source.Layout) (t : Source.IntTy) (F : Source.Fr)
    (selectorBytes data : List UInt8) (four : selectorBytes.length=4)
    (binding : F.cd=selectorBytes++data) (off len : Nat) :
    values D t F (4+off) len=dataValues D t data off len := by
  unfold values dataValues
  congr 1
  funext j
  unfold Source.cdWordAt
  rw [binding,Nat.add_assoc,←four,List.drop_length_add_append]

/-- Complete ordered entry+copy outcome under the actual frame byte binding:
each entry guard failure, and each dirty word, preserves the initial state. -/
theorem guarded_frame_run {E : Source.Env} {Γ : Source.RCtx}
    (t : Source.IntTy) (F : Source.Fr) (selectorBytes data : List UInt8)
    (four : selectorBytes.length=4) (binding : F.cd=selectorBytes++data)
    (i : Nat) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy t) p.1 p.2).run y=
      let off := Source.wordAt data i
      let len := Source.wordAt (data.drop off) 0
      if data.length<off+32 then (.error (.revert []),y)
      else if 2^64≤len then (.error (.revert []),y)
      else if off+32+32*len≤data.length then
        match dataValues E.layout t data (off+32) len with
        | .error e => (.error e,y)
        | .ok xs => (.ok (.val (.memRef rfl y.2.heap.next)),
            (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy t,memory xs⟩).1}))
      else (.error (.revert []),y) := by
  rw [guarded_run]
  dsimp only
  by_cases head : data.length<Source.wordAt data i+32
  · simp only [Source.cdTail,if_pos head]
  · by_cases large : 2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0
    · simp only [Source.cdTail,if_neg head,if_pos large]
    · by_cases span : Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length
      · simp only [Source.cdTail,if_neg head,if_neg large,if_pos span,pure,Except.pure]
        rw [copy_run,Nat.add_assoc,values_frame E.layout t F selectorBytes data four binding]
        rfl
      · simp only [Source.cdTail,if_neg head,if_neg large,if_neg span]

end Solidity.Backend.CalldataPackets.RawInt
