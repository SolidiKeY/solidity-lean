import Solidity.Source.WellTyped
import Solidity.Source.ValueProgress

/-!
# `abi.decode` in the source semantics (lane FU2-B)

S01 types `abi.decode(data, (T₁, …, Tₙ))` (`Typed.abiDecode`): the data is
`bytes` in memory or storage or a string literal (`STy.decodeSrc`), the
second argument a parenthesized list of type expressions or a single one
(`Ctx.decodeTys`: elementary type names, user-defined types by name, arrays
of them, in `memory`), each a type the ABI decoder of S02/S04 reads
(`STy.decodable`: one-word value types, enums at their member count,
user-defined value types at their underlying type, `bytes`/`string` and
dynamic arrays of one-word values in memory). The interpreter evaluates it
by `abiDecodeData` (`Solidity/Source/Eval.lean`), which reuses the
decoder's `decodeArgs` after solc's head-size check.

This module proves, for that fragment:

- **preservation of the heap typing**: the decoder keeps `MemOK` (the heap
  well typed, shaped, with bare-value elements) and every value it returns
  agrees with the grown heap typing (`decodeArg_ok`, `decodeArgs_ok`,
  `abiDecodeData_ok`);
- **progress**: no decoding step is `stuck`; every halt is a revert with no
  data or Panic `0x41` (`NotStuck`), as solc's decoder;
- **the evaluation arm** (`evalE_abiDecode_ok`, `evalE_abiDecode_lit_ok`):
  relative to the data expression's own triple (gap-relative: the data
  expression is any typed expression, whose progress is the walk's), the
  `abi.decode` node keeps `MemOK` and halts only without `stuck`.

Named refusals outside the fragment (no derivation): static arrays,
structs, nested arrays, fixed point, external function types, qualified
type names (`L.S`), `bytes calldata` data, `abi.decode(data, ())`.
-/

namespace Solidity.Source

open Solidity.Roadmap (Bytes Word)
open EM

variable {E : Env} {Γ : RCtx}

/-! ## The decodable types -/

/-- `Env.layout` reads a user-defined value type's underlying type as
`Env.udvtUnderlying`, which S01's `STy.decodable` consults. -/
theorem Env.layout_underlying (E : Env) (d : DeclName) : E.layout.underlying d = E.udvtUnderlying d := rfl

theorem STy.wordElem_loc {τ : STy} (h : τ.wordElem = true) : τ.loc? = none := by
  cases τ <;> first | rfl | (simp only [STy.wordElem, reduceCtorEq] at h)

theorem STy.decodableElem_loc {τ : STy} (h : τ.decodableElem E = true) : τ.loc? = none := by
  cases τ <;> first | rfl | (simp only [STy.decodableElem, STy.wordElem, reduceCtorEq] at h)

theorem STy.decodableElem_isValueTy {τ : STy} (h : τ.decodableElem E = true) : τ.isValueTy = true := by
  cases τ <;> first | rfl | (simp only [STy.decodableElem, STy.wordElem, reduceCtorEq] at h)

/-! ## Words -/

theorem readInt_range {t : IntTy} {w : Word} {v : Int} (h : readInt t w = some v) : t.lo ≤ v ∧ v ≤ t.hi := by
  simp only [readInt] at h
  split at h
  · cases h; assumption
  · cases h

/-- **A one-word value's decoder is never stuck**: an invalid word reverts. -/
theorem decodeElemWord_ok (D : Layout) (w : Nat) {τ : STy} (hτ : τ.wordElem = true) :
    NotStuckR (decodeElemWord D w τ) := by
  intro x hx
  cases τ <;> simp only [STy.wordElem, reduceCtorEq] at hτ <;> simp only [decodeElemWord] at hx
  case int t =>
    split at hx
    · exact mkInt_ok t (readInt_range ‹_›) x hx
    · cases hx
  all_goals (repeat' split at hx) <;> cases hx

theorem decodeWord_ok (w : Nat) {τ : STy} (hτ : τ.decodableElem E = true) :
    NotStuckR (decodeWord E.layout w τ) := by
  cases τ
  case udvt d =>
    intro x hx
    have h := decodeElemWord_ok E.layout w (τ := E.layout.underlying d) hτ
    simp only [decodeWord] at hx
    cases hr : decodeElemWord E.layout w (E.layout.underlying d) with
    | ok v => rw [hr] at hx; cases hx
    | error e =>
      rw [hr] at hx
      cases hx
      exact h x hr
  all_goals
    first
    | (simp only [decodeWord]; exact decodeElemWord_ok _ _ hτ)
    | (simp only [STy.decodableElem, STy.wordElem, reduceCtorEq] at hτ)

/-! ## Hoare triples without `stuck` -/

/-- A lifted result that is never stuck. -/
theorem Hoare.lift_ns {P : EMState E Γ → Prop} {α : Type} {r : R α} (h : NotStuckR r) :
    Hoare P (lift r : EM E Γ α) (fun _ y => P y) (fun e y => P y ∧ NotStuck e) :=
  Hoare.lift' fun x hx => by
    cases r with
    | ok a => exact hx
    | error e =>
      refine ⟨hx, ?_⟩
      cases e with
      | stuck w => exact h w rfl
      | _ => trivial

/-- **Growing the heap typing**, `Hoare.memGrow` with halts that carry a
fact `X` besides `MemOK`. -/
theorem Hoare.memGrowX {α : Type} {m : EM E Γ α} {Q : α → EMState E Γ → Prop} {X : Halt → Prop}
    {H : HeapTy} {R : HeapTy → Prop}
    (h : ∀ H', Hoare (MemOK E H') m (fun a y => MemOK E H' y ∧ Q a y) (fun e y => MemOK E H' y ∧ X e)) :
    Hoare (fun y => MemOK E H y ∧ R y.2.heap.ty) m
      (fun a y => MemOK E H y ∧ Q a y ∧ ∃ H', R H' ∧ H'.Le y.2.heap.ty) (fun e y => MemOK E H y ∧ X e) := by
  intro y ⟨hj, hr⟩
  have h2 := h y.2.heap.ty y hj.self
  revert h2
  cases m.run y with
  | mk r y' =>
    cases r with
    | ok a => exact fun ⟨hj', hq⟩ => ⟨hj'.weaken hj.le, hq, _, hr, hj'.le⟩
    | error e => exact fun ⟨hj', hx⟩ => ⟨hj'.weaken hj.le, hx⟩

/-- `allocRef_mem` with any halt condition: the allocation never halts. -/
theorem allocRef_memX {H : HeapTy} {τ : STy} (x : Data E.layout τ) (hm : τ.loc? = some .memory)
    (ht : Data.Top x) (hi : Data.Inner x) {X : Halt → EMState E Γ → Prop} :
    Hoare (fun y => MemOK E H y ∧ DataOK E y.2.heap.ty x) (allocRef x : EM E Γ (Val E.layout τ))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) X := by
  unfold allocRef alloc
  intro ⟨l, s⟩ ⟨⟨⟨⟨hh, hle⟩, hl⟩, hs, hin⟩, hx⟩
  simp only [Hoare.run_bind, dif_pos hm]
  exact ⟨⟨⟨⟨hh.alloc hx, hle.trans (Heap.alloc_le s.heap _)⟩, LocalsOK.mono (Heap.alloc_le s.heap _) l hl⟩,
    hs.alloc ht, hin.alloc hi⟩, τ, Heap.alloc_ty s.heap ⟨τ, x⟩, rfl⟩

/-- A `mapM` of steps that keep `P` and are never stuck. -/
theorem List.mapM_ok {P : EMState E Γ → Prop} {α β : Type} (f : α → EM E Γ β)
    (hf : ∀ a, Hoare P (f a) (fun _ y => P y) (fun e y => P y ∧ NotStuck e)) (l : List α) :
    Hoare P (l.mapM f) (fun _ y => P y) (fun e y => P y ∧ NotStuck e) := by
  suffices h : ∀ (acc : List β), Hoare P (List.mapM.loop f l acc) (fun _ y => P y) (fun e y => P y ∧ NotStuck e)
    from h []
  induction l with
  | nil => intro acc; exact Hoare.pure' fun _ h => h
  | cons a as ih => intro acc; exact Hoare.bind (hf a) fun b => ih (b :: acc)

/-! ## The decoder -/

/-- **A dynamic argument's tail**: it keeps any invariant, and halts only
by a revert with no data or Panic `0x41`. -/
theorem tailBytes_ok {P : EMState E Γ → Prop} (data : Bytes) (i : Nat) :
    Hoare P (tailBytes data i : EM E Γ Bytes) (fun _ y => P y) (fun e y => P y ∧ NotStuck e) := by
  unfold tailBytes
  dsimp only
  split
  · exact Hoare.halt' fun _ hx => ⟨hx, trivial⟩
  · split
    · exact Hoare.lift' fun _ hx => ⟨hx, trivial⟩
    · split
      · exact Hoare.pure' fun _ hx => hx
      · exact Hoare.halt' fun _ hx => ⟨hx, trivial⟩

/-- A one-word argument: its decoder is a lifted `decodeWord`. -/
theorem decodeArg_word {H : HeapTy} (data : Bytes) (i : Nat) {τ : STy} (hτ : τ.decodableElem E = true)
    (he : (decodeArg data i τ : EM E Γ (Val E.layout τ)) = lift (decodeWord E.layout (wordAt data i) τ)) :
    Hoare (MemOK E H) (decodeArg data i τ : EM E Γ (Val E.layout τ))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun e y => MemOK E H y ∧ NotStuck e) := by
  rw [he]
  exact Hoare.conseq (Hoare.lift_ns (decodeWord_ok _ hτ)) (fun _ h => h)
    (fun v _ hy => ⟨hy, Val.refOK_of_loc (STy.decodableElem_loc hτ) v⟩) (fun _ _ h => h)

/-- **Decoding one argument keeps the memory invariant** and is never
stuck at a type the decoder reads; the value agrees with the grown heap
typing. -/
theorem decodeArg_ok {H : HeapTy} (data : Bytes) (i : Nat) {τ : STy} (hτ : τ.decodable E = true) :
    Hoare (MemOK E H) (decodeArg data i τ : EM E Γ (Val E.layout τ))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun e y => MemOK E H y ∧ NotStuck e) := by
  cases τ
  case bytes l =>
    cases l
    case memory =>
      simp only [decodeArg]
      exact Hoare.bind (tailBytes_ok data i) fun bs =>
        Hoare.conseq (allocRef_memX _ rfl (by trivial) (by trivial)) (fun y hy => ⟨hy, .bytes bs⟩)
          (fun _ _ h => h) (fun _ _ h => h)
    all_goals simp only [STy.decodable, STy.decodableElem, STy.wordElem, reduceCtorEq] at hτ
  case string l =>
    cases l
    case memory =>
      simp only [decodeArg]
      exact Hoare.bind (tailBytes_ok data i) fun bs =>
        Hoare.conseq (allocRef_memX _ rfl (by trivial) (by trivial)) (fun y hy => ⟨hy, .string bs⟩)
          (fun _ _ h => h) (fun _ _ h => h)
    all_goals simp only [STy.decodable, STy.decodableElem, STy.wordElem, reduceCtorEq] at hτ
  case array l σ k =>
    cases l <;> cases k <;> simp only [STy.decodable, STy.decodableElem, STy.wordElem, reduceCtorEq] at hτ
    simp only [decodeArg, if_pos (STy.decodableElem_isValueTy hτ)]
    split
    · exact Hoare.halt' fun _ hx => ⟨hx, trivial⟩
    · split
      · exact Hoare.lift' fun _ hx => ⟨hx, trivial⟩
      · split
        · refine Hoare.bind (List.mapM_ok _ (fun _ => Hoare.lift_ns (decodeWord_ok _ hτ)) _) fun xs => ?_
          exact Hoare.conseq (allocRef_memX _ rfl (by trivial) (by exact fun _ => ⟨_, rfl⟩))
            (fun y hy => ⟨hy, .array fun _ => .val (Val.refOK_of_loc (STy.decodableElem_loc hτ) _)⟩)
            (fun _ _ h => h) (fun _ _ h => h)
        · exact Hoare.halt' fun _ hx => ⟨hx, trivial⟩
  all_goals
    first
    | exact decodeArg_word data i hτ rfl
    | (simp only [STy.decodable, STy.decodableElem, STy.wordElem, reduceCtorEq] at hτ; done)

/-- **Decoding arguments keeps the memory invariant** and is never stuck;
the values agree with the grown heap typing. -/
theorem decodeArgs_ok {H : HeapTy} (data : Bytes) : ∀ (τs : List STy) (i : Nat),
    τs.all (STy.decodable E) = true →
    Hoare (MemOK E H) (decodeArgs data τs i : EM E Γ (Vals E.layout τs))
      (fun vs y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR) (fun e y => MemOK E H y ∧ NotStuck e)
  | [], _, _ => Hoare.pure' fun _ hy => ⟨hy, trivial⟩
  | τ :: τs, i, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [decodeArgs]
    refine Hoare.bind (decodeArg_ok data i h.1) fun v => ?_
    refine Hoare.bind (Hoare.memGrowX (R := fun H' => v.RefOK E H')
      fun H' => decodeArgs_ok (H := H') data τs (i + 1) h.2) fun vs => ?_
    exact Hoare.pure' fun _ ⟨hy, hvs, _, hv, hle⟩ => ⟨hy, hv.mono hle, hvs⟩

/-- A call's value from agreeing returns agrees. -/
theorem RValOK.mkRet {H : HeapTy} : ∀ (rs : List STy) (vs : RVals E.layout rs),
    RValsOK E H vs → RValOK E H (mkRet rs vs)
  | [_], .cons _ .nil, h => h.1
  | [], _, h => h
  | _ :: _ :: _, _, h => h

/-- **`abi.decode` keeps the memory invariant and is never stuck** at
types the decoder reads: short data reverts with no data; the value agrees
with the grown heap typing. -/
theorem abiDecodeData_ok {H : HeapTy} (data : Bytes) {τs : List STy} (hd : τs.all (STy.decodable E) = true) :
    Hoare (MemOK E H) (abiDecodeData data τs : EM E Γ (RVal E.layout (STy.ret τs)))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  unfold abiDecodeData
  split
  · exact Hoare.halt' fun _ hy => ⟨hy, trivial⟩
  · exact Hoare.bind (decodeArgs_ok data τs 0 hd) fun _ =>
      Hoare.pure' fun _ ⟨hy, hvs⟩ => ⟨hy, RValOK.mkRet τs _ hvs⟩

/-! ## The evaluation arm -/

/-- The bytes of agreeing `bytes memory` data are read without `stuck`. -/
theorem bytesOfRV_mem_ok (F : Fr) (n : Nat) {H : HeapTy} (v : RVal E.layout (.bytes .memory)) :
    Hoare (fun y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (bytesOfRV F n v : EM E Γ Bytes)
      (fun _ y => MemOK E H y) (fun e y => MemOK E H y ∧ NotStuck e) := by
  cases v with
  | val x =>
    cases x with
    | memRef h a =>
      simp only [bytesOfRV]
      refine Hoare.conseq (heapBytes_ok (P := fun y => MemOK E H y ∧ RValOK E y.2.heap.ty (.val (.memRef h a)))
        a fun y hy => ⟨⟨hy.1.1, hy.1.2.1⟩, ?_⟩) (fun _ h => h) (fun _ _ h => h.1) (fun _ _ h => h.elim)
      obtain ⟨σ, hσ, hs⟩ := hy.2
      cases σ <;> simp only [STy.memShape, reduceCtorEq, STy.bytes.injEq] at hs
      · exact ⟨_, .inl hσ⟩
      · exact ⟨_, .inr hσ⟩
    | storRef h _ => simp only [STy.loc?, Option.some.injEq, reduceCtorEq] at h
    | cdRef _ _ => exact Hoare.of_false fun _ hy => hy.2

/-- **The `abi.decode` arm on `bytes memory` data** keeps `MemOK` and is
never stuck, relative to the data expression's triple (gap-relative
progress: the data expression's own progress is the walk's). -/
theorem evalE_abiDecode_ok (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy} {τs : List STy}
    (data : RExpr E Γ (.bytes .memory)) (hs : STy.decodeSrc (.bytes .memory) = true)
    (hd : τs.all (STy.decodable E) = true)
    (hdata : Hoare (MemOK E H) (evalE G F n data)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.abiDecode data hs hd))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  simp only [evalE]
  exact Hoare.bind hdata fun v => Hoare.bind (bytesOfRV_mem_ok F n v) fun bs => abiDecodeData_ok bs hd

/-- **The `abi.decode` arm on a string literal** keeps `MemOK` and is never
stuck. -/
theorem evalE_abiDecode_lit_ok (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy} {τs : List STy}
    {bs : List UInt8} (hs : STy.decodeSrc (.stringLit bs) = true) (hd : τs.all (STy.decodable E) = true) :
    Hoare (MemOK E H) (evalE G F (n + 1 + 1) (.abiDecode (.str bs : RExpr E Γ _) hs hd))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  simp only [evalE, bytesOfRV]
  exact abiDecodeData_ok bs hd

/-- info: 'Solidity.Source.decodeArg_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.decodeArg_ok
/-- info: 'Solidity.Source.decodeArgs_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.decodeArgs_ok
/-- info: 'Solidity.Source.abiDecodeData_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.abiDecodeData_ok
/-- info: 'Solidity.Source.evalE_abiDecode_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalE_abiDecode_ok
/-- info: 'Solidity.Source.evalE_abiDecode_lit_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalE_abiDecode_lit_ok

end Solidity.Source
