import Solidity.Yul.Layout.View

/-!
# The allocation laws of the layout view

`alloc_read` and `alloc_total` are the statements of the same-named fields of
`Shrink.LayoutView.Laws` at `view`.

`geometry.write` refuses a nested dynamic array or `bytes` in memory, so the
allocator builds those itself (`put`), and read-after-allocation is proved for
`put` directly instead of through `write_read`. `put_spec` is a mutual
recursion over the written tree. A value at address `a` with tail pointer `f`
owns its inline bytes `[a, a + memSize L)` and its out-of-line bytes
`[f, f + tailSize L t)`; `Placed` says that the write changes memory only
there, and that EVERY state that agrees with the result there reads the tree
back with a read footprint inside those bytes. Stating the read for every
agreeing state is what lets a sibling survive the later writes without a
separate locality argument: the later writes own other bytes.

`alloc_total` follows from `put_total` (a fitting mapping-free tree is always
placed) and `size_le` (the allocation takes at most `64 * Tree.weight` bytes).
-/
namespace Solidity.Yul.Layout

open Solidity.Goals
open Solidity.Yul.Views

/-! ## Words and members -/

private theorem bind_some {α β : Type} {a : Option α} {f : α → Option β} {b : β}
    (h : a.bind f = some b) : ∃ x, a = some x ∧ f x = some b := by
  cases a with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

private theorem map_some {α β : Type} {a : Option α} {g : α → β} {b : β}
    (h : a.map g = some b) : ∃ x, a = some x ∧ g x = b := by
  cases a with
  | none => cases h
  | some x => exact ⟨x, rfl, Option.some.inj h⟩

/-- Memories that agree on a word load the same word. -/
private theorem mloadNat_agree (b b' : ByteView) (a : Nat)
    (h : ∀ x, a ≤ x ∧ x < a + 32 → b x = b' x) : mloadNat b a = mloadNat b' a :=
  readBE_congr _ _ _ _ fun i hi => h _ ⟨Nat.le_add_right a i, Nat.add_lt_add_left hi a⟩

/-- A stored memory word below `2 ^ 256` loads as itself. -/
private theorem mloadNat_mstore (b : ByteView) (a n : Nat) (hn : n < 2 ^ 256) :
    mloadNat (mstore b a (Shrink.toWord n)) a = n :=
  (congrArg Fin.val (mload_mstore b a (Shrink.toWord n))).trans (Nat.mod_eq_of_lt hn)

/-- A memory that agrees with a written two-word header loads its two words. -/
private theorem header_load (b b' : ByteView) (a n f : Nat) (hn : n < 2 ^ 256)
    (hf : f < 2 ^ 256)
    (h : ∀ x, a ≤ x ∧ x < a + 64 →
      b' x = mstore (mstore b a (Shrink.toWord n)) (a + 32) (Shrink.toWord f) x) :
    mloadNat b' a = n ∧ mloadNat b' (a + 32) = f :=
  ⟨(mloadNat_agree b' (mstore b a (Shrink.toWord n)) a fun x hx =>
      (h x (by omega)).trans (mstore_outside _ _ _ _ (by omega))).trans
      (mloadNat_mstore _ _ _ hn),
    (mloadNat_agree b' _ (a + 32) fun x hx => h x (by omega)).trans (mloadNat_mstore _ _ _ hf)⟩

private theorem elem_mem (P : Shrink.Params) (e : Shrink.Layout) (b o i : Nat) :
    geometry.elem P e ⟨.memory, b, o⟩ i = ⟨.memory, b + memSize e * i, indirect e⟩ := rfl

private theorem field_mem (P : Shrink.Params) (all : List Shrink.Layout) (b o i : Nat)
    (g : Shrink.Layout) (h : all[i]? = some g) :
    geometry.field P all ⟨.memory, b, o⟩ i = ⟨.memory, b + memberOffset all i, indirect g⟩ := by
  simp only [geometry, if_true, h, Option.map_some, Option.getD_some]

private theorem memberOffset_zero (fs : List Shrink.Layout) : memberOffset fs 0 = 0 := by
  cases fs <;> rfl

private theorem memberOffset_succ : ∀ (all : List Shrink.Layout) (i : Nat) (g : Shrink.Layout),
    all[i]? = some g → memberOffset all (i + 1) = memberOffset all i + memSize g
  | [], _, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | f :: fs, 0, g, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [memberOffset, memberOffset_zero, Nat.add_zero, Nat.zero_add]
  | f :: fs, i + 1, g, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [memberOffset, memberOffset_succ fs i g h]
    omega

/-! ## What a placed value leaves -/

/-- A write from `m` to `m'` that owns `[a, a + n)` and `[f, f + k)`: slots are
kept, memory changes only there, and every state that agrees with `m'` there
is `good`. -/
private structure Placed (m m' : Shrink.Phys) (a n f k : Nat) (good : Shrink.Phys → Prop) :
    Prop where
  storage : m'.storage = m.storage
  transient : m'.transient = m.transient
  frame : ∀ x, ¬ (a ≤ x ∧ x < a + n) → ¬ (f ≤ x ∧ x < f + k) → m'.memory x = m.memory x
  good : ∀ m'' : Shrink.Phys,
    (∀ x, (a ≤ x ∧ x < a + n) ∨ (f ≤ x ∧ x < f + k) → m''.memory x = m'.memory x) → good m''

/-- A memory word placed. -/
private theorem scalar_placed (P : Shrink.Params) (w v a o f : Nat) (m : Shrink.Phys)
    (hf : 0 < w ∧ w ≤ 32 ∧ v < 256 ^ w) :
    Placed m (m.withMemory (mstore m.memory a (Shrink.toWord v))) a 32 f 0 fun m'' =>
      geometry.read P (.scalar w) ⟨.memory, a, o⟩ m'' = some (.leaf v) ∧
      ∀ c, geometry.cells P (.scalar w) ⟨.memory, a, o⟩ m'' c →
        ∃ x, c = .mem x ∧ ((a ≤ x ∧ x < a + 32) ∨ (f ≤ x ∧ x < f + 0)) := by
  refine ⟨rfl, rfl, fun x hx _ => mstore_outside _ _ _ _ hx, fun m'' agree => ⟨?_, ?_⟩⟩
  · have hv : v < 2 ^ 256 := Nat.lt_of_lt_of_le hf.2.2
      (Nat.pow_le_pow_right (by decide : 0 < 256) hf.2.1)
    have load : mloadNat m''.memory a = v :=
      (mloadNat_agree _ _ a fun x hx => agree x (.inl hx)).trans (mloadNat_mstore _ _ _ hv)
    simp only [Shrink.Geometry.read, geometry, ↓reduceIte, load, Nat.mod_eq_of_lt hf.2.2,
      ite_self, Option.map_some]
  · intro c hc
    simp only [Shrink.Geometry.cells, geometry, ↓reduceIte] at hc
    cases c with
    | slot r s b => exact hc.elim
    | mem x => exact ⟨x, rfl, .inl hc⟩

/-- An indirect `bytes` placed: the header inline, the payload at `f`. -/
private theorem bytes_placed (P : Shrink.Params) (bs : List UInt8) (a f : Nat) (m : Shrink.Phys)
    (hb : bs.length < 2 ^ 256) (ha : a + 64 ≤ f) (hk : f + bs.length < 2 ^ 256) :
    Placed m (m.withMemory (copyBytes
        (mstore (mstore m.memory a (Shrink.toWord bs.length)) (a + 32) (Shrink.toWord f))
        (calldataBytes bs) f 0 bs.length)) a 64 f bs.length fun m'' =>
      geometry.read P .bytes ⟨.memory, a, 1⟩ m'' = some (.blob bs) ∧
      ∀ c, geometry.cells P .bytes ⟨.memory, a, 1⟩ m'' c →
        ∃ x, c = .mem x ∧ ((a ≤ x ∧ x < a + 64) ∨ (f ≤ x ∧ x < f + bs.length)) := by
  refine ⟨rfl, rfl, fun y h1 h2 => ?_, fun m'' agree => ?_⟩
  · exact (copyBytes_outside _ _ _ _ _ _ h2).trans
      ((mstore_outside _ _ _ _ (by omega)).trans (mstore_outside _ _ _ _ (by omega)))
  · obtain ⟨hl, hd⟩ := header_load m.memory m''.memory a bs.length f hb (by omega) fun y hy =>
      (agree y (.inl hy)).trans (copyBytes_outside _ _ _ _ _ _ (by omega))
    have payload : readBytes m''.memory f bs.length = bs := by
      apply List.ext_getElem
      · simp only [readBytes, List.length_map, List.length_range]
      · intro i _ hi
        simp only [readBytes, List.getElem_map, List.getElem_range]
        rw [agree (f + i) (by omega)]
        exact (find_copyBytes _ _ _ _ _ i hi).trans (by
          simp only [calldataBytes, Nat.zero_add, List.getElem?_eq_getElem hi, Option.getD_some])
    refine ⟨?_, fun c hc => ?_⟩
    · simp only [Shrink.Geometry.read, geometry, dataLoc, ↓reduceIte, Nat.one_ne_zero, hl, hd,
        payload, Option.map_some]
    · simp only [Shrink.Geometry.cells, geometry, dataLoc, ↓reduceIte, Nat.one_ne_zero, hl,
        hd] at hc
      cases c with
      | slot r s b => rcases hc with hc | hc <;> exact hc.elim
      | mem y => exact ⟨y, rfl, hc⟩

/-! ## Read after placement -/

mutual
/-- A placed value is read back from every state that agrees with the result
on the bytes it owns, and its read footprint lies in those bytes. -/
private theorem put_spec (P : Shrink.Params) :
    ∀ (t : Shrink.Tree) (L : Shrink.Layout) (a f : Nat) (m m' : Shrink.Phys), L.Fits t →
      a + memSize L ≤ f → f + tailSize L t < 2 ^ 256 →
      put P L ⟨.memory, a, indirect L⟩ t f m = some m' →
      Placed m m' a (memSize L) f (tailSize L t) fun m'' =>
        geometry.read P L ⟨.memory, a, indirect L⟩ m'' = some t ∧
        ∀ c, geometry.cells P L ⟨.memory, a, indirect L⟩ m'' c →
          ∃ x, c = .mem x ∧ ((a ≤ x ∧ x < a + memSize L) ∨ (f ≤ x ∧ x < f + tailSize L t))
  | .leaf v, L, a, f, m, m', hf, _, _, h => by
    cases L with
    | scalar w =>
      rw [Shrink.Layout.Fits] at hf
      simp only [put, Shrink.Geometry.write, if_pos hf, geometry, ↓reduceIte,
        Option.some.injEq] at h
      subst h
      exact scalar_placed P w v a _ f m hf
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .keyed _, L, a, f, m, m', hf, _, _, h => by
    cases L with
    | mapping v => simp only [put, reduceCtorEq] at h
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .blob bs, L, a, f, m, m', hf, ha, hk, h => by
    cases L with
    | bytes =>
      rw [Shrink.Layout.Fits] at hf
      rw [put, if_pos hf] at h
      cases h
      simp only [memSize, tailSize] at ha hk ⊢
      have p := bytes_placed P bs a f m hf ha (by omega)
      refine ⟨p.storage, p.transient, fun y h1 h2 => p.frame y h1 (by omega),
        fun m'' agree => ?_⟩
      obtain ⟨r, c⟩ := p.good m'' fun y hy => agree y (by omega)
      refine ⟨r, fun c' hc => ?_⟩
      obtain ⟨y, rfl, hy⟩ := c c' hc
      exact ⟨y, rfl, by omega⟩
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .node xs, L, a, f, m, m', hf, ha, hk, h => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Layout.Fits] at hf
      obtain ⟨rfl, hn, hall⟩ := hf
      rw [put, if_pos ⟨rfl, hn⟩] at h
      simp only [memSize, tailSize] at ha hk ⊢
      have ec : xs.length * memSize e = memSize e * xs.length := Nat.mul_comm _ _
      have ez : memSize e * (0 + xs.length) = memSize e * xs.length := by rw [Nat.zero_add]
      have p := putElems_spec P xs e a _ 0 f m m' hall (by omega) hk h
      refine ⟨p.storage, p.transient, fun y h1 h2 => p.frame y (by omega) (by omega),
        fun m'' agree => ?_⟩
      obtain ⟨r, c⟩ := p.good m'' fun y hy => agree y (by omega)
      refine ⟨by rw [Shrink.Geometry.read, r]; rfl, fun c' hc => ?_⟩
      rw [Shrink.Geometry.cells] at hc
      obtain ⟨y, rfl, hy⟩ := c c' hc
      exact ⟨y, rfl, by omega⟩
    | dynArray e =>
      rw [Shrink.Layout.Fits] at hf
      rw [put, if_pos hf.1] at h
      simp only [memSize, tailSize] at ha hk ⊢
      have ec : xs.length * memSize e = memSize e * xs.length := Nat.mul_comm _ _
      have ez : memSize e * (0 + xs.length) = memSize e * xs.length := by rw [Nat.zero_add]
      have p := putElems_spec P xs e f 0 0 (f + xs.length * memSize e) _ m' hf.2 (by omega)
        (by omega) h
      refine ⟨p.storage, p.transient, fun y h1 h2 => ?_, fun m'' agree => ?_⟩
      · exact (p.frame y (by omega) (by omega)).trans
          ((mstore_outside _ (a + 32) _ _ (by omega)).trans (mstore_outside _ a _ _ (by omega)))
      · obtain ⟨hl, hd⟩ := header_load m.memory m''.memory a xs.length f hf.1 (by omega)
          fun y hy => (agree y (.inl hy)).trans (p.frame y (by omega) (by omega))
        obtain ⟨r, c⟩ := p.good m'' fun y hy => agree y (by omega)
        have hlen : geometry.length P ⟨.memory, a, indirect (.dynArray e)⟩ m'' = xs.length := hl
        have hdat : geometry.data P ⟨.memory, a, indirect (.dynArray e)⟩ m'' = ⟨.memory, f, 0⟩ :=
          congrArg (fun w => (⟨.memory, w, 0⟩ : Shrink.Loc)) hd
        refine ⟨by rw [Shrink.Geometry.read, hdat, hlen, r]; rfl, fun c' hc => ?_⟩
        rw [Shrink.Geometry.cells, hdat, hlen] at hc
        rcases hc with hc | hc
        · cases c' with
          | slot r s b => exact hc.elim
          | mem y => exact ⟨y, rfl, .inl hc⟩
        · obtain ⟨y, rfl, hy⟩ := c c' hc
          exact ⟨y, rfl, by omega⟩
    | struct fs =>
      rw [Shrink.Layout.Fits] at hf
      rw [put] at h
      simp only [memSize, tailSize] at ha hk ⊢
      have z := memberOffset_zero fs
      have p := putFields_spec P xs fs fs a _ 0 f m m' hf (fun j => by rw [Nat.zero_add])
        (by omega) hk h
      refine ⟨p.storage, p.transient, fun y h1 h2 => p.frame y (by omega) (by omega),
        fun m'' agree => ?_⟩
      obtain ⟨r, c⟩ := p.good m'' fun y hy => agree y (by omega)
      refine ⟨by rw [Shrink.Geometry.read, r]; rfl, fun c' hc => ?_⟩
      rw [Shrink.Geometry.cells] at hc
      obtain ⟨y, rfl, hy⟩ := c c' hc
      exact ⟨y, rfl, by omega⟩
    | _ => simp only [Shrink.Layout.Fits] at hf
private theorem putElems_spec (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (b o i f : Nat) (m m' : Shrink.Phys),
      e.FitsAll xs → b + memSize e * (i + xs.length) ≤ f → f + tailSizes e xs < 2 ^ 256 →
      putElems P e ⟨.memory, b, o⟩ xs i f m = some m' →
      Placed m m' (b + memSize e * i) (memSize e * xs.length) f (tailSizes e xs) fun m'' =>
        geometry.readElems P e ⟨.memory, b, o⟩ xs.length i m'' = some xs ∧
        ∀ c, geometry.elemCells P e ⟨.memory, b, o⟩ xs.length i m'' c →
          ∃ x, c = .mem x ∧
            ((b + memSize e * i ≤ x ∧ x < b + memSize e * i + memSize e * xs.length) ∨
              (f ≤ x ∧ x < f + tailSizes e xs))
  | [], e, b, o, i, f, m, m', _, _, _, h => by
    rw [putElems] at h
    cases h
    refine ⟨rfl, rfl, fun _ _ _ => rfl, fun m'' _ => ⟨?_, fun c hc => ?_⟩⟩
    · rw [List.length_nil, Shrink.Geometry.readElems]
    · rw [List.length_nil, Shrink.Geometry.elemCells] at hc
      exact hc.elim
  | x :: xs, e, b, o, i, f, m, m', hf, ha, hk, h => by
    rw [Shrink.Layout.FitsAll] at hf
    rw [putElems, elem_mem] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    rw [tailSizes] at hk ⊢
    rw [List.length_cons] at ha ⊢
    have e1 : memSize e * (i + (xs.length + 1)) =
        memSize e * i + memSize e + memSize e * xs.length := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    have e2 : memSize e * (i + 1 + xs.length) =
        memSize e * i + memSize e + memSize e * xs.length := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have e3 : memSize e * (i + 1) = memSize e * i + memSize e := Nat.mul_succ _ _
    have e4 : memSize e * (xs.length + 1) = memSize e * xs.length + memSize e :=
      Nat.mul_succ _ _
    have px := put_spec P x e (b + memSize e * i) f m m₁ hf.1 (by omega) (by omega) hx
    have pxs := putElems_spec P xs e b o (i + 1) (f + tailSize e x) m₁ m' hf.2 (by omega)
      (by omega) hxs
    refine ⟨pxs.storage.trans px.storage, pxs.transient.trans px.transient,
      fun y h1 h2 => ?_, fun m'' agree => ?_⟩
    · exact (pxs.frame y (by omega) (by omega)).trans (px.frame y (by omega) (by omega))
    · obtain ⟨rx, cx⟩ := px.good m'' fun y hy =>
        (agree y (by omega)).trans (pxs.frame y (by omega) (by omega))
      obtain ⟨rxs, cxs⟩ := pxs.good m'' fun y hy => agree y (by omega)
      refine ⟨?_, fun c hc => ?_⟩
      · rw [Shrink.Geometry.readElems, elem_mem, rx, rxs]
        rfl
      · rw [Shrink.Geometry.elemCells, elem_mem] at hc
        rcases hc with hc | hc
        · obtain ⟨y, rfl, hy⟩ := cx c hc
          exact ⟨y, rfl, by omega⟩
        · obtain ⟨y, rfl, hy⟩ := cxs c hc
          exact ⟨y, rfl, by omega⟩
private theorem putFields_spec (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (b o i f : Nat)
      (m m' : Shrink.Phys), Shrink.Layout.FitsFields fs xs → (∀ j, all[i + j]? = fs[j]?) →
      b + memberOffset all i + memSizes fs ≤ f → f + tailFields fs xs < 2 ^ 256 →
      putFields P all ⟨.memory, b, o⟩ fs xs i f m = some m' →
      Placed m m' (b + memberOffset all i) (memSizes fs) f (tailFields fs xs) fun m'' =>
        geometry.readFields P all ⟨.memory, b, o⟩ fs i m'' = some xs ∧
        ∀ c, geometry.fieldCells P all ⟨.memory, b, o⟩ fs i m'' c →
          ∃ x, c = .mem x ∧
            ((b + memberOffset all i ≤ x ∧ x < b + memberOffset all i + memSizes fs) ∨
              (f ≤ x ∧ x < f + tailFields fs xs))
  | [], [], all, b, o, i, f, m, m', _, _, _, _, h => by
    rw [putFields] at h
    cases h
    refine ⟨rfl, rfl, fun _ _ _ => rfl, fun m'' _ => ⟨?_, fun c hc => ?_⟩⟩
    · rw [Shrink.Geometry.readFields]
    · rw [Shrink.Geometry.fieldCells] at hc
      exact hc.elim
  | [], _ :: _, _, _, _, _, _, _, _, hf, _, _, _, _ => by
    simp only [Shrink.Layout.FitsFields] at hf
  | _ :: _, [], _, _, _, _, _, _, _, hf, _, _, _, _ => by
    simp only [Shrink.Layout.FitsFields] at hf
  | x :: xs, g :: fs, all, b, o, i, f, m, m', hf, hi, ha, hk, h => by
    rw [Shrink.Layout.FitsFields] at hf
    have hg : all[i]? = some g := hi 0
    have next : ∀ j, all[i + 1 + j]? = fs[j]? := fun j => by
      rw [show i + 1 + j = i + (j + 1) by omega]
      exact hi (j + 1)
    rw [putFields, field_mem P all b o i g hg] at h
    obtain ⟨m₁, hx, hxs⟩ := bind_some h
    rw [tailFields] at hk ⊢
    rw [memSizes] at ha ⊢
    have off := memberOffset_succ all i g hg
    have px := put_spec P x g (b + memberOffset all i) f m m₁ hf.1 (by omega) (by omega) hx
    have pxs := putFields_spec P xs fs all b o (i + 1) (f + tailSize g x) m₁ m' hf.2 next
      (by omega) (by omega) hxs
    refine ⟨pxs.storage.trans px.storage, pxs.transient.trans px.transient,
      fun y h1 h2 => ?_, fun m'' agree => ?_⟩
    · exact (pxs.frame y (by omega) (by omega)).trans (px.frame y (by omega) (by omega))
    · obtain ⟨rx, cx⟩ := px.good m'' fun y hy =>
        (agree y (by omega)).trans (pxs.frame y (by omega) (by omega))
      obtain ⟨rxs, cxs⟩ := pxs.good m'' fun y hy => agree y (by omega)
      refine ⟨?_, fun c hc => ?_⟩
      · rw [Shrink.Geometry.readFields, field_mem P all b o i g hg, rx, rxs]
        rfl
      · rw [Shrink.Geometry.fieldCells, field_mem P all b o i g hg] at hc
        rcases hc with hc | hc
        · obtain ⟨y, rfl, hy⟩ := cx c hc
          exact ⟨y, rfl, by omega⟩
        · obtain ⟨y, rfl, hy⟩ := cxs c hc
          exact ⟨y, rfl, by omega⟩
end

/-! ## Placement succeeds -/

private theorem elem_region (P : Shrink.Params) (e : Shrink.Layout) (l : Shrink.Loc) (i : Nat)
    (h : l.region = .memory) : (geometry.elem P e l i).region = .memory := by
  simp only [geometry, if_pos h]

private theorem field_region (P : Shrink.Params) (fs : List Shrink.Layout) (l : Shrink.Loc)
    (i : Nat) (h : l.region = .memory) : (geometry.field P fs l i).region = .memory := by
  simp only [geometry, if_pos h]

mutual
/-- A fitting mapping-free tree is placed at every memory location. -/
private theorem put_total (P : Shrink.Params) :
    ∀ (t : Shrink.Tree) (L : Shrink.Layout) (l : Shrink.Loc) (f : Nat) (m : Shrink.Phys),
      L.NoMapping → L.Fits t → l.region = .memory → ∃ m', put P L l t f m = some m'
  | .leaf v, L, l, f, m, _, hf, hr => by
    cases L with
    | scalar w =>
      rw [Shrink.Layout.Fits] at hf
      refine ⟨m.withMemory (mstore m.memory l.word (Shrink.toWord v)), ?_⟩
      simp only [put, Shrink.Geometry.write, if_pos hf, geometry, if_pos hr]
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .keyed _, L, l, f, m, hn, hf, _ => by
    cases L with
    | mapping v => simp only [Shrink.Layout.NoMapping] at hn
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .blob bs, L, l, f, m, _, hf, _ => by
    cases L with
    | bytes =>
      rw [Shrink.Layout.Fits] at hf
      exact ⟨_, by rw [put, if_pos hf]⟩
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .node xs, L, l, f, m, hn, hf, hr => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Layout.Fits] at hf
      simp only [Shrink.Layout.NoMapping] at hn
      rw [put, if_pos ⟨hf.1, hf.2.1⟩]
      exact putElems_total P xs e l 0 f m hn hf.2.2 hr
    | dynArray e =>
      rw [Shrink.Layout.Fits] at hf
      simp only [Shrink.Layout.NoMapping] at hn
      rw [put, if_pos hf.1]
      exact putElems_total P xs e _ 0 _ _ hn hf.2 rfl
    | struct fs =>
      rw [Shrink.Layout.Fits] at hf
      simp only [Shrink.Layout.NoMapping] at hn
      rw [put]
      exact putFields_total P xs fs fs l 0 f m hn hf hr
    | _ => simp only [Shrink.Layout.Fits] at hf
private theorem putElems_total (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (e : Shrink.Layout) (l : Shrink.Loc) (i f : Nat) (m : Shrink.Phys),
      e.NoMapping → e.FitsAll xs → l.region = .memory → ∃ m', putElems P e l xs i f m = some m'
  | [], _, _, _, _, m, _, _, _ => ⟨m, by rw [putElems]⟩
  | x :: xs, e, l, i, f, m, hn, hf, hr => by
    rw [Shrink.Layout.FitsAll] at hf
    obtain ⟨m₁, h₁⟩ := put_total P x e _ f m hn hf.1 (elem_region P e l i hr)
    obtain ⟨m', h⟩ := putElems_total P xs e l (i + 1) (f + tailSize e x) m₁ hn hf.2 hr
    exact ⟨m', by rw [putElems, h₁]; exact h⟩
private theorem putFields_total (P : Shrink.Params) :
    ∀ (xs : List Shrink.Tree) (fs all : List Shrink.Layout) (l : Shrink.Loc) (i f : Nat)
      (m : Shrink.Phys), (∀ g ∈ fs, g.NoMapping) → Shrink.Layout.FitsFields fs xs →
      l.region = .memory → ∃ m', putFields P all l fs xs i f m = some m'
  | [], [], _, _, _, _, m, _, _, _ => ⟨m, by rw [putFields]⟩
  | [], _ :: _, _, _, _, _, _, _, hf, _ => by simp only [Shrink.Layout.FitsFields] at hf
  | _ :: _, [], _, _, _, _, _, _, hf, _ => by simp only [Shrink.Layout.FitsFields] at hf
  | x :: xs, g :: fs, all, l, i, f, m, hn, hf, hr => by
    rw [Shrink.Layout.FitsFields] at hf
    obtain ⟨m₁, h₁⟩ := put_total P x g _ f m (hn g (List.mem_cons_self ..)) hf.1
      (field_region P all l i hr)
    obtain ⟨m', h⟩ := putFields_total P xs fs all l (i + 1) (f + tailSize g x) m₁
      (fun k hk => hn k (List.mem_cons_of_mem _ hk)) hf.2 hr
    exact ⟨m', by rw [putFields, h₁]; exact h⟩
end

/-! ## The size of a placed tree -/

mutual
/-- A fitting mapping-free tree takes at most 64 bytes per unit of weight. -/
private theorem size_le : ∀ (t : Shrink.Tree) (L : Shrink.Layout), L.NoMapping → L.Fits t →
    memSize L + tailSize L t ≤ 64 * t.weight
  | .leaf v, L, _, hf => by
    cases L with
    | scalar w => simp only [memSize, tailSize, Shrink.Tree.weight]; omega
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .keyed _, L, hn, hf => by
    cases L with
    | mapping v => simp only [Shrink.Layout.NoMapping] at hn
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .blob bs, L, _, hf => by
    cases L with
    | bytes => simp only [memSize, tailSize, Shrink.Tree.weight]; omega
    | _ => simp only [Shrink.Layout.Fits] at hf
  | .node xs, L, hn, hf => by
    cases L with
    | fixedArray e n =>
      rw [Shrink.Layout.Fits] at hf
      obtain ⟨rfl, _, hall⟩ := hf
      simp only [Shrink.Layout.NoMapping] at hn
      have s := sizes_le xs e hn hall
      simp only [memSize, tailSize, Shrink.Tree.weight]
      omega
    | dynArray e =>
      rw [Shrink.Layout.Fits] at hf
      simp only [Shrink.Layout.NoMapping] at hn
      have s := sizes_le xs e hn hf.2
      simp only [memSize, tailSize, Shrink.Tree.weight]
      omega
    | struct fs =>
      rw [Shrink.Layout.Fits] at hf
      simp only [Shrink.Layout.NoMapping] at hn
      have s := fields_le xs fs hn hf
      simp only [memSize, tailSize, Shrink.Tree.weight]
      omega
    | _ => simp only [Shrink.Layout.Fits] at hf
private theorem sizes_le : ∀ (xs : List Shrink.Tree) (e : Shrink.Layout), e.NoMapping →
    e.FitsAll xs → xs.length * memSize e + tailSizes e xs ≤ 64 * (xs.map Shrink.Tree.weight).sum
  | [], _, _, _ => by
    simp only [List.length_nil, Nat.zero_mul, tailSizes, List.map_nil, List.sum_nil]
    omega
  | x :: xs, e, hn, hf => by
    rw [Shrink.Layout.FitsAll] at hf
    have s := size_le x e hn hf.1
    have ss := sizes_le xs e hn hf.2
    simp only [List.length_cons, Nat.succ_mul, tailSizes, List.map_cons, List.sum_cons]
    omega
private theorem fields_le : ∀ (xs : List Shrink.Tree) (fs : List Shrink.Layout),
    (∀ g ∈ fs, g.NoMapping) → Shrink.Layout.FitsFields fs xs →
    memSizes fs + tailFields fs xs ≤ 64 * (xs.map Shrink.Tree.weight).sum
  | [], [], _, _ => by
    simp only [memSizes, tailFields, List.map_nil, List.sum_nil]
    omega
  | [], _ :: _, _, hf => by simp only [Shrink.Layout.FitsFields] at hf
  | _ :: _, [], _, hf => by simp only [Shrink.Layout.FitsFields] at hf
  | x :: xs, g :: fs, hn, hf => by
    rw [Shrink.Layout.FitsFields] at hf
    have s := size_le x g (hn g (List.mem_cons_self ..)) hf.1
    have ss := fields_le xs fs (fun k hk => hn k (List.mem_cons_of_mem _ hk)) hf.2
    simp only [memSizes, tailFields, List.map_cons, List.sum_cons]
    omega
end

/-! ## The root object -/

/-- The root object written at `a` is read back there; it owns
`[a, a + allocSize L t)`. -/
private theorem allocAt_spec (P : Shrink.Params) (L : Shrink.Layout) (t : Shrink.Tree) (a : Nat)
    (m m' : Shrink.Phys) (hf : L.Fits t) (hk : a + allocSize L t < 2 ^ 256)
    (h : allocAt P L a t m = some m') :
    m'.storage = m.storage ∧ m'.transient = m.transient ∧
      (∀ x, ¬ (a ≤ x ∧ x < a + allocSize L t) → m'.memory x = m.memory x) ∧
      geometry.read P L ⟨.memory, a, 0⟩ m' = some t ∧
      ∀ c, geometry.cells P L ⟨.memory, a, 0⟩ m' c →
        ∃ x, c = .mem x ∧ a ≤ x ∧ x < a + allocSize L t := by
  cases L with
  | bytes =>
    cases t with
    | blob bs =>
      rw [Shrink.Layout.Fits] at hf
      simp only [allocAt, Shrink.Geometry.write, geometry, ↓reduceIte, dif_pos hf,
        Option.some.injEq] at h
      subst h
      simp only [allocSize, tailSize] at hk ⊢
      have hl : mloadNat (bytesObjectView bs hf m.memory a) a = bs.length :=
        congrArg Fin.val (bytesObject_header bs hf m.memory a)
      refine ⟨rfl, rfl, fun x hx => bytesObject_residual bs hf m.memory a x (by omega), ?_,
        fun c hc => ?_⟩
      · simp only [Shrink.Geometry.read, geometry, dataLoc, ↓reduceIte, Shrink.Phys.withMemory,
          hl, bytesObject_payload_list, Option.map_some]
      · simp only [Shrink.Geometry.cells, geometry, dataLoc, ↓reduceIte, Shrink.Phys.withMemory,
          hl] at hc
        cases c with
        | slot r s b => rcases hc with hc | hc <;> exact hc.elim
        | mem y =>
          refine ⟨y, rfl, ?_⟩
          rcases hc with hc | hc
          · exact ⟨hc.1, by have := hc.2; omega⟩
          · exact ⟨by have := hc.1; omega, by have := hc.2; omega⟩
    | _ => simp only [Shrink.Layout.Fits] at hf
  | dynArray e =>
    cases t with
    | node xs =>
      rw [Shrink.Layout.Fits] at hf
      simp only [allocAt, if_pos hf.1] at h
      simp only [allocSize, tailSize] at hk ⊢
      have ez : memSize e * (0 + xs.length) = memSize e * xs.length := by rw [Nat.zero_add]
      have ec : xs.length * memSize e = memSize e * xs.length := Nat.mul_comm _ _
      have p := putElems_spec P xs e (a + 32) 0 0 (a + 32 + xs.length * memSize e) _ m' hf.2
        (by omega) (by omega) h
      have hlen : geometry.length P ⟨.memory, a, 0⟩ m' = xs.length :=
        (mloadNat_agree m'.memory _ a fun y hy => p.frame y (by omega) (by omega)).trans
          (mloadNat_mstore m.memory a _ hf.1)
      have hdat : geometry.data P ⟨.memory, a, 0⟩ m' = ⟨.memory, a + 32, 0⟩ := rfl
      obtain ⟨r, c⟩ := p.good m' fun _ _ => rfl
      refine ⟨p.storage, p.transient, fun x hx => ?_, ?_, fun c' hc => ?_⟩
      · exact (p.frame x (by omega) (by omega)).trans (mstore_outside _ a _ _ (by omega))
      · rw [Shrink.Geometry.read, hdat, hlen, r]
        rfl
      · rw [Shrink.Geometry.cells, hdat, hlen] at hc
        rcases hc with hc | hc
        · cases c' with
          | slot r s b => exact hc.elim
          | mem y =>
            have hy : a ≤ y ∧ y < a + 32 := hc
            exact ⟨y, rfl, hy.1, by omega⟩
        · obtain ⟨y, rfl, hy⟩ := c c' hc
          exact ⟨y, rfl, by omega⟩
    | _ => simp only [Shrink.Layout.Fits] at hf
  | mapping v =>
    cases t with
    | keyed g => simp only [allocAt, put, reduceCtorEq] at h
    | _ => simp only [Shrink.Layout.Fits] at hf
  | _ =>
    simp only [allocAt] at h
    simp only [allocSize] at hk ⊢
    have p := put_spec P t _ a _ m m' hf (Nat.le_refl _) (by omega) h
    obtain ⟨r, c⟩ := p.good m' fun _ _ => rfl
    refine ⟨p.storage, p.transient, fun x hx => p.frame x (by omega) (by omega), r,
      fun c' hc => ?_⟩
    obtain ⟨y, rfl, hy⟩ := c c' hc
    exact ⟨y, rfl, by omega⟩

/-- A fitting mapping-free root object is written at every address. -/
private theorem allocAt_total (P : Shrink.Params) (L : Shrink.Layout) (t : Shrink.Tree) (a : Nat)
    (m : Shrink.Phys) (hn : L.NoMapping) (hf : L.Fits t) : ∃ m', allocAt P L a t m = some m' := by
  cases L with
  | bytes =>
    cases t with
    | blob bs =>
      rw [Shrink.Layout.Fits] at hf
      refine ⟨m.withMemory (bytesObjectView bs hf m.memory a), ?_⟩
      simp only [allocAt, Shrink.Geometry.write, geometry, ↓reduceIte, dif_pos hf]
    | _ => simp only [Shrink.Layout.Fits] at hf
  | dynArray e =>
    cases t with
    | node xs =>
      rw [Shrink.Layout.Fits] at hf
      simp only [Shrink.Layout.NoMapping] at hn
      simp only [allocAt, if_pos hf.1]
      exact putElems_total P xs e _ 0 _ _ hn hf.2 rfl
    | _ => simp only [Shrink.Layout.Fits] at hf
  | mapping v => simp only [Shrink.Layout.NoMapping] at hn
  | _ =>
    simp only [allocAt]
    exact put_total P t _ _ _ _ hn hf rfl

/-- An allocation takes at most 64 bytes per unit of weight. -/
private theorem allocSize_le (L : Shrink.Layout) (t : Shrink.Tree) (hn : L.NoMapping)
    (hf : L.Fits t) : allocSize L t ≤ 64 * t.weight := by
  have s := size_le t L hn hf
  cases L with
  | dynArray e =>
    simp only [memSize] at s
    simp only [allocSize]
    omega
  | bytes =>
    simp only [memSize] at s
    simp only [allocSize]
    omega
  | _ => exact s

/-! ## The allocation laws -/

/-- **Read after allocation** (`LayoutView.Laws.alloc_read` at `view`): the
tree is readable at the returned address, the old free pointer; its footprint
lies between the old and the new free pointer; slots and the memory below the
old free pointer, outside the free-pointer word, are kept. -/
theorem alloc_read (P : Shrink.Params) (L : Shrink.Layout) (t : Shrink.Tree) (m : Shrink.Phys)
    (a : Nat) (m' : Shrink.Phys) (hf : L.Fits t) (h : view.alloc P L t m = some (a, m')) :
    view.geometry.read P L ⟨.memory, a, 0⟩ m' = some t ∧ m.free ≤ a ∧
      (∀ c, view.geometry.cells P L ⟨.memory, a, 0⟩ m' c →
        ∃ x, c = .mem x ∧ m.free ≤ x ∧ x < m'.free) ∧
      m'.storage = m.storage ∧ m'.transient = m.transient ∧
      (∀ x, x < m.free → (x < 64 ∨ 96 ≤ x) → m'.memory x = m.memory x) := by
  change alloc P L t m = some (a, m') at h
  rw [alloc] at h
  split at h
  · rename_i hc
    obtain ⟨m₁, hw, he⟩ := map_some h
    cases he
    obtain ⟨hs, ht, frame, read, cells⟩ := allocAt_spec P L t m.free _ m' hf hc.2 hw
    have free : m'.free = m.free + allocSize L t :=
      (mloadNat_agree m'.memory _ 64 fun y hy => frame y (by omega)).trans
        (mloadNat_mstore m.memory 64 _ hc.2)
    refine ⟨read, Nat.le_refl _, fun c hcell => ?_, hs, ht, fun x hx hx' => ?_⟩
    · obtain ⟨y, rfl, hy⟩ := cells c hcell
      exact ⟨y, rfl, hy.1, by rw [free]; exact hy.2⟩
    · exact (frame x (by omega)).trans (mstore_outside _ 64 _ _ (by omega))
  · cases h

/-- **Allocation succeeds** (`LayoutView.Laws.alloc_total` at `view`) for a
fitting mapping-free tree from a free pointer past the reserved words, when
64 bytes per unit of weight fit below `2 ^ 256`. -/
theorem alloc_total (P : Shrink.Params) (L : Shrink.Layout) (t : Shrink.Tree) (m : Shrink.Phys)
    (hn : L.NoMapping) (hf : L.Fits t) (start : 128 ≤ m.free)
    (room : m.free + 64 * t.weight < 2 ^ 256) : ∃ a m', view.alloc P L t m = some (a, m') := by
  have size := allocSize_le L t hn hf
  obtain ⟨m', h⟩ := allocAt_total P L t m.free
    (m.withMemory (mstore m.memory 64 (Shrink.toWord (m.free + allocSize L t)))) hn hf
  refine ⟨m.free, m', ?_⟩
  change alloc P L t m = some (m.free, m')
  rw [alloc, if_pos ⟨start, by omega⟩, h]
  rfl

end Solidity.Yul.Layout
