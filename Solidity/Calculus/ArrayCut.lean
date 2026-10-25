import Solidity.Calculus.OrLift
import Solidity.Calculus.QuotientCut

/-!
# Array reads cut to fresh atoms (M7, step 6)

An eliminated leaf reads a storage array of primitives at a root through
three observations of its starting storage: the word at `a[i]`
(`obsW`), whether a slot is there (`obsH`), and the live length (`obsL`).
The arithmetic stages read none of them (`TSegs.guardFuel?` refuses an
array step, and the realization layer builds no array).  `LTm.aCut?`
replaces the `j`-th such read by fresh atoms: the read's index `x_j` and
its value `v_j` (`seq i (v_j)`, so the read still halts where its index
does), and `LFml.aCut?` puts in front, as an antecedent, what an actual
array makes of them (`ARead.cons`):

* the index atom is the index where it returns (`i = i → i = x_j`);
* reads at equal indices read one word; all lengths of a root agree;
* a slot is there below the live length, and below a slot that is there;
* past a slot that is not there every word is the default;
* a fixed array of length `n` has exactly the slots below `n`.

The cut is exact in a universal reading (`LFml.aCut_valid_iff`): the
actual observations satisfy the antecedent (`ARead.fill`), and from atoms
that satisfy it an actual storage is rebuilt (`ARead.realize`): each
array root replaced by the array whose live length is the length atom,
whose slots run up to the last index that the atoms say is there or holds
a word other than the default, each slot holding the word its reads give
it.  A countermodel of the cut leaf is so a countermodel of the leaf, in
the rebuilt state (`LFml.aCut_refutes`).

The index of a cut read must read no array root itself (`LTm.aFree`), so
the atoms' values never depend on one another; every other occurrence of
an array root refuses the cut.
-/

namespace Solidity.Decide

open Semantics

variable {C : Contract}

/-! ## Array roots -/

/-- A state variable that is an array of primitives: dynamic, or fixed of a
length that is a word. -/
def _root_.Solidity.Contract.isArrRoot (C : Contract) (a : Name) : Bool :=
  match C.rootType a with
  | some (.ref (.array (.prim _))) => true
  | some (.ref (.fixed (.prim _) n)) => decide (n < 2 ^ 256)
  | _ => false

/-- A fixed array's length. -/
def _root_.Solidity.ArrTy.fixedLen? {R : RefTy} {E : Ty} : ArrTy R E → Option Nat
  | .dyn => none
  | @ArrTy.fixed _ n => some n

/-! ## Reads of an array root -/

/-- Evidence that a path is an element of an array root of primitives. -/
structure ElemPath {T : Ty} (q : LTm C (.path T)) where
  root : Name
  R : RefTy
  h : C.rootType root = some (.ref R)
  harr : C.isArrRoot root = true
  ar : ArrTy R T
  e : PrimTy
  he : T = .prim e
  i : LTm C (.val .uint)
  eq : q = .index (.arr ar) (.app0 (.root root h)) i

/-- Evidence that a path is an array root of primitives. -/
structure RootPath {E : Ty} (q : LTm C (.path (.ref (.array E)))) where
  root : Name
  h : C.rootType root = some (.ref (.array E))
  harr : C.isArrRoot root = true
  e : PrimTy
  he : E = .prim e
  eq : q = .app0 (.root root h)

def elemOp? {R : RefTy} {T : Ty} (ar : ArrTy R T) (o : Op0 C (.path (.ref R)))
    (i : LTm C (.val .uint)) : Option (ElemPath (LTm.index (.arr ar) (.app0 o) i)) :=
  match o with
  | .root a h =>
    if hA : C.isArrRoot a then
      match T, ar with
      | .prim e, ar => some ⟨a, R, h, hA, ar, e, rfl, i, rfl⟩
      | _, _ => none
    else none

def elemRoot? {R : RefTy} {T : Ty} (ar : ArrTy R T) (r : LTm C (.path (.ref R)))
    (i : LTm C (.val .uint)) : Option (ElemPath (LTm.index (.arr ar) r i)) :=
  match r with
  | .app0 o => elemOp? ar o i
  | _ => none

def elemIdx? {R : RefTy} {k : PrimTy} {T : Ty} (it : IndexTy R k T) (r : LTm C (.path (.ref R)))
    (i : LTm C (.val k)) : Option (ElemPath (LTm.index it r i)) :=
  match R, k, it, r, i with
  | _, _, .arr ar, r, i => elemRoot? ar r i
  | _, _, .map, _, _ => none

/-- An element of an array root, recognized with its evidence. -/
def LTm.elemPath? {T : Ty} (q : LTm C (.path T)) : Option (ElemPath q) :=
  match q with
  | .index it r i => elemIdx? it r i
  | _ => none

def rootOp? {E : Ty} (o : Op0 C (.path (.ref (.array E)))) : Option (RootPath (LTm.app0 o)) :=
  match o with
  | .root a h =>
    if hA : C.isArrRoot a then
      match E with
      | .prim e => some ⟨a, h, hA, e, rfl, rfl⟩
      | _ => none
    else none

/-- A dynamic array root, recognized with its evidence. -/
def LTm.rootPath? {E : Ty} (q : LTm C (.path (.ref (.array E)))) : Option (RootPath q) :=
  match q with
  | .app0 o => rootOp? o
  | _ => none

/-! ## Terms that read no array root -/

def _root_.Solidity.Op0.aFree {s : Srt} : Op0 C s → Bool
  | .lit _ | .env _ | .zlit _ => true
  | .root r _ => !C.isArrRoot r
  | _ => false

def _root_.Solidity.Op1.aFree {a s : Srt} : Op1 C a s → Bool
  | .unop .. | .delValue | .field _ | .toInt => true
  | _ => false

def _root_.Solidity.Op2.aFree {a b s : Srt} : Op2 C a b s → Bool
  | .binop .. | .zbin .. | .zcmp .. => true
  | _ => false

def _root_.Solidity.Op3.aFree {a b c s : Srt} : Op3 C a b c s → Bool
  | .ite | .modular _ => true
  | _ => false

/-- **A term that reads no array root**, over the symbols that read no
storage but through an observation. -/
def LTm.aFree : {s : Srt} → LTm C s → Bool
  | _, .var _ | _, .err => true
  | _, .app0 o => o.aFree
  | _, .app1 o a => o.aFree && a.aFree
  | _, .app2 o a b => o.aFree && a.aFree && b.aFree
  | _, .app3 o a b c => o.aFree && a.aFree && b.aFree && c.aFree
  | _, .index _ a b | _, .seq a b | _, .orElse a b => a.aFree && b.aFree
  | _, .obsW a | _, .obsL a | _, .obsH a => a.aFree
  | _, .kite a b t e => a.aFree && b.aFree && t.aFree && e.aFree

/-! ## The cut -/

/-- What a cut read observes. -/
inductive AKind where
  | word | has | len
  deriving DecidableEq

/-- **A cut read**: the root, its type, the element type, what it observes
and at which index (the literal `0` for a length).  The `j`-th read of a
cut from `N` has its index atom at `N + 2j` and its value atom at
`N + 2j + 1`. -/
structure ARead (C : Contract) where
  root : Name
  R : RefTy
  h : C.rootType root = some (.ref R)
  harr : C.isArrRoot root = true
  e : PrimTy
  ar : ArrTy R (.prim e)
  kind : AKind
  idx : LTm C (.val .uint)

/-- The index atom of the `j`-th read. -/
abbrev xAt (N j : Nat) : LTm C (.val .uint) := .var (N + 2 * j)

/-- The value atom of the `j`-th read. -/
abbrev vAt (p : PrimTy) (N j : Nat) : LTm C (.val p) := .var (N + 2 * j + 1)

/-- The first read of `rs` of one root, kind and index term, by term
identity: a read made twice gets one pair of atoms. -/
def findRead (rs : List (ARead C)) (a : Name) (k : AKind) (i : LTm C (.val .uint)) : Option Nat :=
  rs.findIdx? fun r => r.root == a && r.kind == k && r.idx.beqR i

/-- **The cut of a term**, its reads numbered after `rs`: the term and the
reads; `none` where an array root is read otherwise, or a symbol reads
storage but through an observation. -/
def LTm.aCut? (N : Nat) : {s : Srt} → LTm C s → List (ARead C) → Option (LTm C s × List (ARead C))
  | _, .var k, rs => some (.var k, rs)
  | _, .err, rs => some (.err, rs)
  | _, .app0 o, rs => if o.aFree then some (.app0 o, rs) else none
  | _, .app1 o a, rs =>
    if o.aFree then (a.aCut? N rs).map fun (a', rs) => (.app1 o a', rs) else none
  | _, .app2 o a b, rs =>
    if o.aFree then (a.aCut? N rs).bind fun (a', rs) => (b.aCut? N rs).map fun (b', rs) =>
      (.app2 o a' b', rs) else none
  | _, .app3 o a b c, rs =>
    if o.aFree then (a.aCut? N rs).bind fun (a', rs) => (b.aCut? N rs).bind fun (b', rs) =>
      (c.aCut? N rs).map fun (c', rs) => (.app3 o a' b' c', rs) else none
  | _, .index it a b, rs => if a.aFree && b.aFree then some (.index it a b, rs) else none
  | _, .seq a b, rs => (a.aCut? N rs).bind fun (a', rs) => (b.aCut? N rs).map fun (b', rs) =>
      (.seq a' b', rs)
  | _, .orElse a b, rs => (a.aCut? N rs).bind fun (a', rs) => (b.aCut? N rs).map fun (b', rs) =>
      (.orElse a' b', rs)
  | _, .kite a b t e, rs =>
    (a.aCut? N rs).bind fun (a', rs) => (b.aCut? N rs).bind fun (b', rs) =>
      (t.aCut? N rs).bind fun (t', rs) => (e.aCut? N rs).map fun (e', rs) => (.kite a' b' t' e', rs)
  | _, .obsW q, rs =>
    match q.elemPath? with
    | some ep =>
      if ep.i.aFree then
        match findRead rs ep.root .word ep.i with
        | some j => some (.seq ep.i (.var (N + 2 * j + 1)), rs)
        | none => some (.seq ep.i (.var (N + 2 * rs.length + 1)),
            rs ++ [⟨ep.root, ep.R, ep.h, ep.harr, ep.e, ep.he ▸ ep.ar, .word, ep.i⟩])
      else none
    | none => if q.aFree then some (.obsW q, rs) else none
  | _, .obsH q, rs =>
    match q.elemPath? with
    | some ep =>
      if ep.i.aFree then
        match findRead rs ep.root .has ep.i with
        | some j => some (.seq ep.i (.var (N + 2 * j + 1)), rs)
        | none => some (.seq ep.i (.var (N + 2 * rs.length + 1)),
            rs ++ [⟨ep.root, ep.R, ep.h, ep.harr, ep.e, ep.he ▸ ep.ar, .has, ep.i⟩])
      else none
    | none => if q.aFree then some (.obsH q, rs) else none
  | _, .obsL q, rs =>
    match q.rootPath? with
    | some rp =>
      match findRead rs rp.root .len (.app0 (.lit (PrimTy.dflt .uint))) with
      | some j => some (.var (N + 2 * j + 1), rs)
      | none => some (.var (N + 2 * rs.length + 1),
          rs ++ [⟨rp.root, .array (.prim rp.e), rp.he ▸ rp.h, rp.harr, rp.e, .dyn, .len,
            .app0 (.lit (PrimTy.dflt .uint))⟩])
    | none => if q.aFree then some (.obsL q, rs) else none

/-- The cut of a formula. -/
def LFml.aCutF? (N : Nat) : LFml C → List (ARead C) → Option (LFml C × List (ARead C))
  | .tt, rs => some (.tt, rs)
  | .eq a b, rs => (a.aCut? N rs).bind fun (a', rs) => (b.aCut? N rs).map fun (b', rs) =>
      (.eq a' b', rs)
  | .not φ, rs => (φ.aCutF? N rs).map fun (φ', rs) => (.not φ', rs)
  | .and φ ψ, rs => (φ.aCutF? N rs).bind fun (φ', rs) => (ψ.aCutF? N rs).map fun (ψ', rs) =>
      (.and φ' ψ', rs)
  | .imp φ ψ, rs => (φ.aCutF? N rs).bind fun (φ', rs) => (ψ.aCutF? N rs).map fun (ψ', rs) =>
      (.imp φ' ψ', rs)
  | .all .., _ => none

/-! ## What an actual array makes of the atoms -/

/-- `t = true`. -/
abbrev LFml.isT (t : LTm C (.val .bool)) : LFml C := .eq t .tt
/-- `t = false`. -/
abbrev LFml.isF (t : LTm C (.val .bool)) : LFml C := .eq t (.app0 (.lit false))

/-- `a < b` on words. -/
abbrev LTm.ltU (a b : LTm C (.val .uint)) : LTm C (.val .bool) := .app2 (.binop .lt rfl) a b
/-- `a <= b` on words. -/
abbrev LTm.leU (a b : LTm C (.val .uint)) : LTm C (.val .bool) := .app2 (.binop .le rfl) a b

/-- The value atoms of two reads of one root agree, at the element type of
the first. -/
def eqVal (N j k : Nat) (p : PrimTy) : LFml C := .eq (vAt p N j) (vAt p N k)

/-- What one read makes of itself: its index atom the index; at a fixed
array, a slot past the length reads the default and is not there. -/
def ARead.self (N j : Nat) (r : ARead C) : List (LFml C) :=
  let x := xAt (C := C) N j
  match r.kind with
  | .len => []
  | .word =>
    [.imp (.eq r.idx r.idx) (.eq r.idx x)] ++
      match r.ar.fixedLen? with
      | some n => [.imp (LFml.isF (LTm.ltU x (.app0 (.lit (uintOfNat n)))))
          (.eq (vAt r.e N j) (LTm.dfltLit r.e))]
      | none => []
  | .has =>
    [.imp (.eq r.idx r.idx) (.eq r.idx x)] ++
      match r.ar.fixedLen? with
      | some n => [.eq (vAt .bool N j) (LTm.ltU x (.app0 (.lit (uintOfNat n))))]
      | none => []

/-- What two reads of one root make of each other (`j` the first, `k` the
second). -/
def ARead.pair (N j k : Nat) (r s : ARead C) : List (LFml C) :=
  if r.root = s.root then
    match r.kind, s.kind with
    | .word, .word => [.imp (.eq (xAt N j) (xAt N k)) (eqVal N j k r.e)]
    | .len, .len => [eqVal N j k .uint]
    | .has, .has =>
      [.imp (LFml.isT (vAt .bool N j)) (.imp (LFml.isT (LTm.leU (xAt N k) (xAt N j)))
        (LFml.isT (vAt .bool N k)))]
    | .has, .len =>
      [.imp (LFml.isT (LTm.ltU (xAt N j) (vAt .uint N k))) (LFml.isT (vAt .bool N j))]
    | .has, .word =>
      [.imp (LFml.isF (vAt .bool N j)) (.imp (LFml.isT (LTm.leU (xAt N j) (xAt N k)))
        (.eq (vAt s.e N k) (LTm.dfltLit s.e)))]
    | _, _ => []
  else []

/-- **What actual arrays make of the reads' atoms.** -/
def ARead.cons (N : Nat) (rs : List (ARead C)) : LFml C :=
  LFml.conj ((List.range rs.length).flatMap fun j =>
    match rs[j]? with
    | none => []
    | some r => r.self N j ++ (List.range rs.length).flatMap fun k =>
      match rs[k]? with
      | none => []
      | some s => if j = k then [] else r.pair N j k s)

/-- **The cut of a leaf's body**: its reads of array roots cut to atoms from
`N` on, what actual arrays make of them in front. -/
def LFml.aCut? (N : Nat) (φ : LFml C) : Option (LFml C × List (ARead C)) :=
  (φ.aCutF? N []).map fun (φ', rs) => (.imp (ARead.cons N rs) φ', rs)

/-! ## What the atoms describe -/

/-- A length read described: the live length of the dynamic array at the
root (a fixed array has no length read). -/
def lenDesc {R : RefTy} {e : PrimTy} (a : Name) (h : C.rootType a = some (.ref R))
    (ar : ArrTy R (.prim e)) (st : Storage C) (v : PrimTy.uint.Denote) : Prop :=
  match R, h, ar with
  | _, h, .dyn => v = uintOfNat (st.obs.len (.ref (SRef.ofRoot a h)))
  | _, _, .fixed => True

/-- The location of a read at an index. -/
abbrev ARead.loc (r : ARead C) (k : PrimTy.uint.Denote) : SRef C (.prim r.e) :=
  (SRef.ofRoot r.root r.h).index (.arr r.ar) k

/-- The state `g` with the storage `st`. -/
abbrev State.withStorage (g : State C []) (st : Storage C) : State C [] := { g with storage := st }

/-- **The read `j` described**: its index atom is its index where that
returns, and its value atom what the storage `st` shows there (or the
length). -/
def ARead.Describes (r : ARead C) (g : State C []) (st : Storage C) (ν : AEnv) (N j : Nat) : Prop :=
  match r.kind with
  | .word => ∀ k, (r.idx.eval g ν : Option PrimTy.uint.Denote) = some k →
      ν.u (N + 2 * j) = k ∧ ν.get r.e (N + 2 * j + 1) = st.obs.word (.ref (r.loc k))
  | .has => ∀ k, (r.idx.eval g ν : Option PrimTy.uint.Denote) = some k →
      ν.u (N + 2 * j) = k ∧ ν.b (N + 2 * j + 1) = st.obs.has (.ref (r.loc k))
  | .len => lenDesc r.root r.h r.ar st (ν.u (N + 2 * j + 1))

/-- Every read described. -/
def Describes (g : State C []) (st : Storage C) (ν : AEnv) (N : Nat) (rs : List (ARead C)) : Prop :=
  ∀ j (r : ARead C), rs[j]? = some r → r.Describes g st ν N j

/-- With the storage `st`, every term that reads no array root reads as in
`g`. -/
def Frames (g : State C []) (st : Storage C) (ν : AEnv) : Prop :=
  ∀ {s : Srt} (t : LTm C s), t.aFree = true → t.eval (g.withStorage st) ν = t.eval g ν

theorem ArrTy.subsingleton {R : RefTy} {E : Ty} (a b : ArrTy R E) : a = b := by
  cases a <;> cases b <;> rfl

theorem ArrTy.elem_eq {R : RefTy} {e e' : PrimTy} (a : ArrTy R (.prim e)) (b : ArrTy R (.prim e')) :
    e = e' := by
  cases a <;> cases b <;> rfl

theorem findRead_some {rs : List (ARead C)} {a : Name} {k : AKind} {i : LTm C (.val .uint)}
    {j : Nat} (h : findRead rs a k i = some j) :
    ∃ r, rs[j]? = some r ∧ r.root = a ∧ r.kind = k ∧ r.idx = i := by
  unfold findRead at h
  obtain ⟨hj, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨rs[j], List.getElem?_eq_getElem hj, hp.1.1, hp.1.2, LTm.eq_of_beqR hp.2⟩

theorem getElem?_of_prefix {rs₁ rs : List (ARead C)} (hp : rs₁ <+: rs) {j : Nat} {r : ARead C}
    (h : rs₁[j]? = some r) : rs[j]? = some r := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

/-! ## The cut reads what the term reads -/

/-- The cut only adds reads. -/
theorem LTm.aCut?_prefix {N : Nat} : ∀ {s : Srt} (t : LTm C s) (rs₀ : List (ARead C))
    {t' : LTm C s} {rs₁ : List (ARead C)}, t.aCut? N rs₀ = some (t', rs₁) → rs₀ <+: rs₁ := by
  intro s t
  induction t with
  | var | err =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]; exact List.prefix_refl _
  | app0 o =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
    · cases h
  | index it a b _ _ =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
    · cases h
  | app1 o a iha =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?] at h; split at h
    · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨_, _, h1, -, rfl⟩ := h
      exact iha _ h1
    · cases h
  | app2 o a b iha ihb =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?] at h; split at h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨_, _, h1, _, _, h2, -, rfl⟩ := h
      exact (iha _ h1).trans (ihb _ h2)
    · cases h
  | app3 o a b c iha ihb ihc =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?] at h; split at h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨_, _, h1, _, _, h2, _, _, h3, -, rfl⟩ := h
      exact (iha _ h1).trans ((ihb _ h2).trans (ihc _ h3))
    · cases h
  | seq a b iha ihb | orElse a b iha ihb =>
    intro rs₀ t' rs₁ h
    simp only [LTm.aCut?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨_, _, h1, _, _, h2, -, rfl⟩ := h
    exact (iha _ h1).trans (ihb _ h2)
  | kite a b t e iha ihb iht ihe =>
    intro rs₀ t' rs₁ h
    simp only [LTm.aCut?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨_, _, h1, _, _, h2, _, _, h3, _, _, h4, -, rfl⟩ := h
    exact (iha _ h1).trans ((ihb _ h2).trans ((iht _ h3).trans (ihe _ h4)))
  | obsW q _ | obsH q _ =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?] at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact List.prefix_append _ _
      · cases h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
      · cases h
  | obsL q _ =>
    intro rs₀ t' rs₁ h; simp only [LTm.aCut?] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact List.prefix_append _ _
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
      · cases h

section Eval

variable {g : State C []} {st : Storage C} {ν : AEnv} {N : Nat} {rs : List (ARead C)}

/-- A word read cut to its atoms reads what the storage shows. -/
theorem aCut_obsW (hD : Describes g st ν N rs) (hF : Frames g st ν) {p : PrimTy}
    (q : LTm C (.path (.prim p))) (ep : ElemPath q) (hi : ep.i.aFree = true) (j : Nat) (r : ARead C)
    (hr : rs[j]? = some r) (hroot : r.root = ep.root) (hk : r.kind = .word) (hidx : r.idx = ep.i) :
    ((LTm.seq ep.i (.var (N + 2 * j + 1)) : LTm C (.val p)).eval g ν : Option p.Denote) =
      (LTm.obsW q).eval (g.withStorage st) ν := by
  have hd := hD j r hr
  rcases ep with ⟨a, R, h, _, ar, e, he, i, rfl⟩
  cases he
  rcases r with ⟨a', R', h', _, e', ar', k', i'⟩
  dsimp only at hroot hk hidx hi
  subst hroot hk hidx
  obtain rfl : R' = R := by
    have := h'.symm.trans h; simp only [Option.some.injEq, Ty.ref.injEq] at this; exact this
  obtain rfl : e' = p := ArrTy.elem_eq ar' ar
  obtain rfl : ar' = ar := ArrTy.subsingleton _ _
  have hiF := hF i' hi
  simp only [ARead.Describes] at hd
  show ((i'.eval g ν : Option PrimTy.uint.Denote).bind fun _ => some (ν.get e' (N + 2 * j + 1))) = _
  rw [LTm.eval_obsW, LTm.eval_index, LTm.eval_app0, hiF]
  cases hk : (i'.eval g ν : Option PrimTy.uint.Denote) with
  | none => rfl
  | some k =>
    obtain ⟨-, hv⟩ := hd k hk
    simp only [Option.bind_some]
    exact congrArg some hv

/-- A slot test cut to its atoms reads what the storage shows. -/
theorem aCut_obsH (hD : Describes g st ν N rs) (hF : Frames g st ν) {T : Ty}
    (q : LTm C (.path T)) (ep : ElemPath q) (hi : ep.i.aFree = true) (j : Nat) (r : ARead C)
    (hr : rs[j]? = some r) (hroot : r.root = ep.root) (hk : r.kind = .has) (hidx : r.idx = ep.i) :
    ((LTm.seq ep.i (.var (N + 2 * j + 1)) : LTm C (.val .bool)).eval g ν : Option Bool) =
      (LTm.obsH q).eval (g.withStorage st) ν := by
  have hd := hD j r hr
  rcases ep with ⟨a, R, h, _, ar, e, he, i, rfl⟩
  subst he
  rcases r with ⟨a', R', h', _, e', ar', k', i'⟩
  dsimp only at hroot hk hidx hi
  subst hroot hk hidx
  obtain rfl : R' = R := by
    have := h'.symm.trans h; simp only [Option.some.injEq, Ty.ref.injEq] at this; exact this
  obtain rfl : e' = e := ArrTy.elem_eq ar' ar
  obtain rfl : ar' = ar := ArrTy.subsingleton _ _
  have hiF := hF i' hi
  simp only [ARead.Describes] at hd
  show ((i'.eval g ν : Option PrimTy.uint.Denote).bind fun _ => some (ν.b (N + 2 * j + 1))) = _
  rw [LTm.eval_obsH, LTm.eval_index, LTm.eval_app0, hiF]
  cases hk : (i'.eval g ν : Option PrimTy.uint.Denote) with
  | none => rfl
  | some k =>
    obtain ⟨-, hv⟩ := hd k hk
    simp only [Option.bind_some]
    exact congrArg some hv

/-- A length cut to its atom reads what the storage shows. -/
theorem aCut_obsL (hD : Describes g st ν N rs) {E : Ty}
    (q : LTm C (.path (.ref (.array E)))) (rp : RootPath q) (j : Nat) (r : ARead C)
    (hr : rs[j]? = some r) (hroot : r.root = rp.root) (hk : r.kind = .len) :
    ((LTm.var (N + 2 * j + 1) : LTm C (.val .uint)).eval g ν : Option PrimTy.uint.Denote) =
      (LTm.obsL q).eval (g.withStorage st) ν := by
  have hd := hD j r hr
  rcases rp with ⟨a, h, _, e, he, rfl⟩
  subst he
  rcases r with ⟨a', R', h', _, e', ar', k', i'⟩
  dsimp only at hroot hk
  subst hroot hk
  obtain rfl : R' = .array (.prim e) := by
    have := h'.symm.trans h; simp only [Option.some.injEq, Ty.ref.injEq] at this; exact this
  cases ar'
  simp only [ARead.Describes, lenDesc] at hd
  rw [LTm.eval_obsL, LTm.eval_app0]
  exact congrArg some hd

theorem Op1.eval_aFree {a s : Srt} (o : Op1 C a s) (h : o.aFree = true) (x : Option (a.Den C g.H)) :
    o.eval (g.withStorage st) x = o.eval g x := by
  cases o <;> first | rfl | simp only [Op1.aFree, Bool.false_eq_true] at h

theorem Op2.eval_aFree {a b s : Srt} (o : Op2 C a b s) (h : o.aFree = true)
    (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H)) :
    o.eval (g.withStorage st) x y = o.eval g x y := by
  cases o <;> first | rfl | simp only [Op2.aFree, Bool.false_eq_true] at h

theorem Op3.eval_aFree {a b c s : Srt} (o : Op3 C a b c s) (h : o.aFree = true)
    (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H)) (z : Option (c.Den C g.H)) :
    o.eval (g.withStorage st) x y z = o.eval g x y z := by
  cases o <;> first | rfl | simp only [Op3.aFree, Bool.false_eq_true] at h

/-- **A cut term reads in `g`, at atoms that describe its reads in `st`,
what the term reads with the storage `st`.** -/
theorem LTm.aCut_eval (hD : Describes g st ν N rs) (hF : Frames g st ν) :
    ∀ {s : Srt} (t : LTm C s) (rs₀ : List (ARead C)) {t' : LTm C s} {rs₁ : List (ARead C)},
      t.aCut? N rs₀ = some (t', rs₁) → rs₁ <+: rs → t'.eval g ν = t.eval (g.withStorage st) ν := by
  intro s t
  induction t with
  | var | err =>
    intro rs₀ t' rs₁ h _; simp only [LTm.aCut?, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | app0 o =>
    intro rs₀ t' rs₁ h _; simp only [LTm.aCut?] at h; split at h
    · rename_i ho
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
      exact (hF (LTm.app0 o) ho).symm
    · cases h
  | index it a b _ _ =>
    intro rs₀ t' rs₁ h _; simp only [LTm.aCut?] at h; split at h
    · rename_i ho
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
      exact (hF (LTm.index it a b) ho).symm
    · cases h
  | app1 o a iha =>
    intro rs₀ t' rs₁ h hp; simp only [LTm.aCut?] at h; split at h
    · rename_i ho
      simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨a', _, h1, rfl, rfl⟩ := h
      rw [LTm.eval_app1, LTm.eval_app1, iha _ h1 hp, Op1.eval_aFree o ho]
    · cases h
  | app2 o a b iha ihb =>
    intro rs₀ t' rs₁ h hp; simp only [LTm.aCut?] at h; split at h
    · rename_i ho
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨a', rsA, h1, b', _, h2, rfl, rfl⟩ := h
      rw [LTm.eval_app2, LTm.eval_app2, iha _ h1 ((LTm.aCut?_prefix b _ h2).trans hp),
        ihb _ h2 hp, Op2.eval_aFree o ho]
    · cases h
  | app3 o a b c iha ihb ihc =>
    intro rs₀ t' rs₁ h hp; simp only [LTm.aCut?] at h; split at h
    · rename_i ho
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨a', rsA, h1, b', rsB, h2, c', _, h3, rfl, rfl⟩ := h
      have hpB := (LTm.aCut?_prefix c _ h3).trans hp
      rw [LTm.eval_app3, LTm.eval_app3, iha _ h1 ((LTm.aCut?_prefix b _ h2).trans hpB),
        ihb _ h2 hpB, ihc _ h3 hp, Op3.eval_aFree o ho]
    · cases h
  | seq a b iha ihb =>
    intro rs₀ t' rs₁ h hp
    simp only [LTm.aCut?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨a', rsA, h1, b', _, h2, rfl, rfl⟩ := h
    rw [LTm.eval_seq, LTm.eval_seq, iha _ h1 ((LTm.aCut?_prefix b _ h2).trans hp), ihb _ h2 hp]
    rfl
  | orElse a b iha ihb =>
    intro rs₀ t' rs₁ h hp
    simp only [LTm.aCut?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨a', rsA, h1, b', _, h2, rfl, rfl⟩ := h
    rw [LTm.eval_orElse, LTm.eval_orElse, iha _ h1 ((LTm.aCut?_prefix b _ h2).trans hp),
      ihb _ h2 hp]
  | kite a b t e iha ihb iht ihe =>
    intro rs₀ t' rs₁ h hp
    simp only [LTm.aCut?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨a', rsA, h1, b', rsB, h2, t'', rsT, h3, e', _, h4, rfl, rfl⟩ := h
    have hpT := (LTm.aCut?_prefix e _ h4).trans hp
    have hpB := (LTm.aCut?_prefix t _ h3).trans hpT
    rw [LTm.eval_kite, LTm.eval_kite, iha _ h1 ((LTm.aCut?_prefix b _ h2).trans hpB),
      ihb _ h2 hpB, iht _ h3 hpT, ihe _ h4 hp]
  | obsW q _ =>
    intro rs₀ t' rs₁ h hp; simp only [LTm.aCut?] at h
    split at h
    · rename_i ep _
      split at h
      · rename_i hi
        split at h
        · rename_i j hj
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨r, hr, hroot, hk, hidx⟩ := findRead_some hj
          exact aCut_obsW hD hF q ep hi j r (getElem?_of_prefix hp hr) hroot hk hidx
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact aCut_obsW hD hF q ep hi _ ⟨ep.root, ep.R, ep.h, ep.harr, ep.e, ep.he ▸ ep.ar, .word, ep.i⟩
            (getElem?_of_prefix hp (by simp only [List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero])) rfl rfl rfl
      · cases h
    · split at h
      · rename_i hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact (hF (LTm.obsW q) hq).symm
      · cases h
  | obsH q _ =>
    intro rs₀ t' rs₁ h hp; simp only [LTm.aCut?] at h
    split at h
    · rename_i ep _
      split at h
      · rename_i hi
        split at h
        · rename_i j hj
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨r, hr, hroot, hk, hidx⟩ := findRead_some hj
          exact aCut_obsH hD hF q ep hi j r (getElem?_of_prefix hp hr) hroot hk hidx
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact aCut_obsH hD hF q ep hi _ ⟨ep.root, ep.R, ep.h, ep.harr, ep.e, ep.he ▸ ep.ar, .has, ep.i⟩
            (getElem?_of_prefix hp (by simp only [List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero])) rfl rfl rfl
      · cases h
    · split at h
      · rename_i hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact (hF (LTm.obsH q) hq).symm
      · cases h
  | obsL q _ =>
    intro rs₀ t' rs₁ h hp; simp only [LTm.aCut?] at h
    split at h
    · rename_i rp _
      split at h
      · rename_i j hj
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨r, hr, hroot, hk, -⟩ := findRead_some hj
        exact aCut_obsL hD q rp j r (getElem?_of_prefix hp hr) hroot hk
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact aCut_obsL hD q rp _ ⟨rp.root, .array (.prim rp.e), rp.he ▸ rp.h, rp.harr, rp.e, .dyn, .len,
            .app0 (.lit (PrimTy.dflt .uint))⟩
          (getElem?_of_prefix hp (by simp only [List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self, List.getElem?_cons_zero])) rfl rfl
    · split at h
      · rename_i hq
        simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact (hF (LTm.obsL q) hq).symm
      · cases h

end Eval

/-- The cut of a formula only adds reads. -/
theorem LFml.aCutF?_prefix {N : Nat} : ∀ (φ : LFml C) (rs₀ : List (ARead C)) {φ' : LFml C}
    {rs₁ : List (ARead C)}, φ.aCutF? N rs₀ = some (φ', rs₁) → rs₀ <+: rs₁
  | .tt, _, _, _, h => by
    simp only [LFml.aCutF?, Option.some.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
  | .eq a b, rs₀, _, _, h => by
    simp only [LFml.aCutF?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨_, _, h1, _, _, h2, -, rfl⟩ := h
    exact (LTm.aCut?_prefix a _ h1).trans (LTm.aCut?_prefix b _ h2)
  | .not φ, rs₀, _, _, h => by
    simp only [LFml.aCutF?, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨_, _, h1, -, rfl⟩ := h
    exact LFml.aCutF?_prefix φ _ h1
  | .and φ ψ, rs₀, _, _, h | .imp φ ψ, rs₀, _, _, h => by
    simp only [LFml.aCutF?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨_, _, h1, _, _, h2, -, rfl⟩ := h
    exact (LFml.aCutF?_prefix φ _ h1).trans (LFml.aCutF?_prefix ψ _ h2)
  | .all .., _, _, _, h => by cases h

/-- **The cut formula holds** in `g`, at atoms that describe its reads in
`st`, where the formula holds with the storage `st`. -/
theorem LFml.aCutF_holds {g : State C []} {st : Storage C} {ν : AEnv} {N : Nat}
    {rs : List (ARead C)} (hD : Describes g st ν N rs) (hF : Frames g st ν) :
    ∀ (φ : LFml C) (rs₀ : List (ARead C)) {φ' : LFml C} {rs₁ : List (ARead C)},
      φ.aCutF? N rs₀ = some (φ', rs₁) → rs₁ <+: rs →
        (φ'.holds g ν ↔ φ.holds (g.withStorage st) ν)
  | .tt, _, _, _, h, _ => by
    simp only [LFml.aCutF?, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact Iff.rfl
  | .eq a b, rs₀, φ', rs₁, h, hp => by
    simp only [LFml.aCutF?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨a', rsA, h1, b', _, h2, rfl, rfl⟩ := h
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff,
      LTm.aCut_eval hD hF a _ h1 ((LTm.aCut?_prefix b _ h2).trans hp), LTm.aCut_eval hD hF b _ h2 hp]
  | .not φ, rs₀, φ', rs₁, h, hp => by
    simp only [LFml.aCutF?, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨φ'', _, h1, rfl, rfl⟩ := h
    exact not_congr (LFml.aCutF_holds hD hF φ _ h1 hp)
  | .and φ ψ, rs₀, φ', rs₁, h, hp => by
    simp only [LFml.aCutF?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨φ'', rsA, h1, ψ', _, h2, rfl, rfl⟩ := h
    exact and_congr (LFml.aCutF_holds hD hF φ _ h1 ((LFml.aCutF?_prefix ψ _ h2).trans hp))
      (LFml.aCutF_holds hD hF ψ _ h2 hp)
  | .imp φ ψ, rs₀, φ', rs₁, h, hp => by
    simp only [LFml.aCutF?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
      Prod.mk.injEq] at h
    obtain ⟨φ'', rsA, h1, ψ', _, h2, rfl, rfl⟩ := h
    exact imp_congr (LFml.aCutF_holds hD hF φ _ h1 ((LFml.aCutF?_prefix ψ _ h2).trans hp))
      (LFml.aCutF_holds hD hF ψ _ h2 hp)
  | .all .., _, _, _, h, _ => by cases h

/-! ## Realization: arrays rebuilt from the atoms -/

/-- Every member `f` of type `T` replaced by `F f T`. -/
def _root_.Solidity.SFields.mapF (F : (f : Name) → (T : Ty) → SVal T → SVal T) :
    {fs : List (Name × Ty)} → SFields fs → SFields fs
  | [], .nil => .nil
  | (f, T) :: _, .cons v rest => .cons (F f T v) (SFields.mapF F rest)

theorem _root_.Solidity.SFields.get_mapF (F : (f : Name) → (T : Ty) → SVal T → SVal T) {f : Name} :
    {fs : List (Name × Ty)} → {T : Ty} → (x : SFields fs) → (h : lookupBy f fs = some T) →
      (x.mapF F).get h = F f T (x.get h)
  | [], _, .nil, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h => by
    show (SFields.cons (F f' T' v) (rest.mapF F)).get h = _
    rw [SFields.get_cons, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT e
      simp only [dite_true]
    · simp only [e, dite_false]
      exact SFields.get_mapF F rest _

/-- `n` values, the `t`-th `f t`. -/
def vecOf {E : Ty} (f : Nat → SVal E) : (n : Nat) → SVec E n
  | 0 => .nil
  | n + 1 => .cons (f 0) (vecOf (fun t => f (t + 1)) n)

theorem vecOf_toList {E : Ty} : ∀ (f : Nat → SVal E) (n : Nat),
    (vecOf f n).toList = (List.range n).map f
  | _, 0 => by rw [vecOf, SVec.toList_nil]; rfl
  | f, n + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show (SVec.cons (f 0) (vecOf (fun t => f (t + 1)) n)).toList = _
    rw [SVec.toList_cons, vecOf_toList]
    rfl

section Realize

variable (ν : AEnv) (N : Nat) (rs : List (ARead C))

/-- The index atom of the `j`-th read, as a number. -/
def idxV (j : Nat) : Nat := (ν.u (N + 2 * j)).1.toNat

/-- The `j`-th read reads the root `a` and observes `k`. -/
def isRd (a : Name) (k : AKind) (j : Nat) : Bool :=
  match rs[j]? with
  | some r => r.root == a && r.kind == k
  | none => false

/-- The live length the atoms give the root `a`: its first length read's. -/
def lenOf (a : Name) : Nat :=
  match (List.range rs.length).find? (isRd rs a .len) with
  | some j => (ν.u (N + 2 * j + 1)).1.toNat
  | none => 0

/-- The word the atoms give the slot `t` of the root `a`: its first word
read's there. -/
def wordAt (a : Name) (e : PrimTy) (t : Nat) : e.Denote :=
  match (List.range rs.length).find? (fun j => isRd rs a .word j && idxV ν N j == t) with
  | some j => ν.get e (N + 2 * j + 1)
  | none => PrimTy.dflt e

/-- The slots the `j`-th read asks to be there. -/
def bump (a : Name) (e : PrimTy) (j : Nat) : Nat :=
  if (isRd rs a .has j && ν.b (N + 2 * j + 1)) ||
      (isRd rs a .word j && !decide (ν.get e (N + 2 * j + 1) = PrimTy.dflt e)) then
    idxV ν N j + 1
  else 0

/-- The slots of the rebuilt root `a`: past the live length, past every
slot the atoms say is there or hold a word other than the default. -/
def slotsOf (a : Name) (e : PrimTy) : Nat :=
  (List.range rs.length).foldl (fun m j => max m (bump ν N rs a e j)) (lenOf ν N rs a)

/-- The array of the root `a`, rebuilt from the atoms. -/
def arrVal (a : Name) : (T : Ty) → SVal T → SVal T
  | .ref (.array (.prim e)), v =>
    if hL : lenOf ν N rs a < 2 ^ 256 then
      .array (vecOf (fun t => .prim (wordAt ν N rs a e t)) (lenOf ν N rs a))
        (SList.ofList ((List.range (slotsOf ν N rs a e - lenOf ν N rs a)).map
          fun t => .prim (wordAt ν N rs a e (lenOf ν N rs a + t)))) hL
    else v
  | .ref (.fixed (.prim e) n), _ => .fixed (vecOf (fun t => .prim (wordAt ν N rs a e t)) n)
  | _, v => v

/-- **The storage rebuilt from the atoms**: every array root replaced. -/
def realizeSt (st : Storage C) : Storage C :=
  SFields.mapF (fun a T v => if C.isArrRoot a then arrVal ν N rs a T v else v) st

/-- The state rebuilt from the atoms. -/
def realize (g : State C []) : State C [] := g.withStorage (realizeSt ν N rs g.storage)

end Realize

section Frame

variable (ν : AEnv) (N : Nat) (rs : List (ARead C))

theorem realizeSt_get_ne (st : Storage C) {a : Name} {T : Ty} (h : C.rootType a = some T)
    (ha : C.isArrRoot a = false) : (realizeSt ν N rs st).get h = st.get h := by
  unfold realizeSt
  rw [SFields.get_mapF]
  simp only [ha, Bool.false_eq_true, if_false]

/-- A path that reads no array root names no location below one. -/
def RootsOK (H : HTy) : (s : Srt) → Option (s.Den C H) → Prop
  | .path _, x => ∀ r, x = some r → C.isArrRoot r.root = false
  | _, _ => True

theorem LTm.aFree_roots (g : State C []) (ν : AEnv) :
    ∀ {s : Srt} (t : LTm C s), t.aFree = true → RootsOK g.H s (t.eval g ν) := by
  intro s t
  induction t with
  | var => intro _; trivial
  | @err s =>
    intro _
    cases s with
    | path T => intro r h; cases h
    | _ => trivial
  | app0 o =>
    intro h
    cases o with
    | root a ha =>
      intro r hr
      simp only [LTm.aFree, Op0.aFree, Bool.not_eq_true'] at h
      cases hr
      exact h
    | _ => trivial
  | app1 o a iha =>
    intro h
    simp only [LTm.aFree, Bool.and_eq_true] at h
    cases o with
    | field hf =>
      intro r hr
      have ih := iha h.2
      rw [LTm.eval_app1] at hr
      change (a.eval g ν : Option (SRef C _)).map (·.field hf) = some r at hr
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hr
      exact ih r' hr'
    | _ => first | trivial | simp only [Op1.aFree, Bool.false_eq_true, false_and] at h
  | app2 o a b => intro h; cases o <;> first | trivial | simp only [LTm.aFree, Op2.aFree,
      Bool.false_eq_true, Bool.false_and, false_and] at h
  | app3 o a b c => intro h; cases o <;> first | trivial | simp only [LTm.aFree, Op3.aFree,
      Bool.false_eq_true, Bool.false_and, false_and] at h
  | index it q i ihq _ =>
    intro h r hr
    simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_index] at hr
    obtain ⟨r', hr', hr''⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.mp hr''
    cases hk
    exact ihq h.1 r' hr'
  | obsW | obsL | obsH => intro _; trivial
  | @seq s' s d a _ iha =>
    intro h
    simp only [LTm.aFree, Bool.and_eq_true] at h
    cases s with
    | path T =>
      intro r hr
      rw [LTm.eval_seq] at hr
      obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
      exact iha h.2 r hr
    | _ => trivial
  | @orElse s a b iha ihb =>
    intro h
    simp only [LTm.aFree, Bool.and_eq_true] at h
    cases s with
    | path T =>
      intro r hr
      rw [LTm.eval_orElse] at hr
      cases ha : (a.eval g ν : Option (SRef C T)) with
      | none => rw [ha] at hr; exact ihb h.2 r hr
      | some r' => rw [ha] at hr; cases hr; exact iha h.1 _ ha
    | _ => trivial
  | @kite p s a b t e _ _ iht ihe =>
    intro h
    simp only [LTm.aFree, Bool.and_eq_true] at h
    cases s with
    | path T =>
      intro r hr
      rw [LTm.eval_kite] at hr
      obtain ⟨x, -, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨y, -, hr⟩ := Option.bind_eq_some_iff.mp hr
      split at hr
      · exact iht h.1.2 r hr
      · exact ihe h.2 r hr
    | _ => trivial

/-- **The rebuilt storage frames every term that reads no array root.** -/
theorem frames_realize (g : State C []) : Frames g (realizeSt ν N rs g.storage) ν := by
  intro s t
  induction t with
  | var | err => intro _; rfl
  | app0 o =>
    intro h
    cases o <;> first | rfl | simp only [LTm.aFree, Op0.aFree, Bool.false_eq_true] at h
  | app1 o a iha =>
    intro h; simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_app1, LTm.eval_app1, iha h.2, Op1.eval_aFree o h.1]
  | app2 o a b iha ihb =>
    intro h; simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_app2, LTm.eval_app2, iha h.1.2, ihb h.2, Op2.eval_aFree o h.1.1]
  | app3 o a b c iha ihb ihc =>
    intro h; simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_app3, LTm.eval_app3, iha h.1.1.2, ihb h.1.2, ihc h.2, Op3.eval_aFree o h.1.1.1]
  | index it a b iha ihb =>
    intro h; simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_index, LTm.eval_index, iha h.1, ihb h.2]
  | seq a b iha ihb =>
    intro h; simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_seq, LTm.eval_seq, iha h.1, ihb h.2]
    rfl
  | orElse a b iha ihb =>
    intro h; simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_orElse, LTm.eval_orElse, iha h.1, ihb h.2]
  | kite a b t e iha ihb iht ihe =>
    intro h; simp only [LTm.aFree, Bool.and_eq_true] at h
    rw [LTm.eval_kite, LTm.eval_kite, iha h.1.1.1, ihb h.1.1.2, iht h.1.2, ihe h.2]
  | obsW q ih =>
    intro h; simp only [LTm.aFree] at h
    rw [LTm.eval_obsW, LTm.eval_obsW, ih h]
    have hr := LTm.aFree_roots g ν q h
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      congr 1
      simp only [Storage.obs_word_ref]
      exact congrArg (fun v => v.obs.word r.path) (realizeSt_get_ne ν N rs g.storage r.hroot (hr r hq))
  | obsL q ih =>
    intro h; simp only [LTm.aFree] at h
    rw [LTm.eval_obsL, LTm.eval_obsL, ih h]
    have hr := LTm.aFree_roots g ν q h
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      congr 2
      simp only [Storage.obs_len_ref]
      exact congrArg (fun v => v.obs.len r.path) (realizeSt_get_ne ν N rs g.storage r.hroot (hr r hq))
  | obsH q ih =>
    intro h; simp only [LTm.aFree] at h
    rw [LTm.eval_obsH, LTm.eval_obsH, ih h]
    have hr := LTm.aFree_roots g ν q h
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      congr 1
      simp only [Storage.obs_has_ref]
      exact congrArg (fun v => v.obs.has r.path) (realizeSt_get_ne ν N rs g.storage r.hroot (hr r hq))

end Frame

/-! ## The rebuilt arrays' observations -/

theorem foldl_max_ge_init (f : Nat → Nat) : ∀ (l : List Nat) (m : Nat),
    m ≤ l.foldl (fun a j => max a (f j)) m
  | [], _ => Nat.le_refl _
  | j :: l, m => Nat.le_trans (Nat.le_max_left m (f j)) (foldl_max_ge_init f l _)

theorem foldl_max_ge (f : Nat → Nat) : ∀ (l : List Nat) (m : Nat) {j : Nat}, j ∈ l →
    f j ≤ l.foldl (fun a j => max a (f j)) m
  | [], _, _, h => nomatch h
  | k :: l, m, j, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right m (f j)) (foldl_max_ge_init f l _)
    · exact foldl_max_ge f l _ h

theorem foldl_max_le (f : Nat → Nat) {M : Nat} : ∀ (l : List Nat) (m : Nat), m ≤ M →
    (∀ j ∈ l, f j ≤ M) → l.foldl (fun a j => max a (f j)) m ≤ M
  | [], _, hm, _ => hm
  | k :: l, _, hm, hf => foldl_max_le f l _ (Nat.max_le.mpr ⟨hm, hf k List.mem_cons_self⟩)
      fun j hj => hf j (List.mem_cons_of_mem _ hj)

theorem uint_toNat_lt (v : PrimTy.uint.Denote) : v.1.toNat < 2 ^ 256 := by
  have h := v.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  omega

section RealObs

variable (ν : AEnv) (N : Nat) (rs : List (ARead C)) (st : Storage C)

theorem lenOf_lt (a : Name) : lenOf ν N rs a < 2 ^ 256 := by
  unfold lenOf
  split
  · exact uint_toNat_lt _
  · exact Nat.two_pow_pos 256

theorem lenOf_le_slotsOf (a : Name) (e : PrimTy) : lenOf ν N rs a ≤ slotsOf ν N rs a e :=
  foldl_max_ge_init _ _ _

theorem slots_toList {E : Ty} (f : Nat → SVal E) {L S : Nat} (h : L ≤ S) :
    (List.range L).map f ++ (List.range (S - L)).map (fun t => f (L + t)) = (List.range S).map f := by
  have e : S = L + (S - L) := by omega
  conv => rhs; rw [e, List.range_add, List.map_append, List.map_map]
  rfl

theorem getElem?_range_map {α : Type} (f : Nat → α) (S k : Nat) :
    ((List.range S).map f)[k]? = if k < S then some (f k) else none := by
  by_cases hk : k < S <;> simp [hk]

/-- The rebuilt dynamic array: a word at an index. -/
theorem realize_dyn_word {a : Name} {e : PrimTy} (h : C.rootType a = some (.ref (.array (.prim e))))
    (ha : C.isArrRoot a = true) (k : PrimTy.uint.Denote) :
    (realizeSt ν N rs st).obs.word (.ref ((SRef.ofRoot a h).index (.arr .dyn) k)) =
      if k.1.toNat < slotsOf ν N rs a e then wordAt ν N rs a e k.1.toNat else PrimTy.dflt e := by
  rw [Storage.obs_word_ref]
  rw [show ((SRef.ofRoot a h).index (.arr .dyn) k).path = .at k .nil by
    simp only [SRef.index, SRef.append, SRef.ofRoot, Path.index_dyn, Path.append_nil]]
  show ((realizeSt ν N rs st).get h).obs.word (.at k .nil) = _
  unfold realizeSt
  rw [SFields.get_mapF]
  simp only [ha, if_true, arrVal, dif_pos (lenOf_lt ν N rs a), SVal.obs_word, SVal.findM,
    vecOf_toList, SList.toList_ofList, slots_toList _ (lenOf_le_slotsOf ν N rs a e),
    getElem?_range_map]
  by_cases hk : k.1.toNat < slotsOf ν N rs a e <;> simp only [hk, if_true, if_false] <;> rfl

/-- The rebuilt dynamic array: whether a slot is there. -/
theorem realize_dyn_has {a : Name} {e : PrimTy} (h : C.rootType a = some (.ref (.array (.prim e))))
    (ha : C.isArrRoot a = true) (k : PrimTy.uint.Denote) :
    (realizeSt ν N rs st).obs.has (.ref ((SRef.ofRoot a h).index (.arr .dyn) k)) =
      decide (k.1.toNat < slotsOf ν N rs a e) := by
  rw [Storage.obs_has_ref]
  rw [show ((SRef.ofRoot a h).index (.arr .dyn) k).path = .at k .nil by
    simp only [SRef.index, SRef.append, SRef.ofRoot, Path.index_dyn, Path.append_nil]]
  show ((realizeSt ν N rs st).get h).obs.has (.at k .nil) = _
  unfold realizeSt
  rw [SFields.get_mapF]
  simp only [ha, if_true, arrVal, dif_pos (lenOf_lt ν N rs a), SVal.obs_has, SVal.findM,
    vecOf_toList, SList.toList_ofList, slots_toList _ (lenOf_le_slotsOf ν N rs a e),
    getElem?_range_map]
  split <;> simp_all

/-- The rebuilt dynamic array: its live length. -/
theorem realize_dyn_len {a : Name} {e : PrimTy} (h : C.rootType a = some (.ref (.array (.prim e))))
    (ha : C.isArrRoot a = true) :
    (realizeSt ν N rs st).obs.len (.ref (SRef.ofRoot a h)) = lenOf ν N rs a := by
  rw [Storage.obs_len_ref]
  show ((realizeSt ν N rs st).get h).obs.len .nil = _
  unfold realizeSt
  rw [SFields.get_mapF]
  simp only [ha, if_true, arrVal, dif_pos (lenOf_lt ν N rs a), SVal.obs_len, SVal.findM]
  rfl

/-- The rebuilt fixed array: a word at an index. -/
theorem realize_fixed_word {a : Name} {e : PrimTy} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed (.prim e) n))) (ha : C.isArrRoot a = true)
    (k : PrimTy.uint.Denote) :
    (realizeSt ν N rs st).obs.word (.ref ((SRef.ofRoot a h).index (.arr .fixed) k)) =
      if k.1.toNat < n then wordAt ν N rs a e k.1.toNat else PrimTy.dflt e := by
  rw [Storage.obs_word_ref]
  rw [show ((SRef.ofRoot a h).index (.arr .fixed) k).path = .atF k .nil by
    simp only [SRef.index, SRef.append, SRef.ofRoot, Path.index_fixed, Path.append_nil]]
  show ((realizeSt ν N rs st).get h).obs.word (.atF k .nil) = _
  unfold realizeSt
  rw [SFields.get_mapF]
  simp only [ha, if_true, arrVal, SVal.obs_word, SVal.findM, vecOf_toList, getElem?_range_map]
  by_cases hk : k.1.toNat < n <;> simp only [hk, if_true, if_false] <;> rfl

/-- The rebuilt fixed array: whether a slot is there. -/
theorem realize_fixed_has {a : Name} {e : PrimTy} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed (.prim e) n))) (ha : C.isArrRoot a = true)
    (k : PrimTy.uint.Denote) :
    (realizeSt ν N rs st).obs.has (.ref ((SRef.ofRoot a h).index (.arr .fixed) k)) =
      decide (k.1.toNat < n) := by
  rw [Storage.obs_has_ref]
  rw [show ((SRef.ofRoot a h).index (.arr .fixed) k).path = .atF k .nil by
    simp only [SRef.index, SRef.append, SRef.ofRoot, Path.index_fixed, Path.append_nil]]
  show ((realizeSt ν N rs st).get h).obs.has (.atF k .nil) = _
  unfold realizeSt
  rw [SFields.get_mapF]
  simp only [ha, if_true, arrVal, SVal.obs_has, SVal.findM, vecOf_toList, getElem?_range_map]
  split <;> simp_all

end RealObs

/-! ## What the antecedent says -/

section ConsFacts

variable {g : State C []} {ν : AEnv} {N : Nat} {rs : List (ARead C)}

theorem cons_mem (hC : (ARead.cons N rs).holds g ν) {d : LFml C}
    (hd : d ∈ (List.range rs.length).flatMap fun j =>
      match rs[j]? with
      | none => []
      | some r => r.self N j ++ (List.range rs.length).flatMap fun k =>
        match rs[k]? with
        | none => []
        | some s => if j = k then [] else r.pair N j k s) : d.holds g ν :=
  (LFml.holds_conj g ν _).mp hC d hd

theorem cons_self (hC : (ARead.cons N rs).holds g ν) {j : Nat} {r : ARead C} (hr : rs[j]? = some r) :
    ∀ d ∈ r.self N j, d.holds g ν := by
  intro d hd
  apply cons_mem hC
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
  rw [hr]
  exact List.mem_append_left _ hd

theorem cons_pair (hC : (ARead.cons N rs).holds g ν) {j k : Nat} {r s : ARead C} (hjk : j ≠ k)
    (hr : rs[j]? = some r) (hs : rs[k]? = some s) : ∀ d ∈ r.pair N j k s, d.holds g ν := by
  intro d hd
  apply cons_mem hC
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  have hk : k < rs.length := (List.getElem?_eq_some_iff.mp hs).1
  refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
  rw [hr]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩)
  rw [hs]
  show d ∈ (if j = k then [] else r.pair N j k s)
  rw [if_neg hjk]
  exact hd

theorem holds_isT (t : LTm C (.val .bool)) :
    (LFml.isT t).holds g ν ↔ (t.eval g ν : Option Bool) = some true := by
  rw [LFml.holds_eq_iff]
  exact ⟨fun ⟨x, h1, h2⟩ => by cases h2; exact h1, fun h => ⟨true, h, rfl⟩⟩

theorem holds_isF (t : LTm C (.val .bool)) :
    (LFml.isF t).holds g ν ↔ (t.eval g ν : Option Bool) = some false := by
  rw [LFml.holds_eq_iff]
  exact ⟨fun ⟨x, h1, h2⟩ => by cases h2; exact h1, fun h => ⟨false, h, rfl⟩⟩

theorem eval_ltU (a b : Nat) :
    ((LTm.ltU (.var a) (.var b) : LTm C (.val .bool)).eval g ν : Option Bool) =
      some (decide ((ν.u a).1 < (ν.u b).1)) := rfl

theorem eval_leU (a b : Nat) :
    ((LTm.leU (.var a) (.var b) : LTm C (.val .bool)).eval g ν : Option Bool) =
      some (decide ((ν.u a).1 ≤ (ν.u b).1)) := rfl

theorem eval_ltLit (a : Nat) (n : PrimTy.uint.Denote) :
    ((LTm.ltU (.var a) (.app0 (.lit n)) : LTm C (.val .bool)).eval g ν : Option Bool) =
      some (decide ((ν.u a).1 < n.1)) := rfl

theorem holds_eqVar {p : PrimTy} (a b : Nat) :
    (LFml.eq (.var a : LTm C (.val p)) (.var b)).holds g ν ↔ ν.get p a = ν.get p b := by
  rw [LFml.holds_eq_iff]
  constructor
  · rintro ⟨x, h1, h2⟩
    exact (Option.some.inj h1).trans (Option.some.inj h2).symm
  · intro h; exact ⟨_, rfl, by rw [LTm.eval_var, h]⟩

theorem holds_eqDflt {p : PrimTy} (a : Nat) :
    (LFml.eq (.var a : LTm C (.val p)) (LTm.dfltLit p)).holds g ν ↔ ν.get p a = PrimTy.dflt p := by
  rw [LFml.holds_eq_iff]
  constructor
  · rintro ⟨x, h1, h2⟩
    exact (Option.some.inj h1).trans (Option.some.inj h2).symm
  · intro h; exact ⟨_, rfl, by rw [h]; rfl⟩

theorem pair_ww (hC : (ARead.cons N rs).holds g ν) {j k : Nat} {r s : ARead C} (hjk : j ≠ k)
    (hr : rs[j]? = some r) (hs : rs[k]? = some s) (hroot : r.root = s.root) (hkr : r.kind = .word)
    (hks : s.kind = .word) (hx : ν.u (N + 2 * j) = ν.u (N + 2 * k)) :
    ν.get r.e (N + 2 * j + 1) = ν.get r.e (N + 2 * k + 1) := by
  have hp := cons_pair hC hjk hr hs
  simp only [ARead.pair, hroot, if_true, hkr, hks, List.mem_singleton, forall_eq] at hp
  exact (holds_eqVar _ _).mp (hp ((holds_eqVar (p := .uint) _ _).mpr hx))

theorem pair_ll (hC : (ARead.cons N rs).holds g ν) {j k : Nat} {r s : ARead C} (hjk : j ≠ k)
    (hr : rs[j]? = some r) (hs : rs[k]? = some s) (hroot : r.root = s.root) (hkr : r.kind = .len)
    (hks : s.kind = .len) : ν.u (N + 2 * j + 1) = ν.u (N + 2 * k + 1) := by
  have hp := cons_pair hC hjk hr hs
  simp only [ARead.pair, hroot, if_true, hkr, hks, List.mem_singleton, forall_eq] at hp
  exact (holds_eqVar (p := .uint) _ _).mp hp

theorem pair_hh (hC : (ARead.cons N rs).holds g ν) {j k : Nat} {r s : ARead C} (hjk : j ≠ k)
    (hr : rs[j]? = some r) (hs : rs[k]? = some s) (hroot : r.root = s.root) (hkr : r.kind = .has)
    (hks : s.kind = .has) (hj : ν.b (N + 2 * j + 1) = true)
    (hle : (ν.u (N + 2 * k)).1 ≤ (ν.u (N + 2 * j)).1) : ν.b (N + 2 * k + 1) = true := by
  have hp := cons_pair hC hjk hr hs
  simp only [ARead.pair, hroot, if_true, hkr, hks, List.mem_singleton, forall_eq] at hp
  have := hp ((holds_isT _).mpr (by rw [LTm.eval_var]; exact congrArg some hj))
    ((holds_isT _).mpr (by rw [eval_leU]; simp only [hle, decide_true]))
  rw [holds_isT, LTm.eval_var] at this
  exact Option.some.inj this

theorem pair_hl (hC : (ARead.cons N rs).holds g ν) {j k : Nat} {r s : ARead C} (hjk : j ≠ k)
    (hr : rs[j]? = some r) (hs : rs[k]? = some s) (hroot : r.root = s.root) (hkr : r.kind = .has)
    (hks : s.kind = .len) (hlt : (ν.u (N + 2 * j)).1 < (ν.u (N + 2 * k + 1)).1) :
    ν.b (N + 2 * j + 1) = true := by
  have hp := cons_pair hC hjk hr hs
  simp only [ARead.pair, hroot, if_true, hkr, hks, List.mem_singleton, forall_eq] at hp
  have := hp ((holds_isT _).mpr (by rw [eval_ltU]; simp only [hlt, decide_true]))
  rw [holds_isT, LTm.eval_var] at this
  exact Option.some.inj this

theorem pair_hw (hC : (ARead.cons N rs).holds g ν) {j k : Nat} {r s : ARead C} (hjk : j ≠ k)
    (hr : rs[j]? = some r) (hs : rs[k]? = some s) (hroot : r.root = s.root) (hkr : r.kind = .has)
    (hks : s.kind = .word) (hj : ν.b (N + 2 * j + 1) = false)
    (hle : (ν.u (N + 2 * j)).1 ≤ (ν.u (N + 2 * k)).1) :
    ν.get s.e (N + 2 * k + 1) = PrimTy.dflt s.e := by
  have hp := cons_pair hC hjk hr hs
  simp only [ARead.pair, hroot, if_true, hkr, hks, List.mem_singleton, forall_eq] at hp
  exact (holds_eqDflt _).mp (hp ((holds_isF _).mpr (by rw [LTm.eval_var]; exact congrArg some hj))
    ((holds_isT _).mpr (by rw [eval_leU]; simp only [hle, decide_true])))

/-- A word or slot read's index atom is its index. -/
theorem self_idx (hC : (ARead.cons N rs).holds g ν) {j : Nat} {r : ARead C} (hr : rs[j]? = some r)
    (hk : r.kind = .word ∨ r.kind = .has) {k : PrimTy.uint.Denote}
    (hi : (r.idx.eval g ν : Option PrimTy.uint.Denote) = some k) : ν.u (N + 2 * j) = k := by
  have hs := cons_self hC hr
  have hd : (LFml.imp (.eq r.idx r.idx) (.eq r.idx (xAt N j))).holds g ν := by
    rcases hk with hk | hk <;> exact hs _ (by simp only [ARead.self, hk, List.mem_append,
      List.mem_singleton, true_or])
  have := hd ((LFml.holds_rets g ν r.idx).mpr ⟨k, hi⟩)
  rw [LFml.holds_eq_iff, hi] at this
  obtain ⟨x, hx, hx'⟩ := this
  cases hx
  exact Option.some.inj hx'

end ConsFacts

/-! ## The atoms that satisfy the antecedent describe the rebuilt arrays -/

section Realized

variable {g : State C []} {ν : AEnv} {N : Nat} {rs : List (ARead C)}

theorem isRd_of {j : Nat} {r : ARead C} (hr : rs[j]? = some r) : isRd rs r.root r.kind j = true := by
  simp only [isRd, hr, beq_self_eq_true, Bool.and_self]

theorem isRd_some {a : Name} {k : AKind} {j : Nat} (h : isRd rs a k j = true) :
    ∃ r, rs[j]? = some r ∧ r.root = a ∧ r.kind = k := by
  unfold isRd at h
  split at h
  · rename_i r hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨r, hr, h.1, h.2⟩
  · cases h

theorem uint_ext_toNat {u w : PrimTy.uint.Denote} (h : u.1.toNat = w.1.toNat) : u = w := by
  have hu := uint_nonneg u
  have hw := uint_nonneg w
  apply Subtype.ext
  omega

theorem ARead.e_eq_of_root (r s : ARead C) (h : r.root = s.root) : r.e = s.e := by
  rcases r with ⟨a, R, hR, _, e, ar, _, _⟩
  rcases s with ⟨a', R', hR', _, e', ar', _, _⟩
  dsimp only at h ⊢
  subst h
  obtain rfl : R' = R := by
    have := hR'.symm.trans hR; simp only [Option.some.injEq, Ty.ref.injEq] at this; exact this
  exact ArrTy.elem_eq ar ar'

theorem bump_le_slots (a : Name) (e : PrimTy) {j : Nat} (hj : j < rs.length) :
    bump ν N rs a e j ≤ slotsOf ν N rs a e :=
  foldl_max_ge _ _ _ (List.mem_range.mpr hj)

/-- The slot of a word read holds its value atom. -/
theorem wordAt_eq (hC : (ARead.cons N rs).holds g ν) {j : Nat} {r : ARead C} (hr : rs[j]? = some r)
    (hk : r.kind = .word) : wordAt ν N rs r.root r.e (idxV ν N j) = ν.get r.e (N + 2 * j + 1) := by
  unfold wordAt
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  cases hf : (List.range rs.length).find?
      (fun j' => isRd rs r.root .word j' && idxV ν N j' == idxV ν N j) with
  | none =>
    have := List.find?_range_eq_none.mp hf j hj
    rw [← hk, isRd_of hr] at this
    simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true] at this
  | some j₀ =>
    obtain ⟨hp, hj₀, -⟩ := List.find?_range_eq_some.mp hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨r₀, hr₀, hroot₀, hk₀⟩ := isRd_some hp.1
    by_cases e : j₀ = j
    · subst e; rfl
    · have hw := pair_ww hC e hr₀ hr (hroot₀.trans rfl) hk₀ hk
        (uint_ext_toNat hp.2)
      rw [ARead.e_eq_of_root r₀ r hroot₀] at hw
      exact hw

/-- A word read past the slots reads the default. -/
theorem word_past (a : Name) (e : PrimTy) {j : Nat} {r : ARead C} (hr : rs[j]? = some r)
    (hroot : r.root = a) (hk : r.kind = .word)
    (hS : ¬ idxV ν N j < slotsOf ν N rs a e) : ν.get e (N + 2 * j + 1) = PrimTy.dflt e := by
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  refine Classical.byContradiction fun hne => hS ?_
  have hb := bump_le_slots (ν := ν) (N := N) a e hj
  have hrd : isRd rs a .word j = true := by rw [← hroot, ← hk]; exact isRd_of hr
  simp only [bump, hrd, hne, decide_false, Bool.not_false, Bool.and_true, Bool.or_true,
    if_true] at hb
  omega

/-- A slot read that says no slot is there reads past every slot. -/
theorem has_false_slots (hC : (ARead.cons N rs).holds g ν) {j : Nat} {r : ARead C}
    (hr : rs[j]? = some r) (hk : r.kind = .has) (hb : ν.b (N + 2 * j + 1) = false) :
    slotsOf ν N rs r.root r.e ≤ idxV ν N j := by
  have hj0 := uint_nonneg (ν.u (N + 2 * j))
  apply foldl_max_le
  · unfold lenOf
    split
    · rename_i j₁ hf
      obtain ⟨hp, -, -⟩ := List.find?_range_eq_some.mp hf
      obtain ⟨r₁, hr₁, hroot₁, hk₁⟩ := isRd_some hp
      have hne : j ≠ j₁ := fun e => by subst e; rw [hr] at hr₁; cases hr₁; rw [hk] at hk₁; cases hk₁
      refine Classical.byContradiction fun hlt => ?_
      have h1 := uint_nonneg (ν.u (N + 2 * j₁ + 1))
      have := pair_hl hC hne hr hr₁ hroot₁.symm hk hk₁ (by unfold idxV at hlt; omega)
      rw [hb] at this; cases this
    · exact Nat.zero_le _
  · intro m hm
    have hm' : m < rs.length := List.mem_range.mp hm
    unfold bump
    split
    · rename_i hcond
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hcond
      rcases hcond with ⟨hrd, hbm⟩ | ⟨hrd, hne⟩
      · obtain ⟨rm, hrm, hrootm, hkm⟩ := isRd_some hrd
        have hmj : m ≠ j := fun e => by subst e; rw [hb] at hbm; cases hbm
        refine Classical.byContradiction fun hlt => ?_
        have h1 := uint_nonneg (ν.u (N + 2 * m))
        have := pair_hh hC hmj hrm hr hrootm hkm hk hbm (by unfold idxV at hlt; omega)
        rw [hb] at this; cases this
      · obtain ⟨rm, hrm, hrootm, hkm⟩ := isRd_some hrd
        have hjm : j ≠ m := fun e => by subst e; rw [hr] at hrm; cases hrm; rw [hk] at hkm; cases hkm
        refine Classical.byContradiction fun hlt => ?_
        have h1 := uint_nonneg (ν.u (N + 2 * m))
        have := pair_hw hC hjm hr hrm hrootm.symm hk hkm hb (by unfold idxV at hlt; omega)
        rw [ARead.e_eq_of_root rm r hrootm] at this
        exact hne this
    · exact Nat.zero_le _

theorem uintOfNat_toNatA (i : PrimTy.uint.Denote) : uintOfNat i.1.toNat = i := by
  have hlt := uint_toNat_lt i
  have h0 := uint_nonneg i
  rw [uintOfNat_eq_lenU hlt]
  apply Subtype.ext
  show ((i.1.toNat : Nat) : Int) = i.1
  omega

theorem fixed_lt_bound {a : Name} {e : PrimTy} {n : Nat}
    (h : C.rootType a = some (.ref (.fixed (.prim e) n))) (ha : C.isArrRoot a = true) :
    n < 2 ^ 256 := by
  unfold Contract.isArrRoot at ha
  rw [h] at ha
  simpa only [decide_eq_true_eq] using ha

/-- **Atoms that satisfy the antecedent describe the rebuilt storage.** -/
theorem describes_realize (hC : (ARead.cons N rs).holds g ν) :
    Describes g (realizeSt ν N rs g.storage) ν N rs := by
  intro j r hr
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨a, R, h, harr, e, ar, kind, idx⟩ := r
  cases ar with
  | dyn =>
    cases kind with
    | word =>
      simp only [ARead.Describes]
      intro k hk
      have hx := self_idx hC hr (Or.inl rfl) hk
      refine ⟨hx, ?_⟩
      show _ = (realizeSt ν N rs g.storage).obs.word (.ref ((SRef.ofRoot a h).index (.arr .dyn) k))
      rw [realize_dyn_word ν N rs g.storage h harr k]
      have hk' : k.1.toNat = idxV ν N j := by rw [idxV, hx]
      rw [hk']
      split
      · exact (wordAt_eq hC hr rfl).symm
      · rename_i hS
        exact word_past a e hr rfl rfl hS
    | has =>
      simp only [ARead.Describes]
      intro k hk
      have hx := self_idx hC hr (Or.inr rfl) hk
      refine ⟨hx, ?_⟩
      show _ = (realizeSt ν N rs g.storage).obs.has (.ref ((SRef.ofRoot a h).index (.arr .dyn) k))
      rw [realize_dyn_has ν N rs g.storage h harr k]
      have hk' : k.1.toNat = idxV ν N j := by rw [idxV, hx]
      rw [hk']
      cases hb : ν.b (N + 2 * j + 1) with
      | false =>
        have := has_false_slots hC hr rfl hb
        exact (decide_eq_false (Nat.not_lt.mpr this)).symm
      | true =>
        have hbump := bump_le_slots (ν := ν) (N := N) (rs := rs) a e hj
        have hrd : isRd rs a .has j = true := isRd_of hr
        simp only [bump, hrd, hb, Bool.and_self, Bool.true_or, if_true] at hbump
        exact (decide_eq_true (by omega)).symm
    | len =>
      simp only [ARead.Describes, lenDesc]
      rw [realize_dyn_len ν N rs g.storage h harr]
      unfold lenOf
      cases hf : (List.range rs.length).find? (isRd rs a .len) with
      | none =>
        have := List.find?_range_eq_none.mp hf j hj
        rw [show a = (⟨a, _, h, harr, e, .dyn, .len, idx⟩ : ARead C).root from rfl, isRd_of hr] at this
        cases this
      | some j₁ =>
        obtain ⟨hp, -, -⟩ := List.find?_range_eq_some.mp hf
        obtain ⟨r₁, hr₁, hroot₁, hk₁⟩ := isRd_some hp
        dsimp only
        rw [uintOfNat_toNatA]
        by_cases e₁ : j₁ = j
        · subst e₁; rfl
        · exact (pair_ll hC e₁ hr₁ hr hroot₁ hk₁ rfl).symm
  | @fixed _ n =>
    have hn := fixed_lt_bound h harr
    have hs := cons_self hC hr
    cases kind with
    | word =>
      simp only [ARead.Describes]
      intro k hk
      have hx := self_idx hC hr (Or.inl rfl) hk
      refine ⟨hx, ?_⟩
      show _ = (realizeSt ν N rs g.storage).obs.word (.ref ((SRef.ofRoot a h).index (.arr .fixed) k))
      rw [realize_fixed_word ν N rs g.storage h harr k]
      have hk' : k.1.toNat = idxV ν N j := by rw [idxV, hx]
      rw [hk']
      split
      · exact (wordAt_eq hC hr rfl).symm
      · rename_i hS
        simp only [ARead.self, ArrTy.fixedLen?, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp, forall_eq] at hs
        refine (holds_eqDflt _).mp (hs.2 ((holds_isF _).mpr ?_))
        rw [eval_ltLit, uintOfNat_val hn]
        have h0 := uint_nonneg (ν.u (N + 2 * j))
        unfold idxV at hS
        exact congrArg some (decide_eq_false (by omega))
    | has =>
      simp only [ARead.Describes]
      intro k hk
      have hx := self_idx hC hr (Or.inr rfl) hk
      refine ⟨hx, ?_⟩
      show _ = (realizeSt ν N rs g.storage).obs.has (.ref ((SRef.ofRoot a h).index (.arr .fixed) k))
      rw [realize_fixed_has ν N rs g.storage h harr k]
      simp only [ARead.self, ArrTy.fixedLen?, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq] at hs
      have h2 := hs.2
      rw [LFml.holds_eq_iff, LTm.eval_var, eval_ltLit, uintOfNat_val hn, hx] at h2
      obtain ⟨x, hx1, hx2⟩ := h2
      have h0 := uint_nonneg k
      have e1 : ν.b (N + 2 * j + 1) = x := Option.some.inj hx1
      rw [e1, ← Option.some.inj hx2]
      exact decide_eq_decide.mpr (by omega)
    | len => simp only [ARead.Describes, lenDesc]

end Realized

end Solidity.Decide
