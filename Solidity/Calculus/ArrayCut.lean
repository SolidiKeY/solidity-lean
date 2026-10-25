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
  ar : ArrTy R T
  e : PrimTy
  he : T = .prim e
  i : LTm C (.val .uint)
  eq : q = .index (.arr ar) (.app0 (.root root h)) i

/-- Evidence that a path is an array root of primitives. -/
structure RootPath {E : Ty} (q : LTm C (.path (.ref (.array E)))) where
  root : Name
  h : C.rootType root = some (.ref (.array E))
  e : PrimTy
  he : E = .prim e
  eq : q = .app0 (.root root h)

def elemOp? {R : RefTy} {T : Ty} (ar : ArrTy R T) (o : Op0 C (.path (.ref R)))
    (i : LTm C (.val .uint)) : Option (ElemPath (LTm.index (.arr ar) (.app0 o) i)) :=
  match o with
  | .root a h =>
    if C.isArrRoot a then
      match T, ar with
      | .prim e, ar => some ⟨a, R, h, ar, e, rfl, i, rfl⟩
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
    if C.isArrRoot a then
      match E with
      | .prim e => some ⟨a, h, e, rfl, rfl⟩
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
            rs ++ [⟨ep.root, ep.R, ep.h, ep.e, ep.he ▸ ep.ar, .word, ep.i⟩])
      else none
    | none => if q.aFree then some (.obsW q, rs) else none
  | _, .obsH q, rs =>
    match q.elemPath? with
    | some ep =>
      if ep.i.aFree then
        match findRead rs ep.root .has ep.i with
        | some j => some (.seq ep.i (.var (N + 2 * j + 1)), rs)
        | none => some (.seq ep.i (.var (N + 2 * rs.length + 1)),
            rs ++ [⟨ep.root, ep.R, ep.h, ep.e, ep.he ▸ ep.ar, .has, ep.i⟩])
      else none
    | none => if q.aFree then some (.obsH q, rs) else none
  | _, .obsL q, rs =>
    match q.rootPath? with
    | some rp =>
      match findRead rs rp.root .len (.app0 (.lit (PrimTy.dflt .uint))) with
      | some j => some (.var (N + 2 * j + 1), rs)
      | none => some (.var (N + 2 * rs.length + 1),
          rs ++ [⟨rp.root, .array (.prim rp.e), rp.he ▸ rp.h, rp.e, .dyn, .len,
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

/-- The live length of a dynamic array read at its root; a fixed array's
length. -/
def lenObsOf {R : RefTy} {e : PrimTy} (a : Name) (h : C.rootType a = some (.ref R))
    (ar : ArrTy R (.prim e)) (st : Storage C) : Nat :=
  match R, h, ar with
  | _, h, .dyn => st.obs.len (.ref (SRef.ofRoot a h))
  | _, _, @ArrTy.fixed _ n => n

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
  | .len => ν.u (N + 2 * j + 1) = uintOfNat (lenObsOf r.root r.h r.ar st)

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
  rcases ep with ⟨a, R, h, ar, e, he, i, rfl⟩
  cases he
  rcases r with ⟨a', R', h', e', ar', k', i'⟩
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
  rcases ep with ⟨a, R, h, ar, e, he, i, rfl⟩
  subst he
  rcases r with ⟨a', R', h', e', ar', k', i'⟩
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
  rcases rp with ⟨a, h, e, he, rfl⟩
  subst he
  rcases r with ⟨a', R', h', e', ar', k', i'⟩
  dsimp only at hroot hk
  subst hroot hk
  obtain rfl : R' = .array (.prim e) := by
    have := h'.symm.trans h; simp only [Option.some.injEq, Ty.ref.injEq] at this; exact this
  cases ar'
  simp only [ARead.Describes, lenObsOf] at hd
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
          exact aCut_obsW hD hF q ep hi _ ⟨ep.root, ep.R, ep.h, ep.e, ep.he ▸ ep.ar, .word, ep.i⟩
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
          exact aCut_obsH hD hF q ep hi _ ⟨ep.root, ep.R, ep.h, ep.e, ep.he ▸ ep.ar, .has, ep.i⟩
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
        exact aCut_obsL hD q rp _ ⟨rp.root, .array (.prim rp.e), rp.he ▸ rp.h, rp.e, .dyn, .len,
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

end Solidity.Decide
