import Solidity.Theory.Storage

/-!
# What a storage term means

`Theory/Storage.lean` is solkey's storage theory as terms.  This module maps a
term to the interpreter's own storage value and proves the two agree, which is
what makes the taclets over there statements about *this* semantics rather
than about a private model.

## The denotation needs no types

A type-directed denotation looked unavoidable at first: KeY's defaults are
sort-indexed (`defaultValue<[α]>`) where the interpreter materializes them
(`defaultForTy`), so `mtSt` has no `SVal` until someone supplies a type.  It
is avoidable, because nothing needs it.  A term produced by a rule's update
(`Update/Theory.lean`) is rooted at `sval`, the pre-state tree; `mtSt` and
`dflt` arise only on paths where the *interpreter* is stuck or reverting
anyway.  So `denoteSt` sends them to `Halt.stuck` and lands in `Res SVal`,
where the agreement theorem is an unconditional equation rather than an
equation under a well-formedness predicate.

`slotOf` and `putAt` are one step of `Semantics.SVal.save`, split in two: the
slot is resolved *before* the child is denoted, because that is the order
`SVal.save` fails in — an out-of-bounds index reverts without ever looking at
the value being written.

## Push and pop are whole-array writes here

KeY spells `arr.push(se)` as **two** saves in one parallel update, the new
slot `consr(arr, at(find(storage, consr(arr, size))))` and the new length
`consr(arr, size)`, both reading the pre-state.  The slot index is therefore
the *old* length — outside the array — and `SVal.save` reverts there, so that
term cannot denote through `putAt` without giving `putAt` an append arm that
would then disagree with `SVal.save` on every ordinary write at that index.

`Rules.StorageUpd.push` is already a merged constructor over KeY's three push
taclets, and `Update/Eval.lean`'s `pushStorage` already computes the extended
array in one go, so `Update/Theory.lean` writes the extended array at the
array's own path.  The same holds for `pop`.

solkey `c80a54494c` made the three push taclets' *inner* terms differ — the
value copy writes `copyAt` where the other two write `save` — and the merged
constructor survives it for the reason the slot index gives: at the old length
there is nothing to keep, so `denote_copyAt_absent` below collapses the copy to
the plain write.
-/

namespace Solidity
namespace Theory

open Semantics

/-! ## One step of `SVal.save`, split -/

/-- The value a slot currently holds, failing exactly where `SVal.save`'s step
fails: an absent member is stuck, an out-of-bounds index reverts, an absent
mapping key reads the mapping's default. -/
def slotOf : SVal -> Seg -> Res SVal
  | SVal.struct fields, Seg.field name =>
      match lookupBy name fields with
      | some old => .ok old
      | none => .error .stuck
  | SVal.array elems, Seg.at i =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then .ok (elems.get ⟨i.toNat, h.2⟩)
      else .error .revert
  | SVal.map entries d, Seg.at i =>
      match lookupBy i entries with
      | some old => .ok old
      | none => .ok d
  | SVal.prim _, _ => .error .stuck
  | SVal.struct _, Seg.at _ => .error .stuck
  | SVal.array _, Seg.field _ => .error .stuck
  | SVal.map _ _, Seg.field _ => .error .stuck

/-- Write a slot.  The shape dispatch is `slotOf`'s, so the two agree on which
inputs fail and how. -/
def putAt : SVal -> Seg -> SVal -> Res SVal
  | SVal.struct fields, Seg.field name, w =>
      match lookupBy name fields with
      | some _ => .ok (SVal.struct (setBy name w fields))
      | none => .error .stuck
  | SVal.array elems, Seg.at i, w =>
      if 0 ≤ i ∧ i.toNat < elems.length then .ok (SVal.array (elems.set i.toNat w))
      else .error .revert
  | SVal.map entries d, Seg.at i, w => .ok (SVal.map (setBy i w entries) d)
  | SVal.prim _, _, _ => .error .stuck
  | SVal.struct _, Seg.at _, _ => .error .stuck
  | SVal.array _, Seg.field _, _ => .error .stuck
  | SVal.map _ _, Seg.field _, _ => .error .stuck

/-! ## The copied location, eagerly

`StValue.merge` is the one lazy marker of the theory, so this is where its
meaning is fixed: a copied struct member by member, with a mapping member taken
from the *target's* old value.  The recursion is on the copied value, which is
why `mergeFields` walks `fn` and only looks `fo` up: a member the target does
not have is copied outright. -/

mutual
/-- `merge<[Struct]>(old, new)`, evaluated. -/
def mergeKeepMaps : SVal -> SVal -> SVal
  | SVal.struct fo, SVal.struct fn => SVal.struct (mergeFields fo fn)
  | _, n => n

/-- One member of a copied struct: `selectStMergeMap` on a mapping member,
`selectStMergeRef` on any other member the target has, and the copied value
where the target has none. -/
def mergeMember : Option SVal -> SVal -> SVal
  | some (SVal.map es d), _ => SVal.map es d
  | some o, v => mergeKeepMaps o v
  | none, v => v

/-- The member walk of `mergeKeepMaps`. -/
def mergeFields : List (Name × SVal) -> List (Name × SVal) -> List (Name × SVal)
  | _, [] => []
  | fo, (name, v) :: rest =>
      (name, mergeMember (lookupBy name fo) v) :: mergeFields fo rest
end

mutual
/-- Does this *value* carry a mapping anywhere?  The value-level twin of
`Semantics.tyHasMapping`, and the side condition under which a copy is the
plain write the interpreter performs. -/
def svalHasMapping : SVal -> Bool
  | SVal.map _ _ => true
  | SVal.struct fs => fieldsHaveMappingV fs
  | SVal.array es => elemsHaveMapping es
  | SVal.prim _ => false

def fieldsHaveMappingV : List (Name × SVal) -> Bool
  | [] => false
  | (_, v) :: rest => svalHasMapping v || fieldsHaveMappingV rest

def elemsHaveMapping : List SVal -> Bool
  | [] => false
  | v :: rest => svalHasMapping v || elemsHaveMapping rest
end

/-- A copied location, once both sides are denoted.  A target with no value at
all — `dflt` and `mtSt`, i.e. a *fresh* slot, which is what `push` writes —
keeps nothing, so the copy is the copied value; a revert propagates. -/
def mergeDen : Res SVal -> Res SVal -> Res SVal
  | .ok a, .ok b => .ok (mergeKeepMaps a b)
  | .ok _, .error e => .error e
  | .error .stuck, r => r
  | .error e, _ => .error e

/-- What a storage term denotes.  `mtSt` and `dflt` carry no type and so no
value — see the module docstring for why that costs nothing. -/
def denoteSt : StValue -> Res SVal
  | StValue.prim p => .ok (SVal.prim p)
  | StValue.sval v => .ok v
  | StValue.mtSt => .error .stuck
  | StValue.dflt => .error .stuck
  | StValue.merge o n => mergeDen (denoteSt o) (denoteSt n)
  | StValue.storeSt st a v => do
      let sv <- denoteSt st
      let _ <- slotOf sv a
      let w <- denoteSt v
      putAt sv a w

@[simp] theorem denoteSt_sval (v : SVal) : denoteSt (StValue.sval v) = .ok v := rfl


/-! ## `SVal.save` and `SVal.find`, one step at a time

Everything below rests on two decompositions: `SVal.save` is `slotOf` then a
recursive save then `putAt`, and `SVal.find` is `selOf` then a recursive find.
Proving those once makes each agreement theorem a short induction instead of a
re-run of the interpreter's case analysis. -/

/-- One step of `SVal.save`. -/
theorem save_cons (v : SVal) (a : Seg) (rest : List Seg) (w : SVal) :
    v.save (a :: rest) w =
      (do let old <- slotOf v a
          let upd <- old.save rest w
          putAt v a upd) := by
  cases v <;> cases a <;>
    simp [slotOf, putAt, SVal.save, bind, Except.bind] <;>
    split <;> simp_all

/-- The read step: `slotOf`'s twin, with the `length` arm an array read has
and an array *write* does not (assigning `a.length` is a solc error). -/
def selOf : SVal -> Seg -> Res SVal
  | SVal.struct fields, Seg.field name =>
      match lookupBy name fields with
      | some v => .ok v
      | none => .error .stuck
  | SVal.array elems, Seg.field "length" => .ok (SVal.int elems.length)
  | SVal.array elems, Seg.at i =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then .ok (elems.get ⟨i.toNat, h.2⟩)
      else .error .revert
  | SVal.map entries d, Seg.at i =>
      match lookupBy i entries with
      | some v => .ok v
      | none => .ok d
  | SVal.prim _, _ => .error .stuck
  | SVal.struct _, Seg.at _ => .error .stuck
  | SVal.array _, Seg.field _ => .error .stuck
  | SVal.map _ _, Seg.field _ => .error .stuck

/-- One step of `SVal.find`. -/
theorem find_cons (v : SVal) (a : Seg) (rest : List Seg) :
    v.find (a :: rest) = (do let c <- selOf v a; c.find rest) := by
  match v, a with
  | SVal.prim _, Seg.field _ => rfl
  | SVal.prim _, Seg.at _ => rfl
  | SVal.struct fields, Seg.field n =>
      simp only [SVal.find, selOf, bind, Except.bind]
      cases lookupBy n fields <;> rfl
  | SVal.struct _, Seg.at _ => rfl
  | SVal.array elems, Seg.field n =>
      by_cases hn : n = "length"
      · subst hn; rfl
      · simp [SVal.find, selOf, bind, Except.bind, hn]
  | SVal.array elems, Seg.at i =>
      simp only [SVal.find, selOf, bind, Except.bind]
      split <;> rfl
  | SVal.map _ _, Seg.field _ => rfl
  | SVal.map entries _, Seg.at i =>
      simp only [SVal.find, selOf, bind, Except.bind]
      cases lookupBy i entries <;> rfl

/-! ## The agreement, writing -/

/-- **The storage half of the bridge.** The theory's `save` on the pre-state
tree, denoted, *is* the interpreter's `SVal.save` — errors and all, with no
side condition.

This is what turns every taclet of `Theory/Storage.lean` into a statement
about `Semantics.lean`: `SemanticsProperties.SVal.find_save_same` is
`StValue.find_save_extends` read through here, and the frame law the
interpreter never had is `StValue.find_save_frame` read through here.

Stated over an arbitrary payload *term*, because the copy family's payload is a
`merge` marker rather than an `sval` leaf; `denote_save` just below is the leaf
instance, and it is the one every other theorem here uses. -/
theorem denote_save_of {t : StValue} {w : SVal} (ht : denoteSt t = .ok w) :
    ∀ (v : SVal) (p : List Seg), denoteSt (StValue.save (StValue.sval v) p t) = v.save p w := by
  intro v p
  induction p generalizing v with
  | nil => simpa [SVal.save] using ht
  | cons a rest ih =>
      rw [StValue.save, denoteSt, save_cons]
      simp only [denoteSt_sval, bind, Except.bind]
      cases hslot : slotOf v a with
      | error e => rfl
      | ok old =>
          have hsel : StValue.svalSelect v a = StValue.sval old := by
            cases v <;> cases a <;>
              simp_all [slotOf, StValue.svalSelect] <;>
              split at hslot <;> simp_all
          rw [hsel, StValue.asStruct, ih]

/-- The leaf instance: a written `sval` leaf denotes the value it holds. -/
theorem denote_save (v : SVal) (p : List Seg) (w : SVal) :
    denoteSt (StValue.save (StValue.sval v) p (StValue.sval w)) = v.save p w :=
  denote_save_of rfl v p

/-! ## The agreement, reading

`find` lands in no `Res` — KeY's reads are total — so the statement has to be
denotational, and the array `length` arm is why: KeY's `size` is a field of
the term algebra, so `find(storage, consr(arr, size))` reads to a `prim`,
while the interpreter computes `elems.length`.  The two terms differ; what
they denote does not, and that is the whole claim. -/

/-- What the induction needs of a leaf: it denotes the value, and it selects
the way the value does.  Both `sval v` and the `prim` an array length reads to
satisfy it, which is exactly the slack the `length` arm needs. -/
def Denotes (t : StValue) (v : SVal) : Prop :=
  denoteSt t = .ok v ∧ ∀ a, StValue.selectSt t a = StValue.svalSelect v a

theorem Denotes.ofSval (v : SVal) : Denotes (StValue.sval v) v :=
  ⟨rfl, fun _ => rfl⟩

theorem Denotes.ofPrim (p : PrimVal) : Denotes (StValue.prim p) (SVal.prim p) :=
  ⟨rfl, fun a => by cases a <;> rfl⟩

/-- Selecting one segment preserves it.  The array `length` arm is the only
one that lands on `ofPrim` rather than `ofSval`, and it is the reason
`Denotes` has to be a predicate rather than an equation. -/
theorem Denotes.sel {v c : SVal} {a : Seg} (h : selOf v a = .ok c) :
    Denotes (StValue.svalSelect v a) c := by
  match v, a with
  | SVal.prim _, Seg.field _ => exact Except.noConfusion h
  | SVal.prim _, Seg.at _ => exact Except.noConfusion h
  | SVal.struct fields, Seg.field n =>
      simp only [selOf] at h
      cases hl : lookupBy n fields with
      | none => rw [hl] at h; exact Except.noConfusion h
      | some w =>
          rw [hl] at h
          injection h with h'
          subst h'
          simp only [StValue.svalSelect, hl]
          exact Denotes.ofSval w
  | SVal.struct _, Seg.at _ => exact Except.noConfusion h
  | SVal.array elems, Seg.field n =>
      by_cases hn : n = "length"
      · subst hn
        simp only [selOf] at h
        injection h with h'
        subst h'
        exact Denotes.ofPrim (PrimVal.int elems.length)
      · simp [selOf] at h
  | SVal.array elems, Seg.at i =>
      simp only [selOf] at h
      split at h
      · injection h with h'
        subst h'
        rename_i hb
        simp only [StValue.svalSelect, dif_pos hb]
        exact Denotes.ofSval _
      · exact Except.noConfusion h
  | SVal.map _ _, Seg.field _ => exact Except.noConfusion h
  | SVal.map entries d, Seg.at i =>
      simp only [selOf] at h
      cases hl : lookupBy i entries with
      | none =>
          rw [hl] at h
          injection h with h'
          subst h'
          simp only [StValue.svalSelect, hl]
          exact Denotes.ofSval d
      | some w =>
          rw [hl] at h
          injection h with h'
          subst h'
          simp only [StValue.svalSelect, hl]
          exact Denotes.ofSval w

/-- Where the interpreter reads a value, the theory's `find` denotes it. -/
theorem denote_find_of : ∀ {p : List Seg} {t : StValue} {v r : SVal},
    Denotes t v -> v.find p = .ok r -> denoteSt (StValue.find t p) = .ok r := by
  intro p
  induction p with
  | nil =>
      intro t v r ht h
      simp only [SVal.find] at h
      cases h
      exact ht.1
  | cons a rest ih =>
      intro t v r ht h
      rw [find_cons] at h
      cases hc : selOf v a with
      | error e => rw [hc] at h; exact absurd h (by simp [bind, Except.bind])
      | ok c =>
          rw [hc] at h
          simp only [bind, Except.bind] at h
          cases rest with
          | nil =>
              simp only [SVal.find] at h
              cases h
              show denoteSt (StValue.selectSt t a) = _
              rw [ht.2, (Denotes.sel hc).1]
          | cons b rest' =>
              show denoteSt (StValue.find (StValue.selectSt t a) (b :: rest')) = _
              rw [ht.2]
              exact ih (Denotes.sel hc) h

/-- The read half of the bridge. -/
theorem denote_find {v r : SVal} {p : List Seg} (h : v.find p = .ok r) :
    denoteSt (StValue.find (StValue.sval v) p) = .ok r :=
  denote_find_of (Denotes.ofSval v) h

/-! ## Delete

`delAt(storage, p)` reads the subtree at `p`, deletes it and writes it back.
That is `Semantics.storageDeleteUpd`'s shape, and the hypothesis is the one
`delete` always satisfies: its target is a simple place, so the read lands on
a value rather than on the computed `length` of an array (assigning or
deleting `a.length` is a solc error, so no program produces that path). -/

theorem denote_delAt {v cur : SVal} {p : List Seg}
    (h : StValue.find (StValue.sval v) p = StValue.sval cur) :
    denoteSt (StValue.delAt (StValue.sval v) p) = v.save p cur.defaultOf := by
  rw [StValue.delAt, h]
  exact denote_save v p cur.defaultOf

/-! ## Copy

**Upstream's `copyAt`, collapsed.**  solkey `c80a54494c` spells every
storage-to-storage copy `copyAt(storage, p, find<[StValue]>(storage, src))`
where it used to spell it `save(…)`, so that a mapping member of the target
survives.  The interpreter never performs such a copy — solc ≥ 0.7 rejects the
program and `Semantics.tyHasMapping` makes it stuck — and on the fragment it
does perform, the two terms denote the same write.  That is what the theorems
below say, and why every bridge in `Update/Theory.lean` may keep reading a copy
as a `save`.

The side condition is on the **target's current value**, not on the source:
`mergeFields` walks the copied value's members and keeps the old one exactly
where the old one is a mapping, so a mapping-free source is not enough. -/

/-- A non-struct target keeps nothing: the common case, with no hypothesis. -/
theorem mergeKeepMaps_of_not_struct {cur w : SVal} (h : ∀ fs, cur ≠ SVal.struct fs) :
    mergeKeepMaps cur w = w := by
  cases cur with
  | struct fs => exact absurd rfl (h fs)
  | _ => cases w <;> simp [mergeKeepMaps]

/-- A member of a struct body is smaller than the body: what the recursion on
the *target* below needs, since `mergeFields` reaches a member through
`lookupBy` rather than by walking. -/
theorem lookupBy_sizeOf_lt : ∀ (fs : List (Name × SVal)) (n : Name) (o : SVal),
    lookupBy n fs = some o -> sizeOf o < sizeOf fs
  | (m, v) :: rest, n, o, h => by
      simp only [lookupBy] at h
      split at h
      · injection h with h; subst h; simp; omega
      · have := lookupBy_sizeOf_lt rest n o h; simp; omega

/-- A mapping-free target keeps nothing either: `selectStMergeRef` bottoms out
at the copied value everywhere.  The recursion is on the target, because that
is what the hypothesis shrinks along. -/
theorem lookupBy_no_mapping : ∀ (fs : List (Name × SVal)) (n : Name) (o : SVal),
    lookupBy n fs = some o -> fieldsHaveMappingV fs = false -> svalHasMapping o = false
  | (m, u) :: rest, n, o, hl, h => by
      simp only [lookupBy] at hl
      simp only [fieldsHaveMappingV, Bool.or_eq_false_iff] at h
      split at hl
      · injection hl with hl; subst hl; exact h.1
      · exact lookupBy_no_mapping rest n o hl h.2

/-- A member the target holds and that is not itself a mapping contributes
nothing, given that its own merge is trivial. -/
theorem mergeMember_of_no_mapping {o v : SVal} (h : svalHasMapping o = false)
    (hrec : mergeKeepMaps o v = v) : mergeMember (some o) v = v := by
  cases o with
  | map _ _ => simp [svalHasMapping] at h
  | _ => simp only [mergeMember]; exact hrec

/-- A mapping-free target keeps nothing either: `selectStMergeRef` bottoms out
at the copied value everywhere.  The recursion is on the target, because that
is what the hypothesis shrinks along. -/
theorem mergeKeepMaps_of_no_mapping : ∀ (cur w : SVal), svalHasMapping cur = false ->
    mergeKeepMaps cur w = w
  | SVal.struct fo, SVal.struct fn, h => by
      rw [mergeKeepMaps]
      refine congrArg SVal.struct ?_
      induction fn with
      | nil => simp [mergeFields]
      | cons f rest ih =>
          obtain ⟨name, v⟩ := f
          rw [mergeFields, ih]
          refine congrArg (· :: rest) (congrArg (Prod.mk name) ?_)
          cases hl : lookupBy name fo with
          | none => simp [mergeMember]
          | some o =>
              have hsz : sizeOf o < sizeOf fo := lookupBy_sizeOf_lt fo name o hl
              have ho : svalHasMapping o = false :=
                lookupBy_no_mapping fo name o hl (by simpa [svalHasMapping] using h)
              exact mergeMember_of_no_mapping ho (mergeKeepMaps_of_no_mapping o v ho)
  | SVal.struct _, SVal.prim _, _ => by simp [mergeKeepMaps]
  | SVal.struct _, SVal.array _, _ => by simp [mergeKeepMaps]
  | SVal.struct _, SVal.map _ _, _ => by simp [mergeKeepMaps]
  | SVal.prim _, w, _ => by cases w <;> simp [mergeKeepMaps]
  | SVal.array _, w, _ => by cases w <;> simp [mergeKeepMaps]
  | SVal.map _ _, _, h => by simp [svalHasMapping] at h
  termination_by cur _ _ => sizeOf cur
  decreasing_by simp; omega

/-- A non-struct target, or a mapping-free one: the two ways a copy is just
its own value. -/
theorem mergeDen_ok_of_no_mapping {cur w : SVal} (h : svalHasMapping cur = false) :
    mergeDen (.ok cur) (.ok w) = .ok w := by
  rw [mergeDen, mergeKeepMaps_of_no_mapping cur w h]

/-- `copyAt` at a target whose current value carries no mapping denotes the
plain write — the collapse. -/
theorem denote_copyAt {v cur w : SVal} {p : List Seg}
    (hcur : StValue.find (StValue.sval v) p = StValue.sval cur)
    (hnm : svalHasMapping cur = false) :
    denoteSt (StValue.copyAt (StValue.sval v) p (StValue.sval w)) = v.save p w := by
  rw [StValue.copyAt, hcur, StValue.asStruct]
  exact denote_save_of (by rw [denoteSt, denoteSt_sval, denoteSt_sval,
    mergeDen_ok_of_no_mapping hnm]) v p

/-- The fresh-slot case, which needs no side condition at all: nothing was
there to keep.  This is the shape `push` writes — the appended element sits at
the *old* length — and the reason the three push taclets still share one
constructor after `c80a54494c` split their inner terms. -/
theorem denote_copyAt_absent {v w : SVal} {p : List Seg}
    (h : StValue.find (StValue.sval v) p = StValue.dflt) :
    denoteSt (StValue.copyAt (StValue.sval v) p (StValue.sval w)) = v.save p w := by
  rw [StValue.copyAt, h, StValue.asStruct]
  exact denote_save_of (by rw [denoteSt]; rfl) v p

/-! ## Sanity

One concrete instance of each agreement theorem, so a wrong `putAt` or a
wrong `slotOf` shows up here rather than inside an induction. -/

section Sanity

private def alice : SVal :=
  SVal.struct [("account", SVal.struct [("balance", SVal.int 1)]), ("age", SVal.int 34)]

/-- Two ledgers, each a nonce beside a mapping: `copyKeepsMapping.key`'s shape. -/
private def ledgers : SVal :=
  SVal.struct
    [("a", SVal.struct [("n", SVal.int 1), ("m", SVal.map [(1, SVal.int 11)] (SVal.int 0))]),
     ("b", SVal.struct [("n", SVal.int 2), ("m", SVal.map [(1, SVal.int 22)] (SVal.int 0))])]

/-- A deep field write denotes the interpreter's write. -/
example :
    denoteSt (StValue.save (StValue.sval alice)
        [Seg.field "account", Seg.field "balance"] (StValue.sval (SVal.int 10)))
      = alice.save [Seg.field "account", Seg.field "balance"] (SVal.int 10) :=
  denote_save _ _ _

/-- …and computes the value one would write by hand. -/
example :
    denoteSt (StValue.save (StValue.sval alice)
        [Seg.field "account", Seg.field "balance"] (StValue.sval (SVal.int 10)))
      = .ok (SVal.struct [("account", SVal.struct [("balance", SVal.int 10)]),
                          ("age", SVal.int 34)]) := by
  native_decide

/-- An out-of-bounds write reverts on both sides, rather than being stuck on
one of them — the halt has to agree, not just the success. -/
example :
    denoteSt (StValue.save (StValue.sval (SVal.array [SVal.int 1]))
        [Seg.at 5] (StValue.sval (SVal.int 0)))
      = .error .revert := by
  native_decide

/-- A mapping-carrying target: the copy keeps the target's mapping and takes
the value member from the source, so it is *not* the plain write. -/
example :
    denoteSt (StValue.copyAt (StValue.sval ledgers) [Seg.field "b"]
        (StValue.find (StValue.sval ledgers) [Seg.field "a"]))
      = .ok (SVal.struct
          [("a", SVal.struct [("n", SVal.int 1), ("m", SVal.map [(1, SVal.int 11)] (SVal.int 0))]),
           ("b", SVal.struct [("n", SVal.int 1), ("m", SVal.map [(1, SVal.int 22)] (SVal.int 0))])]) := by
  native_decide

/-- …and on a mapping-free target it *is* the plain write — the collapse,
on one store. -/
example :
    denoteSt (StValue.copyAt (StValue.sval alice) [Seg.field "account"]
        (StValue.sval (SVal.struct [("balance", SVal.int 9)])))
      = alice.save [Seg.field "account"] (SVal.struct [("balance", SVal.int 9)]) :=
  denote_copyAt (cur := SVal.struct [("balance", SVal.int 1)]) rfl (by native_decide)

end Sanity

end Theory
end Solidity
