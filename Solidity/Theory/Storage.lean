import Solidity.Theory.Terms

/-!
# `structRules.key` as a term algebra

solkey gives `findSt`, `save`, `selectSt`, `storeSt` and `mtSt` no definition:
they are uninterpreted function symbols (`structHeader.key`, `structRules.key`),
and their whole meaning is the taclet set.  A rule's
`{storage := save(storage, p, se)}` is therefore a *term*, and what the rule
claims about the state is whatever those taclets let one derive about it.

This module is that term algebra.  Every symbol is a total Lean function and
every taclet is a theorem named after it, so the file can be read against
`structRules.key` line by line.

## Two sorts

`solidityDLHeader.key` declares `Prim ⊑ StValue` and `structHeader.key`
`Struct ⊑ StValue`; the symbols are typed on those sorts —
`storeSt(Struct, Field, StValue)`, `selectSt<[α]>(Struct, Field)`,
`findSt<[α]>(Struct, List)`, `save(Struct, List, StValue)`.  Lean has no
subsorting, so the two sorts are a mutual inductive pair with `StValue.st` as
the injection `Struct ⊑ StValue` and `asStruct` as the cast `(Struct) v`
(`castDel` on a `Struct`, `defaultValueStruct` on a `Prim`).  The third
argument of `storeSt` is the supersort, so a member may hold a primitive or a
nested struct; that is what lets `save` store a primitive leaf verbatim.

## Paths are `Seg`

KeY's `Field` sort maps onto `Semantics.Seg` with nothing added: a member
constant is `Seg.field n`, `at(i)` is `Seg.at i`, `size` is
`Seg.field "length"`, and `consr(p, a)` is `p ++ [a]`.  `MapField`/`RefField`
are *not* carried on a segment, and that is the one thing this algebra cannot
say (see "Delete").

## The leaf of a write collapses

Solidity never copies a mapping, and since solc 0.7 it does not even try:
a storage-to-storage assignment of a type that contains a mapping is a compile
error, and solkey's front end rejects it the same way
(`ParserUtils.parseAssignmentMaybe`, `StorageReferenceTypes.containsMapping`).
So the value written at the end of a walk is the value read back:
`save(st, nil, v) ⇝ v` (`saveOnEmpty`), `save`'s spine rule carries the
`isEmpty(flds)` split, and `selectOnSaveEmpty` reads a member of a written
value out of the value.  These are the rules `structRules.key` had before its
`copyAt`/`save` fold (solkey `c80a54494c`/`8c5c69ca25`); the fold's
non-collapsing leaf, read through by member sort so that a struct written over
a location keeps the location's mappings, describes programs no front end
admits, and this package refuses them one level up: `TypedStmt.Assign.mk`
demands a mapping-free type for a storage-to-storage copy and
`stmtTypingOk` states the same predicate.

Reads are **total**, as KeY's are: reading off the store is `st mtSt`, the
`Struct` default, and the caller's cast makes it the sort's default
(`asInt (st mtSt) = 0`).  The bounds test of an array index is a *guard* on
the taclet (`Rules.SideFormula.inBounds`), not part of the read.

## Delete

KeY's `delete` writes a **lazy** marker — `delAt`/`delNode` — whose meaning is
given by the rules that read *through* it, keyed on the field's sort.  Here
`delNode` is eager: a `field` member is deleted in place, an `at` member is
dropped (`selectStDelNodeIndexStruct` reads every index of a deleted node as
`mtSt`), a primitive resets to its sort's default.  What a `Seg` cannot carry
is `MapField`, so `selectStDelNodeMap` — a mapping member survives `delete` —
has no statement in this algebra; the interpreter's `SVal.defaultOf` is where
that behaviour lives.
-/

namespace Solidity
namespace Theory

open Semantics

namespace StValue

open Struct

/-! ## What is here and what is one module down

The sorts, the casts, `selectSt` and `findSt` are `Theory/Terms.lean`: `findSt` on
a `copyMem` view is a `readR` into memory, so it has to be declared in the same
mutual block as the memory readers.  What is here is the rest of
`structRules.key` — the walk a write takes, the taclets, and the four
`findSt`-over-`save` laws that solkey has no rule for. -/

/-! ## The read taclets

`selectSt` and the readers are `Theory/Terms.lean`; these are their `.key`
rules.  They are stated about **`findSt`**, the reader that does not cross into
memory, because that is the one `structRules.key` has: `copyMem` is declared in
`structMemoryRules.key`, and its `findOnCopy` taclet is
`Theory/CrossDomain.lean`'s.  `Struct.find_eq_findSt` is the bridge, and
`Struct.viewFree` its hypothesis. -/

/-- `selectSt<[α]>(storeSt(st, a1, v), a2)`. -/
@[simp] theorem selectOnStore (s : Struct) (a1 a2 : Seg) (v : StValue) :
    selectSt (storeSt s a1 v) a2 = if a1 = a2 then v else selectSt s a2 := rfl

/-- `selectSt<[α]>(mtSt, a) ⇝ defaultValue<[α]>`. -/
@[simp] theorem selectOnEmptyStorage (a : Seg) : selectSt mtSt a = st mtSt := rfl

/-- `findSt<[α]>(st, nil) ⇝ (α) st`. -/
@[simp] theorem findDefinitionEmpty (s : Struct) : findSt s [] = st s := rfl

/-- The paper's `singletonPath`: `⟨f⟩ = ∅·f`.  A path is a `List Seg`, so the
one-element path is `[f]` and the rule is definitional. -/
theorem singletonPath (f : Seg) : ([f] : List Seg) = [] ++ [f] := rfl

/-- `findSt<[α]>(st, cons(a, flds))`, in KeY's own shape. -/
theorem findDefinitionCons (s : Struct) (a : Seg) (flds : List Seg) :
    findSt s (a :: flds) =
      if flds.isEmpty then selectSt s a else findSt (asStruct (selectSt s a)) flds := by
  cases flds <;> rfl

/-- One step of a read, in the form that does not split on the tail. -/
theorem find_cons (s : Struct) (a : Seg) {flds : List Seg} (h : flds ≠ []) :
    findSt s (a :: flds) = findSt (asStruct (selectSt s a)) flds := by
  cases flds with
  | nil => exact absurd rfl h
  | cons b rest => rfl

/-- Reads compose along `++`, through the cast KeY's `findSt<[Struct]>` makes. -/
theorem find_append (s : Struct) (p : List Seg) {q : List Seg} (hq : q ≠ []) :
    findSt s (p ++ q) = findSt (asStruct (findSt s p)) q := by
  induction p generalizing s with
  | nil => simp
  | cons a rest ih =>
      rw [List.cons_append, find_cons _ _ (by simp [hq]), ih]
      cases rest with
      | nil => rfl
      | cons b rest' => rfl

/-- Reading a member of `mtSt` is nothing. -/
theorem find_mtSt {q : List Seg} (hq : q ≠ []) : findSt mtSt q = st mtSt := by
  induction q with
  | nil => exact absurd rfl hq
  | cons a rest ih =>
      cases rest with
      | nil => rfl
      | cons b rest' => exact ih (by simp)

/-! ## `save`

KeY's `save` walks the *store chain*, which is why its taclets split on
`mtSt` versus `storeSt`.  `storeAt` is that walk at one segment — not an
upstream symbol, but the shape `saveOnStoreCons` produces — and `save` puts
the segments together.  The last segment stores the written value verbatim:
`storeSt`'s third argument is the supersort, so a primitive leaf is kept as
itself, which is what `saveOnEmptyPrim` reads back in KeY.  A `save` at `nil`
is the written value at sort `Struct` (`saveOnEmpty`). -/

/-- One segment of the walk: `w` placed at `a`, the chain's other members kept. -/
def storeAt : Struct -> Seg -> StValue -> Struct
  | mtSt, a, w => storeSt mtSt a w
  | storeSt s b v0, a, w =>
      if b = a then storeSt s b w else storeSt (storeAt s a w) b v0
  -- No taclet upstream: a write over a `copyMem` view puts a shadow node
  -- *over* it rather than replacing it, so a read off the written path still
  -- falls through into the view.  Replacing it would make `findSt_save_frame`
  -- false.
  | Struct.copyMem mem id, a, w => storeSt (Struct.copyMem mem id) a w

/-- The walk never produces a view, which is what lets the laws below use the
read taclets on its result. -/
theorem storeAt_ne_copyMem (s : Struct) (a : Seg) (w : StValue) :
    forall mem id, storeAt s a w ≠ Struct.copyMem mem id := by
  intro mem id h
  cases s with
  | mtSt => simp only [storeAt] at h; cases h
  | copyMem _ _ => simp only [storeAt] at h; cases h
  | storeSt s0 b v0 =>
      by_cases hb : b = a
      · rw [storeAt, if_pos hb] at h; cases h
      · rw [storeAt, if_neg hb] at h; cases h

/-- `save(st, p, v)`. -/
def save : Struct -> List Seg -> StValue -> Struct
  | _, [], v => asStruct v
  | s, [a], v => storeAt s a v
  | s, a :: b :: flds, v => storeAt s a (st (save (asStruct (selectSt s a)) (b :: flds) v))

/-- `save(st, nil, v) ⇝ v` (at sort `Struct`). -/
@[simp] theorem saveOnEmpty (s : Struct) (v : StValue) : save s [] v = asStruct v := rfl

theorem save_single (s : Struct) (a : Seg) (v : StValue) :
    save s [a] v = storeAt s a v := rfl

theorem save_cons_cons (s : Struct) (a b : Seg) (flds : List Seg) (v : StValue) :
    save s (a :: b :: flds) v =
      storeAt s a (st (save (asStruct (selectSt s a)) (b :: flds) v)) := rfl

/-- The spine step without the tail split. -/
theorem save_cons (s : Struct) (a : Seg) {flds : List Seg} (h : flds ≠ []) (v : StValue) :
    save s (a :: flds) v = storeAt s a (st (save (asStruct (selectSt s a)) flds v)) := by
  cases flds with
  | nil => exact absurd rfl h
  | cons b rest => rfl

/-- `save(mtSt, cons(a, flds), v)`. -/
theorem saveOnEmptyStorage (a : Seg) (flds : List Seg) (v : StValue) :
    save mtSt (a :: flds) v =
      storeSt mtSt a (if flds.isEmpty then v else st (save mtSt flds v)) := by
  cases flds <;> rfl

/-- `save(storeSt(st, a1, v0), cons(a2, flds), v1)`, in KeY's own shape:
`(Struct) v0` is `asStruct v0`. -/
theorem saveOnStoreCons (s : Struct) (a1 a2 : Seg) (flds : List Seg) (v0 v1 : StValue) :
    save (storeSt s a1 v0) (a2 :: flds) v1 =
      if a1 = a2 then
        storeSt s a1 (if flds.isEmpty then v1 else st (save (asStruct v0) flds v1))
      else storeSt (save s (a2 :: flds) v1) a1 v0 := by
  by_cases h : a1 = a2 <;> cases flds <;> simp [save, storeAt, selectSt, h]

/-- Reading one selector out of the walk. -/
theorem selectSt_storeAt (s : Struct) (a1 a2 : Seg) (w : StValue) :
    selectSt (storeAt s a1 w) a2 = if a1 = a2 then w else selectSt s a2 := by
  induction s using Struct.inductionOn with
  | h0 => by_cases h : a1 = a2 <;> simp [storeAt, selectSt, h]
  | h1 s b v ih =>
      by_cases hb : b = a1
      · subst hb
        by_cases h : b = a2 <;> simp [storeAt, selectSt, h]
      · by_cases h : b = a2
        · subst h
          simp [storeAt, selectSt, hb, Ne.symm hb]
        · simp only [storeAt, if_neg hb, selectSt, if_neg h, ih]
  -- Over a view the walk is a shadow `storeSt`, so this is `selectOnStore`.
  | h2 mem id => by_cases h : a1 = a2 <;> simp [storeAt, selectSt, h]

/-! ### `selectOnSaveCons`

The taclet that does the work: reading one selector out of a write.  The
fundamentals repository proves its analogue (`selectSave`) under an `isStruct`
well-formedness hypothesis; here the definitions are total, so there is none.
KeY's `cast<[α]>(save(…, flds, v))` is the `isEmpty(flds)` split below: at the
last segment the written value itself, before it the walk continued. -/

/-- `selectSt<[α]>(save(st, cons(a1, flds), v), a2)`. -/
theorem selectOnSaveCons (s : Struct) (a1 a2 : Seg) (flds : List Seg) (v : StValue) :
    selectSt (save s (a1 :: flds) v) a2 =
      if a1 = a2 then
        (if flds.isEmpty then v else st (save (asStruct (selectSt s a1)) flds v))
      else selectSt s a2 := by
  cases flds <;> simp [save, selectSt_storeAt]

/-- `selectSt<[α]>(save(st, nil, v), a) ⇝ selectSt<[α]>((Struct) v, a)`. -/
theorem selectOnSaveEmpty (s : Struct) (v : StValue) (a : Seg) :
    selectSt (save s [] v) a = selectSt (asStruct v) a := rfl

/-- `saveOnEmptyPrim` at `int`: the leaf a walk stores is the written value. -/
@[simp] theorem saveOnEmptyPrimInt (s : Struct) (a : Seg) (v : StValue) :
    asInt (selectSt (save s [a] v) a) = asInt v := by
  simp [save, selectSt_storeAt]

/-- …and at `bool`. -/
@[simp] theorem saveOnEmptyPrimBool (s : Struct) (a : Seg) (v : StValue) :
    asBool (selectSt (save s [a] v) a) = asBool v := by
  simp [save, selectSt_storeAt]

/-! ## `findSt` over `save`

solkey has no `findSt(save(…), …)` taclet: a read of a write is reached by
`findDefinitionCons` unfolding `findSt` into `selectSt` and `selectOnSaveCons`
then commuting one selector past the write.  The four laws below package
those steps, one per way a read path can lie against a written one — the
same path, below it, above it, or off it.  `Semantics` has only the first
(`SemanticsProperties.SVal.find_save_same`), and only in the form that
presupposes the write succeeded. -/

/-- **Reading exactly the write.**  No well-formedness of the store or the
path: totality buys both away. -/
theorem find_save_same (s : Struct) {p : List Seg} (hp : p ≠ []) (v : StValue) :
    findSt (save s p v) p = v := by
  induction p generalizing s with
  | nil => exact absurd rfl hp
  | cons a rest ih =>
      cases rest with
      | nil => simp [save, findSt, selectSt_storeAt]
      | cons b rest' =>
          rw [save_cons_cons, find_cons _ _ (by simp), selectSt_storeAt, if_pos rfl, asStruct_st]
          exact ih _ (by simp)

/-- …which at `int` is `saveOnEmptyPrim` at the end of a walk. -/
theorem find_save_same_asInt (s : Struct) {p : List Seg} (hp : p ≠ []) (v : StValue) :
    asInt (findSt (save s p v) p) = asInt v := by
  rw [find_save_same s hp]

/-- **Reading below the write.**  Everything under the written path comes out
of the written value, cast to `Struct` as KeY's `findSt<[Struct]>` does. -/
theorem find_save_extends (s : Struct) {p q : List Seg} (hp : p ≠ []) (hq : q ≠ [])
    (v : StValue) :
    findSt (save s p v) (p ++ q) = findSt (asStruct v) q := by
  induction p generalizing s with
  | nil => exact absurd rfl hp
  | cons a rest ih =>
      cases rest with
      | nil =>
          rw [List.singleton_append, save_single, find_cons _ _ hq, selectSt_storeAt, if_pos rfl]
      | cons b rest' =>
          rw [List.cons_append, save_cons_cons, find_cons _ _ (by simp), selectSt_storeAt,
            if_pos rfl, asStruct_st]
          exact ih _ (by simp)

/-- **Reading above the write.**  A prefix of the written path reads the
write pushed down to what is left of it. -/
theorem find_save_prefix (s : Struct) (q : List Seg) {r : List Seg} (hr : r ≠ [])
    (v : StValue) :
    findSt (save s (q ++ r) v) q = st (save (asStruct (findSt s q)) r v) := by
  induction q generalizing s with
  | nil => rfl
  | cons a q' ih =>
      cases q' with
      | nil =>
          rw [List.singleton_append, save_cons _ _ hr]
          simp [findSt, selectSt_storeAt]
      | cons b q'' =>
          rw [List.cons_append, save_cons _ _ (by simp), find_cons _ _ (by simp), selectSt_storeAt,
            if_pos rfl, asStruct_st, ih]
          rfl

/-- The read path leaves the written one: they agree up to some point and
then differ.  Neither a prefix nor an extension diverges — `[]` is a prefix
of everything, which is why both `nil` arms are `false`. -/
def diverges : List Seg -> List Seg -> Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: p, b :: q => if a = b then diverges p q else true

/-- **The frame.**  A read off the written path does not see the write — the
`\else` branch of `selectOnSaveCons`, lifted from one selector to a path. -/
theorem find_save_frame (s : Struct) (v : StValue) :
    ∀ p q : List Seg, diverges p q = true -> findSt (save s p v) q = findSt s q := by
  intro p
  induction p generalizing s with
  | nil => intro q h; simp [diverges] at h
  | cons a p' ih =>
      intro q h
      cases q with
      | nil => simp [diverges] at h
      | cons b q' =>
          by_cases hab : a = b
          · subst hab
            simp only [diverges] at h
            have hq' : q' ≠ [] := by
              cases q' with
              | nil => cases p' <;> simp [diverges] at h
              | cons _ _ => simp
            cases p' with
            | nil => simp [diverges] at h
            | cons c p'' =>
                rw [save_cons_cons, find_cons _ _ hq', find_cons _ _ hq', selectSt_storeAt,
                  if_pos rfl, asStruct_st, ih _ _ h]
          · cases p' with
            | nil =>
                rw [save_single, findDefinitionCons, findDefinitionCons, selectSt_storeAt,
                  if_neg hab]
            | cons c p'' =>
                rw [save_cons_cons, findDefinitionCons, findDefinitionCons, selectSt_storeAt,
                  if_neg hab]

/-! ## The delete family

KeY's `delete` writes a lazy marker — `delAt`/`delNode` — read through by
`selectStDelNode{Map,Ref,IndexStruct,Default}`, keyed on the field's sort.
Eager here: the three sorts a `Seg` and a `PrimVal` do carry — `at(i)`, a
reference (`st`), a primitive — give the three rules that can be stated;
`MapField` is the one they cannot (module docstring). -/

/-- `defaultValue<[alphaPrim]>`, read off the value's own sort. -/
def primDefault : PrimVal -> PrimVal
  | .int _ => .int 0
  | .bool _ => .bool false

mutual
  /-- `delNode(st)`: a `field` member deleted in place, an `at` member dropped. -/
  def delNode : Struct -> Struct
    | mtSt => mtSt
    | storeSt s (Seg.field f) v => storeSt (delNode s) (Seg.field f) (delValue v)
    | storeSt s (Seg.at _) _ => delNode s
    -- No taclet upstream.  `delNode` is eager here, so it cannot walk a view
    -- whose members it does not know; every member of a deleted node reads
    -- its default, which is what `mtSt` says.
    | Struct.copyMem _ _ => mtSt

  /-- `delValue<[α]>(v)`: `delValueStruct` on a `Struct`, `delValueDefault` on a `Prim`. -/
  def delValue : StValue -> StValue
    | prim q => prim (primDefault q)
    | st s => st (delNode s)
end

/-- `delAt(st, p)`: the value at `p`, deleted in place. -/
def delAt (s : Struct) (p : List Seg) : Struct :=
  save s p (delValue (findSt s p))

/-- `delValue<[Struct]>(st) ⇝ delNode(st)`. -/
theorem delValueStruct (s : Struct) : delValue (st s) = st (delNode s) := rfl

/-- `delValue<[alphaPrim]>(x) ⇝ defaultValue<[alphaPrim]>`. -/
theorem delValueDefault (q : PrimVal) : delValue (prim q) = prim (primDefault q) := rfl

/-- …at `int`. -/
@[simp] theorem delValueDefault_asInt (q : PrimVal) : asInt (delValue (prim q)) = 0 := by
  cases q <;> rfl

/-- The paper's `delValueCast` at `Struct`: `(Struct) delValue<[StValue]>(v) ⇝
delValue<[Struct]>((Struct) v)`.  The cast a later read carries is pushed
through the reset, so the sort the reader supplies reaches it. -/
theorem delValueCast (v : StValue) : asStruct (delValue v) = delNode (asStruct v) := by
  cases v <;> rfl

/-- …at `int`: `(int) delValue<[StValue]>(v) ⇝ delValue<[int]>((int) v)`, and the
right-hand side is `delValueDefault`. -/
theorem delValueCast_asInt (v : StValue) : asInt (delValue v) = 0 := by
  cases v with
  | prim q => cases q <;> rfl
  | st _ => rfl

/-- …at `bool`. -/
theorem delValueCast_asBool (v : StValue) : asBool (delValue v) = false := by
  cases v with
  | prim q => cases q <;> rfl
  | st _ => rfl

/-- `delAt(st, nil) ⇝ delNode(st)`. -/
@[simp] theorem delAtEmpty (s : Struct) : delAt s [] = delNode s := rfl

/-- `selectStDelNodeRef` (a reference member is deleted recursively) and
`selectStDelNodeDefault` (a value member reads its default) in one: a delete
commutes with every `field` selector.  Unconditional — an absent member is
`st mtSt` on both sides. -/
theorem selectStDelNodeRef (s : Struct) (f : Name) :
    selectSt (delNode s) (Seg.field f) = delValue (selectSt s (Seg.field f)) := by
  induction s using Struct.inductionOn with
  | h0 => rfl
  | h1 s b v ih =>
      cases b with
      | field g => by_cases h : g = f <;> simp [delNode, selectSt, h, ih]
      | «at» i => simp [delNode, selectSt, ih]
  -- Both sides are `st mtSt`: the delete flattens the view, and a member of
  -- the flattened view is deleted to the same default.
  | h2 mem id => rfl

/-- `selectStDelNodeDefault` at `int`. -/
theorem selectStDelNodeDefault (s : Struct) (f : Name) :
    asInt (selectSt (delNode s) (Seg.field f)) = 0 := by
  rw [selectStDelNodeRef]
  cases selectSt s (Seg.field f) with
  | prim q => cases q <;> rfl
  | st _ => rfl

/-- `selectStDelNodeIndexStruct`: an index into a deleted node is `mtSt`. -/
theorem selectStDelNodeIndexStruct (s : Struct) (i : Int) :
    selectSt (delNode s) (Seg.at i) = st mtSt := by
  induction s using Struct.inductionOn with
  | h0 => rfl
  | h1 s b v ih =>
      cases b with
      | field g => simp [delNode, ih]
      | «at» j => simp [delNode, ih]
  | h2 mem id => rfl

/-- `selectOnDelAtCons`: one selector out of a delete, through `selectOnSaveCons`. -/
theorem selectOnDelAtCons (s : Struct) (a1 a2 : Seg) (flds : List Seg) :
    selectSt (delAt s (a1 :: flds)) a2 =
      if a1 = a2 then
        (if flds.isEmpty then delValue (selectSt s a1)
         else st (delAt (asStruct (selectSt s a1)) flds))
      else selectSt s a2 := by
  unfold delAt
  rw [selectOnSaveCons]
  cases flds <;> simp [findSt]

/-! ### `findSt` over `delAt`

`delAt` *is* a `save` of the deleted value (its definition), so the two path
laws the paper states for it are the corresponding `findSt`-over-`save` laws with
that value substituted.  They are stated rather than left to the reader because
they are the two rules `sections/signature.tex` names, and a chain writes a
rule on its arrow. -/

/-- **`findDelAt`** — reading exactly the deleted path gives the deleted
value. -/
theorem find_delAt_same (s : Struct) {p : List Seg} (hp : p ≠ []) :
    findSt (delAt s p) p = delValue (findSt s p) :=
  find_save_same s hp _

/-- **`findDelAtOutside`** — a read that leaves the deleted path does not see
the delete, the frame of `find_save_frame`. -/
theorem find_delAt_frame (s : Struct) {p q : List Seg} (h : diverges p q = true) :
    findSt (delAt s p) q = findSt s q :=
  find_save_frame s _ p q h

/-! ## Sanity

The worked examples of the fundamentals repository, in this vocabulary.
They are here to catch a wrong definition before `Corpus/Wp/Rules.lean`
builds on one. -/

section Sanity

private def acct : Seg := Seg.field "account"
private def bal : Seg := Seg.field "balance"
private def age : Seg := Seg.field "age"
private def alice : Seg := Seg.field "alice"
private def bob : Seg := Seg.field "bob"

/-- `alice.account.balance = 10; result = alice.account.balance` — the
fundamentals' `findOnSaveEx`, over an arbitrary store. -/
example (s : Struct) :
    asInt (findSt (save s [acct, bal] (int 10)) [acct, bal]) = 10 := by
  rw [find_save_same_asInt s (by simp)]; rfl

/-- `alice.account.balance = 1; alice.age` — `storage-field-disjoint-fields.key`:
the write is invisible to the other member. -/
example (s : Struct) :
    findSt (save s [acct, bal] (int 1)) [age] = findSt s [age] :=
  find_save_frame s (int 1) [acct, bal] [age] (by decide)

/-- Reading *above* a write sees the write pushed down into the subtree. -/
example (s : Struct) :
    findSt (save s [acct, bal] (int 7)) [acct]
      = st (save (asStruct (findSt s [acct])) [bal] (int 7)) :=
  find_save_prefix s [acct] (by simp) (int 7)

/-- A concrete store: `bob.age = 7; alice = bob; bob.age = 9` leaves
`alice.age = 7` — a copy is by value, `findSt<[Struct]>` being the cast. -/
example :
    let s1 := save mtSt [bob, age] (int 7)
    let s2 := save s1 [alice] (st (asStruct (findSt s1 [bob])))
    findSt (save s2 [bob, age] (int 9)) [alice, age] = int 7 := by
  decide

/-- `delete` on a struct resets its members at every depth. -/
example :
    delNode (storeSt (storeSt mtSt (Seg.field "owner") (int 3))
        (Seg.field "inner") (st (storeSt mtSt (Seg.field "n") (int 5))))
      = storeSt (storeSt mtSt (Seg.field "owner") (int 0))
          (Seg.field "inner") (st (storeSt mtSt (Seg.field "n") (int 0))) := by
  decide

end Sanity

end StValue
end Theory
end Solidity
