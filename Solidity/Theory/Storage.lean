import Solidity.DecEq

/-!
# `structRules.key` as a term algebra

solkey gives `find`, `save`, `selectSt`, `storeSt` and `mtSt` no definition:
they are uninterpreted function symbols (`structHeader.key`), and their whole
meaning is the taclet set of `structRules.key`.  A rule's
`{storage := save(storage, p, se)}` is therefore a *term*, and what the rule
claims about the state is whatever those taclets let one derive about it.

This module is that term algebra.  Every symbol is a total Lean function and
every taclet is a theorem named after it, so the file can be read against
`structRules.key` line by line.  `Theory/Denote.lean` then maps a term to the
interpreter's `SVal` and proves the two agree; `Update/Theory.lean` reads a
rule's `UpdTerm` as a term of this algebra and gets the rule's stated update
and the interpreter's update equal.

## Paths are `Seg`

KeY's `Field` sort maps onto `Semantics.Seg` with nothing added:
a member constant is `Seg.field n`, `at(i)` is `Seg.at i`, `size` is
`Seg.field "length"` (`SVal.find`'s length arm), and `consr(p, a)` is
`p ++ [a]`.  `MapField`/`RefField` are deliberately *not* carried on a
segment: KeY's delete rules discriminate on the field's sort where the
interpreter's `SVal.defaultOf` discriminates on the value's shape, and
`docs/lean-key-rule-map.md` records those as the same semantics.  Keeping one
path type on both sides is what keeps `Denote.lean` short.

## The `sval` leaf

`StValue.sval` embeds an interpreter value as an opaque leaf.  That is what
makes this a theory of terms *over a concrete pre-state* with no reification
lemma: `Update/Theory.lean` roots every update term at `sval s.storage-tree`,
which is exactly KeY's program variable `storage`, and a taclet theorem holds
with `sval` leaves because it holds for an arbitrary leaf.

## Where the definitions are eager and KeY is lazy

KeY's reads are *sort-indexed* (`selectSt<[alpha]>`, `defaultValue<[alpha]>`)
and its casts are underspecified on ill-sorted arguments.  Here `dflt` stands
for the sort-free default (`memoryRules.key`'s own `defVal`), resolved by a
cast at the point of use (`asInt`, `asBool`), and `asStruct` sends a
non-`Struct` to `mtSt`.  Nothing observable depends on that choice:
`selectSt` of a non-`Struct` is `dflt` either way (`selectSt_asStruct`).

Reads here are **total**, as KeY's are: an out-of-bounds `find` is `dflt`, not
a revert.  The bounds test is a *guard* on the taclet (`Rules.SideFormula.inBounds`),
not part of the read, and it reappears as a hypothesis in `Denote.lean`.
-/

namespace Solidity
namespace Theory

open Semantics

/-- A term of solkey's storage theory (`solidityDLHeader.key`:
`Prim, Struct ⊑ StValue`). -/
inductive StValue where
  /-- `Prim`: an int or a bool. -/
  | prim (p : PrimVal)
  /-- `defaultValue<[α]>` / `defVal`: the sort-free default, resolved on read. -/
  | dflt
  /-- `\unique Struct mtSt`. -/
  | mtSt
  /-- `storeSt(st, a, v)`. -/
  | storeSt (st : StValue) (a : Seg) (v : StValue)
  /-- An interpreter value as an opaque leaf — see the module docstring. -/
  | sval (v : SVal)
  deriving Repr, DecidableEq

namespace StValue

@[match_pattern] abbrev int (v : Int) : StValue := .prim (.int v)
@[match_pattern] abbrev bool (b : Bool) : StValue := .prim (.bool b)

/-! ## Casts

`cast<[Struct]>` and the `Prim` casts of `cast.key`/`memoryRules.key`.  KeY
deletes a cast on a well-sorted argument (`castDel`); these are total, so the
ill-sorted cases get the sort's default, which is `defaultValueInt` /
`defaultValueBool` / `defaultValueStruct` read as functions. -/

/-- `(Struct) t`. -/
def asStruct : StValue -> StValue
  | storeSt st a v => storeSt st a v
  | sval v => sval v
  | _ => mtSt

/-- `(int) t` — `defValResolve` at `int`, then `defaultValueInt`. -/
def asInt : StValue -> Int
  | prim (PrimVal.int v) => v
  | sval (SVal.int v) => v
  | _ => 0

/-- `(bool) t` — `defValResolve` at `bool`, then `defaultValueBool`. -/
def asBool : StValue -> Bool
  | prim (PrimVal.bool b) => b
  | sval (SVal.bool b) => b
  | _ => false

/-! ## `selectSt` -/

/-- One selector step inside an opaque interpreter leaf.  This is
`Semantics.SVal.find` at a single segment, with its `revert`/`stuck` arms
read as `dflt`: KeY's reads are total and the bounds test is the taclet's
guard, not the read. -/
def svalSelect (v : SVal) (a : Seg) : StValue :=
  match v, a with
  | SVal.struct fields, Seg.field n =>
      match lookupBy n fields with
      | some w => sval w
      | none => dflt
  | SVal.array elems, Seg.field "length" => prim (PrimVal.int elems.length)
  | SVal.array elems, Seg.at i =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then sval (elems.get ⟨i.toNat, h.2⟩)
      else dflt
  | SVal.map entries d, Seg.at i =>
      match lookupBy i entries with
      | some w => sval w
      | none => sval d
  | _, _ => dflt

/-- `selectSt<[α]>(st, a)`. -/
def selectSt : StValue -> Seg -> StValue
  | mtSt, _ => dflt
  | storeSt st a1 v, a2 => if a1 = a2 then v else selectSt st a2
  | sval v, a => svalSelect v a
  | prim _, _ => dflt
  | dflt, _ => dflt

/-! ## `save`

KeY's `save` walks the *store chain*, which is why its taclets split on
`mtSt` versus `storeSt`: the result is a chain in which the written path is
outermost-visible.  The `sval` arm has no KeY counterpart because KeY's
`storage` is a program variable, not a value; it expands the leaf one level,
which is the same shape `saveOnStoreCons` produces. -/

def save : StValue -> List Seg -> StValue -> StValue
  | _, [], v => v
  | storeSt st a1 v0, a2 :: flds, v1 =>
      if a1 = a2 then storeSt st a1 (save (asStruct v0) flds v1)
      else storeSt (save st (a2 :: flds) v1) a1 v0
  | sval sv, a :: flds, v =>
      storeSt (sval sv) a (save (asStruct (svalSelect sv a)) flds v)
  | mtSt, a :: flds, v => storeSt mtSt a (save mtSt flds v)
  | prim _, a :: flds, v => storeSt mtSt a (save mtSt flds v)
  | dflt, a :: flds, v => storeSt mtSt a (save mtSt flds v)
termination_by st flds _ => (flds.length, st)

/-! ## `find` -/

/-- `find<[α]>(st, flds)`.  The one-segment arm is KeY's `isEmpty(flds)`
branch, and it is not the same as recursing: the last step reads at the
*caller's* sort, so a primitive leaf survives it. -/
def find : StValue -> List Seg -> StValue
  | st, [] => st
  | st, [a] => selectSt st a
  | st, a :: b :: flds => find (selectSt st a) (b :: flds)

/-! ## The taclets of `structRules.key`

One theorem per taclet, in the file's order.  Those that are the defining
equations are `rfl`; the two that are not are `saveOnStoreCons` and
`findDefinitionCons`, whose KeY form carries an `isEmpty(flds)` split that
`saveOnEmpty` already accounts for, and `selectOnSaveCons`, which is the
real content. -/

/-- `defaultValue<[Struct]> ⇝ mtSt`. -/
@[simp] theorem defaultValueStruct : asStruct dflt = mtSt := rfl

/-- `selectSt<[α]>(storeSt(st, a1, v), a2)`. -/
@[simp] theorem selectOnStore (st : StValue) (a1 a2 : Seg) (v : StValue) :
    selectSt (storeSt st a1 v) a2 =
      if a1 = a2 then v else selectSt st a2 := rfl

/-- `selectSt<[α]>(mtSt, a) ⇝ defaultValue<[α]>`. -/
@[simp] theorem selectOnEmptyStorage (a : Seg) : selectSt mtSt a = dflt := rfl

/-- `save(mtSt, nil, v) ⇝ v`. -/
@[simp] theorem saveOnEmptyStorageEmpty (v : StValue) : save mtSt [] v = v := by
  simp [save]

/-- `save(mtSt, cons(a, flds), v)`. -/
@[simp] theorem saveOnEmptyStorage (a : Seg) (flds : List Seg) (v : StValue) :
    save mtSt (a :: flds) v = storeSt mtSt a (save mtSt flds v) := by
  simp [save]

/-- `save(storeSt(st, a, v0), nil, v1) ⇝ v1`. -/
@[simp] theorem saveOnStoreEmpty (st : StValue) (a : Seg) (v0 v1 : StValue) :
    save (storeSt st a v0) [] v1 = v1 := by
  simp [save]

/-- `save(st, nil, v) ⇝ v` — the lazy rule, and the one the two above are
instances of. -/
@[simp] theorem saveOnEmpty (st : StValue) (v : StValue) : save st [] v = v := by
  cases st <;> simp [save]

/-- `save(storeSt(st, a1, v0), cons(a2, flds), v1)`, in KeY's own shape: the
inner `isEmpty(flds)` split is `saveOnEmpty`, so the definition drops it. -/
theorem saveOnStoreCons (st : StValue) (a1 a2 : Seg) (flds : List Seg)
    (v0 v1 : StValue) :
    save (storeSt st a1 v0) (a2 :: flds) v1 =
      (if a1 = a2 then
        storeSt st a1 (if flds.isEmpty then v1 else save (asStruct v0) flds v1)
      else storeSt (save st (a2 :: flds) v1) a1 v0) := by
  cases flds <;> simp [save]

/-- `find<[α]>(st, nil) ⇝ (α) st`. -/
@[simp] theorem findDefinitionEmpty (st : StValue) : find st [] = st := rfl

/-- `find<[α]>(st, cons(a, flds))`, in KeY's own shape.  The `isEmpty` branch
is not decoration: the last step reads at the caller's sort, so a primitive
leaf survives it where `selectSt<[Struct]>` would not. -/
theorem findDefinitionCons (st : StValue) (a : Seg) (flds : List Seg) :
    find st (a :: flds) =
      if flds.isEmpty then selectSt st a else find (selectSt st a) flds := by
  cases flds <;> rfl

/-- `selectSt<[α]>(save(st, nil, v), a)`, in the shape its `\find` binds.

Upstream's `\replacewith` is `selectSt(save(st, flds, v), a)` with an `flds`
its `\find` never binds — the intended statement is this one
(`docs/solkey-feedback.md`). -/
@[simp] theorem selectOnSaveEmpty (st : StValue) (v : StValue) (a : Seg) :
    selectSt (save st [] v) a = selectSt v a := by rw [saveOnEmpty]

/-! ### `selectOnSaveCons`

The taclet that does the work, and the reason this module exists: reading one
selector out of a write.  The fundamentals repository proves its analogue
(`selectSave`) under an `isStruct` well-formedness hypothesis; here the
definitions are total, so there is none. -/

/-- A cast to `Struct` is invisible to a selector. -/
@[simp] theorem selectSt_asStruct (t : StValue) (a : Seg) :
    selectSt (asStruct t) a = selectSt t a := by
  cases t <;> rfl

/-- …and therefore to a write. -/
@[simp] theorem save_asStruct (t : StValue) (p : List Seg) (v : StValue) :
    save (asStruct t) p v = save t p v := by
  cases t <;> cases p <;> simp [save, asStruct]

/-- `selectSt<[α]>(save(st, cons(a1, flds), v), a2)`. -/
theorem selectOnSaveCons (st : StValue) (a1 a2 : Seg) (flds : List Seg)
    (v : StValue) :
    selectSt (save st (a1 :: flds) v) a2 =
      if a1 = a2 then save (asStruct (selectSt st a1)) flds v
      else selectSt st a2 := by
  induction st with
  | storeSt st' b w ih =>
      by_cases hb : b = a1
      · subst hb
        by_cases h : b = a2 <;> simp [save, selectSt, h]
      · by_cases h : b = a2
        · subst h
          simp [save, selectSt, hb, Ne.symm hb]
        · simp only [save, if_neg hb, selectSt, if_neg h, ih]
  | _ => by_cases h : a1 = a2 <;> simp [save, selectSt, h]

/-! ## `find` over `save`

solkey has no `find(save(…), …)` taclet: a read of a write is reached by
`findDefinitionCons` unfolding `find` into `selectSt` and `selectOnSaveCons`
then commuting one selector past the write.  Those four steps are what the
laws below package, one per way a read path can lie against a written one —
the same path, below it, above it, or off it.  `Semantics` has only the first
(`SemanticsProperties.SVal.find_save_same`), and only in the form that
presupposes the write succeeded. -/

/-- A cast to `Struct` is invisible to a non-empty read. -/
theorem find_asStruct (t : StValue) {q : List Seg} (hq : q ≠ []) :
    find (asStruct t) q = find t q := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a rest => cases rest <;> simp [findDefinitionCons]

/-- **Reading below the write.** Everything at or under the written path comes
out of the written value. -/
theorem find_save_extends (st : StValue) (p q : List Seg) (v : StValue) :
    find (save st p v) (p ++ q) = find v q := by
  induction p generalizing st with
  | nil => simp
  | cons a rest ih =>
      rw [List.cons_append, findDefinitionCons, selectOnSaveCons, if_pos rfl,
        save_asStruct]
      cases hrq : rest ++ q with
      | nil =>
          have hr : rest = [] := List.eq_nil_of_append_eq_nil hrq |>.1
          have hq : q = [] := List.eq_nil_of_append_eq_nil hrq |>.2
          subst hr; subst hq; simp_all
      | cons _ _ => rw [if_neg (by simp), ← hrq, ih]

/-- **Reading exactly the write** — `find(save(st, p, v), p) = v`, with no
side condition at all.  The fundamentals repository's `findOnSave` needs a
well-formed path and a well-formed store; totality buys both away. -/
theorem find_save_same (st : StValue) (p : List Seg) (v : StValue) :
    find (save st p v) p = v := by
  have := find_save_extends st p [] v
  simpa using this

/-- **Reading above the write.** A prefix of the written path reads the
written subtree, i.e. the write pushed down to what is left of it. -/
theorem find_save_prefix (st : StValue) (q r : List Seg) (v : StValue) :
    find (save st (q ++ r) v) q = save (find st q) r v := by
  induction q generalizing st with
  | nil => simp
  | cons a q' ih =>
      rw [List.cons_append, findDefinitionCons, selectOnSaveCons, if_pos rfl,
        save_asStruct]
      cases q' with
      | nil => simp [findDefinitionCons]
      | cons b q'' => rw [if_neg (by simp), ih]; rfl

/-- The read path leaves the written one: they agree up to some point and
then differ.  Neither a prefix nor an extension diverges — `[]` is a prefix
of everything, which is why both `nil` arms are `false`. -/
def diverges : List Seg -> List Seg -> Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: p, b :: q => if a = b then diverges p q else true

/-- **The frame.** A read off the written path does not see the write — the
`\else` branch of `selectOnSaveCons`, lifted from one selector to a whole
path.  This is the law `Semantics` was missing entirely. -/
theorem find_save_frame (st : StValue) (v : StValue) :
    ∀ p q : List Seg, diverges p q = true -> find (save st p v) q = find st q := by
  intro p
  induction p generalizing st with
  | nil => intro q h; simp [diverges] at h
  | cons a p' ih =>
      intro q h
      cases q with
      | nil => simp [diverges] at h
      | cons b q' =>
          by_cases hab : a = b
          · subst hab
            -- Agreed here, so the divergence is further down; a `nil` tail
            -- cannot diverge, which is what makes the read non-empty.
            simp only [diverges] at h
            have hq' : q' ≠ [] := by
              cases q' with
              | nil => cases p' <;> simp [diverges] at h
              | cons _ _ => simp
            rw [findDefinitionCons, findDefinitionCons, selectOnSaveCons,
              if_pos rfl, save_asStruct,
              if_neg (by simpa using hq'), if_neg (by simpa using hq'), ih _ _ h]
          · -- Off the path at the very first segment: `selectOnSaveCons`'s
            -- `\else` branch makes the two sides the same term.
            rw [findDefinitionCons, findDefinitionCons, selectOnSaveCons,
              if_neg hab]

/-! ## The delete family

KeY's `delete` writes a **lazy** marker — `delAt`/`delNode` — whose meaning is
given by the four rules that read *through* it (`selectStDelNode{Map,Ref,
IndexStruct,Default}`): a mapping member survives a delete, a reference member
is deleted recursively, an index into a deleted node is empty, and a value
member reads its default.  That is Solidity's own `delete`, and the
interpreter implements it eagerly as `SVal.defaultOf` — which
`docs/lean-key-rule-map.md` already records as the matching semantics.

Eager here too, so the four read-through rules become theorems rather than
definitions.  The one place the shape matters is a *chain*: `delValue` has to
dispatch on what the chain is built over, because `defaultOf` empties an
array, keeps a mapping and recurses into a struct, and a chain's own
constructors do not say which it is. -/

/-- The value a store chain is built over. -/
def base : StValue -> StValue
  | storeSt st _ _ => base st
  | t => t

/-- The chain denotes a mapping: `delete` leaves it alone. -/
def isMapping (t : StValue) : Bool :=
  match base t with
  | sval (SVal.map _ _) => true
  | _ => false

/-- The chain denotes an array: `delete` empties it, writes and all. -/
def isArray (t : StValue) : Bool :=
  match base t with
  | sval (SVal.array _) => true
  | _ => false

/-- `delValue<[α]>(v)` and `delNode(st)` at once — KeY keeps them apart by
sort (`delValueStruct` is the bridge between them), which a total function
does not need to. -/
def delValue : StValue -> StValue
  | sval v => sval v.defaultOf
  | prim _ => dflt
  | dflt => dflt
  | mtSt => mtSt
  | storeSt st a v =>
      if isMapping (storeSt st a v) then storeSt st a v
      else if isArray (storeSt st a v) then sval (SVal.array [])
      else storeSt (delValue st) a (delValue v)

/-- `delNode(st)`: `delValue` at sort `Struct`. -/
abbrev delNode : StValue -> StValue := delValue

/-- `delAt(st, p)`: the value at `p`, deleted in place.  KeY writes the
marker and lets reads push it down; the eager reading is the write of the
deleted subtree, which is `Semantics.storageDeleteUpd`'s shape exactly. -/
def delAt (st : StValue) (p : List Seg) : StValue :=
  save st p (delValue (find st p))

/-- `delValue<[Struct]>(st) ⇝ delNode(st)`. -/
theorem delValueStruct (st : StValue) : delValue st = delNode st := rfl

/-- `delValue<[alphaPrim]>(x) ⇝ defaultValue<[alphaPrim]>`. -/
@[simp] theorem delValueDefault (p : PrimVal) : delValue (prim p) = dflt := rfl

/-- `delAt(st, nil) ⇝ delNode(st)`. -/
@[simp] theorem delAtEmpty (st : StValue) : delAt st [] = delNode st := by
  simp [delAt]

/-- `selectStDelNodeMap`: a mapping member reads through a delete
untouched — real Solidity semantics, and why `SVal.defaultOf` has a `map`
arm that returns its argument. -/
theorem selectStDelNodeMap {t : StValue} (h : isMapping t = true) (a : Seg) :
    selectSt (delValue t) a = selectSt t a := by
  cases t with
  | sval v =>
      cases v <;> simp only [isMapping, base] at h <;> simp_all [delValue, SVal.defaultOf]
  | storeSt st b w => rw [delValue, if_pos h]
  | _ => simp [isMapping, base] at h

/-- `selectStDelNodeIndexStruct`: an index into a deleted collection is the
default — the array was emptied. -/
theorem selectStDelNodeIndexStruct {t : StValue} (h : isArray t = true) (i : Int) :
    selectSt (delValue t) (Seg.at i) = dflt := by
  cases t with
  | sval v =>
      cases v <;> simp only [isArray, base] at h <;>
        simp_all [delValue, SVal.defaultOf, selectSt, svalSelect]
  | storeSt st b w =>
      have hm : isMapping (storeSt st b w) = false := by
        simp only [isMapping, isArray, base] at h ⊢
        split at h <;> simp_all
      rw [delValue, if_neg (by simp [hm]), if_pos h]
      simp [selectSt, svalSelect]
  | _ => simp [isArray, base] at h

/-- Keys survive `defaultOf` on a struct body, so a member lookup commutes
with it. -/
theorem lookupBy_defaultOfFields (n : Name) :
    ∀ fs : List (Name × SVal),
      lookupBy n (SVal.defaultOf.defaultOfFields fs) =
        (lookupBy n fs).map SVal.defaultOf
  | [] => rfl
  | (m, v) :: rest => by
      simp only [SVal.defaultOf.defaultOfFields, lookupBy]
      by_cases h : n = m
      · simp [h]
      · simp [h, lookupBy_defaultOfFields n rest]

/-- `selectStDelNodeRef` and `selectStDelNodeDefault` in one: off a mapping
and an array, a delete commutes with every selector — a reference member is
deleted recursively, a value member reads its default. -/
theorem selectSt_delValue {t : StValue} (hm : isMapping t = false)
    (ha : isArray t = false) (a : Seg) :
    selectSt (delValue t) a = delValue (selectSt t a) := by
  induction t with
  | sval v =>
      cases v with
      | struct fs =>
          cases a
          next n =>
            simp only [delValue, selectSt, svalSelect, SVal.defaultOf,
              lookupBy_defaultOfFields]
            cases lookupBy n fs <;> rfl
          next i => rfl
      | array es => simp [isArray, base] at ha
      | map es d => simp [isMapping, base] at hm
      | prim p => cases p <;> cases a <;> rfl
  | storeSt st b w ih _ =>
      have hm' : isMapping st = false := by simpa [isMapping, base] using hm
      have ha' : isArray st = false := by simpa [isArray, base] using ha
      rw [delValue, if_neg (by simp [hm]), if_neg (by simp [ha]), selectOnStore,
        selectOnStore]
      by_cases h : b = a
      · simp [h]
      · simp [h, ih hm' ha']
  | _ => cases a <;> rfl

/-! ## Sanity

The worked examples of the fundamentals repository, in this vocabulary, plus
the two disjointness taclet tests `Examples/Taclets/StorageOps.lean` checks by
running the interpreter.  They are here to catch a wrong definition before
`Denote.lean` builds on one. -/

section Sanity

private def acct : Seg := Seg.field "account"
private def bal : Seg := Seg.field "balance"
private def age : Seg := Seg.field "age"

/-- `alice.account.balance = 10; result = alice.account.balance` — the
fundamentals' `findOnSaveEx`, over an arbitrary store rather than a
`isStruct`-constrained one. -/
example (st : StValue) :
    find (save st [acct, bal] (int 10)) [acct, bal] = int 10 :=
  find_save_same st [acct, bal] (int 10)

/-- `alice.account.balance = 1; alice.age` — `storage-field-disjoint-fields.key`:
the write is invisible to the other member. -/
example (st : StValue) :
    find (save st [acct, bal] (int 1)) [age] = find st [age] :=
  find_save_frame st (int 1) [acct, bal] [age] (by decide)

/-- Reading *above* a write sees the write pushed down into the subtree. -/
example (st : StValue) :
    find (save st [acct, bal] (int 7)) [acct] = save (find st [acct]) [bal] (int 7) :=
  find_save_prefix st [acct] [bal] (int 7)

/-- A concrete store, evaluated: `bob.age = 7; alice = bob; bob.age = 9`
leaves `alice.age = 7` (a copy is by value). -/
example :
    find (save (save (sval (SVal.struct [("age", SVal.int 7)])) [age] (int 9))
        [] (sval (SVal.struct [("age", SVal.int 7)]))) [age]
      = sval (SVal.int 7) := by
  native_decide

/-- `delete` on a struct defaults its members but keeps its mappings —
`selectStDelNodeMap` and `selectStDelNodeDefault` on one value. -/
example :
    delValue (sval (SVal.struct
        [("owner", SVal.int 3), ("stash", SVal.map [(1, SVal.int 5)] (SVal.int 0))]))
      = sval (SVal.struct
        [("owner", SVal.int 0), ("stash", SVal.map [(1, SVal.int 5)] (SVal.int 0))]) := by
  native_decide

end Sanity

end StValue
end Theory
end Solidity
