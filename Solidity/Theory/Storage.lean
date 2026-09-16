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

The one lazy symbol is `merge`, the copied-location marker of the copy family:
its per-member decision needs a value from each of two trees, which no single
`SVal` leaf can hold.  Its section says why.

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
  /-- `merge<[alpha]>(old, new)`: a copied location as a read sees it.  The one
  **lazy** marker here — see "The copy family". -/
  | merge (old new : StValue)
  deriving Repr, DecidableEq

namespace StValue

@[match_pattern] abbrev int (v : Int) : StValue := .prim (.int v)
@[match_pattern] abbrev bool (b : Bool) : StValue := .prim (.bool b)

/-! ## Casts

`cast<[Struct]>` and the `Prim` casts of `cast.key`/`memoryRules.key`.  KeY
deletes a cast on a well-sorted argument (`castDel`); these are total, so the
ill-sorted cases get the sort's default, which is `defaultValueInt` /
`defaultValueBool` / `defaultValueStruct` read as functions. -/

/-- `(Struct) t`.  A `merge` marker is `Struct`-sorted, so the cast is
`castDel` on it: dropping it here would drop the copied value. -/
def asStruct : StValue -> StValue
  | storeSt st a v => storeSt st a v
  | sval v => sval v
  | merge o n => merge o n
  | _ => mtSt

/-- `(int) t` — `defValResolve` at `int`, then `defaultValueInt`.  The `merge`
arm *is* `mergePrim`: at a primitive sort a copied location is the copy. -/
def asInt : StValue -> Int
  | prim (PrimVal.int v) => v
  | sval (SVal.int v) => v
  | merge _ n => asInt n
  | _ => 0

/-- `(bool) t` — `defValResolve` at `bool`, then `defaultValueBool`;
`mergePrim` at `bool`. -/
def asBool : StValue -> Bool
  | prim (PrimVal.bool b) => b
  | sval (SVal.bool b) => b
  | merge _ n => asBool n
  | _ => false

/-! ## The shape dispatch

KeY discriminates a struct's members by the *field's* sort — `MapField`,
`RefField`, or a value member under `alphaPrim` — and both the delete family and
the copy family below read that sort off the segment.  A `Seg` does not carry
it, so both dispatch on the **value's** shape instead, which is what the
interpreter does (`SVal.defaultOf`) and what `docs/lean-key-rule-map.md` records
as the same semantics. -/

/-- The value a store chain is built over. -/
def base : StValue -> StValue
  | storeSt st _ _ => base st
  | merge _ n => base n
  | t => t

/-- The chain denotes a mapping: `delete` leaves it alone, a copy keeps the
target's own. -/
def isMapping (t : StValue) : Bool :=
  match base t with
  | sval (SVal.map _ _) => true
  | _ => false

/-- The chain denotes an array: `delete` empties it, writes and all. -/
def isArray (t : StValue) : Bool :=
  match base t with
  | sval (SVal.array _) => true
  | _ => false

/-- The chain denotes a struct node: a copy merges it member by member, since a
nested struct may carry a mapping.  This is KeY's `RefField`, read off the
value.  An array member needs no marker even though its field is a `RefField`:
every read of a merged array goes to the copied side anyway
(`selectStMergeIndexStruct` for `at(i)`, `selectStMergeDefault` for `size`). -/
def isNode (t : StValue) : Bool :=
  match base t with
  | sval (SVal.struct _) => true
  | mtSt => true
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

/-- `selectSt<[α]>(st, a)`.  The `merge` arms are the four `selectStMerge*`
taclets, with KeY's field sort replaced by the shape dispatch above: a mapping
member is the target's own, a struct member stays merged, everything else — an
element and every value member — is the copied value's. -/
def selectSt : StValue -> Seg -> StValue
  | mtSt, _ => dflt
  | storeSt st a1 v, a2 => if a1 = a2 then v else selectSt st a2
  | sval v, a => svalSelect v a
  | merge _ n, Seg.at i => selectSt n (Seg.at i)
  | merge o n, Seg.field f =>
      if isMapping (selectSt o (Seg.field f)) then selectSt o (Seg.field f)
      else if isNode (selectSt o (Seg.field f)) then
        merge (selectSt o (Seg.field f)) (selectSt n (Seg.field f))
      else selectSt n (Seg.field f)
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
  | merge o n, a :: flds, v =>
      storeSt (merge o n) a (save (asStruct (selectSt (merge o n) a)) flds v)
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

Upstream used to rewrite to `selectSt(save(st, flds, v), a)`, with an `flds`
its `\find` never binds; solkey `c80a54494c` adopted this statement
(`selectSt<[alpha]>((Struct) v, a)`, the cast absorbed by `selectSt_asStruct`).
The history is in `docs/solkey-feedback.md`. -/
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
dispatch on what the chain is built over — `isMapping`/`isArray` above — because
`defaultOf` empties an array, keeps a mapping and recurses into a struct, and a
chain's own constructors do not say which it is. -/

/-- No copy marker on the chain's spine.  `delValue` pushes through a store
chain member by member; a `merge` is not a chain step, and on one the push is
only sound when the two sides agree on what is a mapping — which a well-sorted
copy guarantees and this predicate assumes away. -/
def mergeFree : StValue -> Bool
  | merge _ _ => false
  | storeSt st _ _ => mergeFree st
  | _ => true

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
  | merge o n =>
      if isMapping (merge o n) then merge o n
      else if isArray (merge o n) then sval (SVal.array [])
      else merge (delValue o) (delValue n)

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
  | merge o n => rw [delValue, if_pos h]
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
  | merge o n =>
      have hm : isMapping (merge o n) = false := by
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
deleted recursively, a value member reads its default.

`mergeFree` is what a chain of `storeSt` over an `sval` leaf satisfies, i.e.
every term a rule's update builds; on a copy marker the push through is only
sound when the two sides agree on what is a mapping, and nothing here needs
it. -/
theorem selectSt_delValue {t : StValue} (hm : isMapping t = false)
    (ha : isArray t = false) (hmf : mergeFree t = true) (a : Seg) :
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
      have hmf' : mergeFree st = true := by simpa [mergeFree] using hmf
      rw [delValue, if_neg (by simp [hm]), if_neg (by simp [ha]), selectOnStore,
        selectOnStore]
      by_cases h : b = a
      · simp [h]
      · simp [h, ih hm' ha' hmf']
  | merge o n _ _ => simp [mergeFree] at hmf
  | _ => cases a <;> rfl

/-! ## The copy family

A storage-to-storage copy overwrites a location, *except* that mapping members
keep what the target held: Solidity never copies a mapping.  solkey
(`c80a54494c`) gives that meaning with a second lazy pair — `copyAt` writes the
copied value and `merge` is the copied location as a read sees it — and every
`*CopySource` / `…StoreRoot` rule now emits `copyAt` where it used to emit
`save`.

`copyAt` is eager on the outside and lazy on the inside, which is the one place
this file departs from the delete family above.  `delValue`'s decision is on a
single value and can be taken inside an `SVal` leaf; `merge`'s is on a *pair*
drawn from two different trees, and rebuilding a struct whose members come from
both cannot stay inside one leaf.  So the marker survives into the term and the
four `selectStMerge*` taclets are the arms of `selectSt` rather than theorems
over a definition.  Keeping `save` on the outside is what lets `copyAt` inherit
the `find`-over-`save` laws above unchanged.

One divergence from upstream, and it is the field sort again: KeY fires
`selectStMergeRef` on a `RefField` whatever the target holds there, so a target
member that is *absent* still recurses, and the nested mapping read lands on an
empty mapping.  The shape dispatch sees `dflt`, takes the copied side, and so
copies the source's mapping.  The two differ exactly when the target's member is
absent while the source's carries a mapping — unreachable through the
interpreter, which materialises every member (`defaultForTy`) and refuses a
mapping-typed source outright (`Wp/TerminalUpdate.rhsSVal`). -/

/-- `copyAt(st, p, v)`: the storage with the location at `p` overwritten by
`v`, mapping members excepted.  Upstream writes the marker and lets reads push
it down; here the `save` is eager and only the merge is deferred. -/
def copyAt (st : StValue) (p : List Seg) (v : StValue) : StValue :=
  save st p (merge (find st p) (asStruct v))

/-- `copyAt(st, nil, v) ⇝ merge<[Struct]>(st, (Struct) v)`. -/
@[simp] theorem copyAtEmpty (st v : StValue) :
    copyAt st [] v = merge st (asStruct v) := by simp [copyAt]

/-- `selectOnCopyAtCons`: reading one selector out of a copy — `selectOnSaveCons`
with the copied value in place of the written one. -/
theorem selectOnCopyAtCons (st : StValue) (a1 a2 : Seg) (flds : List Seg)
    (v : StValue) :
    selectSt (copyAt st (a1 :: flds) v) a2 =
      (if a1 = a2 then
        (if flds.isEmpty then merge (selectSt st a1) (asStruct v)
         else copyAt (selectSt st a1) flds v)
      else selectSt st a2) := by
  rw [copyAt, selectOnSaveCons]
  by_cases h : a1 = a2
  · rw [if_pos h, if_pos h]
    cases flds with
    | nil => simp [find]
    | cons b rest =>
        rw [if_neg (by simp), copyAt, save_asStruct, findDefinitionCons,
          if_neg (by simp)]
  · rw [if_neg h, if_neg h]

/-- `mergePrim` at `int`: at a primitive sort a copied location *is* the copy. -/
@[simp] theorem mergePrimInt (o n : StValue) : asInt (merge o n) = asInt n := rfl

/-- `mergePrim` at `bool`. -/
@[simp] theorem mergePrimBool (o n : StValue) : asBool (merge o n) = asBool n := rfl

/-- `selectStMergeMap`: a mapping member of a copied location is the target's
own.  This is the half of the change no `.sol` example can state — both front
ends reject a copy whose type carries a mapping — so
`keyext.solidity.examples/storage/copyKeepsMapping.key` pins it upstream and
`Examples/Solkey/Rules.lean` here. -/
theorem selectStMergeMap {o n : StValue} {f : Name}
    (h : isMapping (selectSt o (Seg.field f)) = true) :
    selectSt (merge o n) (Seg.field f) = selectSt o (Seg.field f) := by
  simp [selectSt, h]

/-- `selectStMergeRef`: a struct member stays merged, because a nested struct
may itself carry a mapping. -/
theorem selectStMergeRef {o n : StValue} {f : Name}
    (hm : isMapping (selectSt o (Seg.field f)) = false)
    (h : isNode (selectSt o (Seg.field f)) = true) :
    selectSt (merge o n) (Seg.field f) =
      merge (selectSt o (Seg.field f)) (selectSt n (Seg.field f)) := by
  simp [selectSt, hm, h]

/-- `selectStMergeIndexStruct`: an element of a copied collection is the
copy's, with no shape test — upstream's `Struct` and `alphaPrim` instances
agree here. -/
@[simp] theorem selectStMergeIndexStruct (o n : StValue) (i : Int) :
    selectSt (merge o n) (Seg.at i) = selectSt n (Seg.at i) := rfl

/-- `selectStMergeDefault`: a value member of a copied location is the copy's. -/
theorem selectStMergeDefault {o n : StValue} {f : Name}
    (hm : isMapping (selectSt o (Seg.field f)) = false)
    (hn : isNode (selectSt o (Seg.field f)) = false) :
    selectSt (merge o n) (Seg.field f) = selectSt n (Seg.field f) := by
  simp [selectSt, hm, hn]

/-- `mergeStValueCast`: pushing a reader's cast into a sort-free `merge` is
invisible to the read, the treatment `findStValueCast` and
`delValueStValueCast` already get (`selectSt_asStruct` on both sides).
`selectStValueCast` is `selectSt_asStruct` itself. -/
@[simp] theorem merge_asStruct (o n : StValue) (a : Seg) :
    selectSt (merge (asStruct o) (asStruct n)) a = selectSt (merge o n) a := by
  cases a <;> simp only [selectSt, selectSt_asStruct]

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

private def ledgerSeg : Seg := Seg.field "ledger"
private def ledger2Seg : Seg := Seg.field "ledger2"
private def nonceSeg : Seg := Seg.field "nonce"
private def balancesSeg : Seg := Seg.field "balances"

/-- Two ledgers, each a nonce beside a mapping. -/
private def twoLedgers : StValue :=
  sval (SVal.struct
    [("ledger", SVal.struct
        [("nonce", SVal.int 1), ("balances", SVal.map [(1, SVal.int 11)] (SVal.int 0))]),
     ("ledger2", SVal.struct
        [("nonce", SVal.int 2), ("balances", SVal.map [(1, SVal.int 22)] (SVal.int 0))])])

/-- `ledger2 = ledger`, the copy of `copyKeepsMapping.key`. -/
private def copiedLedgers : StValue :=
  copyAt twoLedgers [ledger2Seg] (find twoLedgers [ledgerSeg])

/-- A copy takes every value member from the source (`selectStMergeDefault`)
and keeps the target's own mapping (`selectStMergeMap`). -/
example :
    asInt (find copiedLedgers [ledger2Seg, nonceSeg]) = 1
      ∧ asInt (find copiedLedgers [ledger2Seg, balancesSeg, Seg.at 1]) = 22 := by
  native_decide

/-- …and the mapping is *not* the source's: this is the refutation an inverted
`isMapping` branch would fail. -/
example : asInt (find copiedLedgers [ledger2Seg, balancesSeg, Seg.at 1]) ≠ 11 := by
  native_decide

/-- `delete` *after* a copy — `delValue`'s `merge` arm, which is what upstream's
`testPushCopyThenDeleteTarget` walks into: the copied value's members reset and
the target's own mapping is still there, both at once. -/
example :
    asInt (find (delValue copiedLedgers) [ledger2Seg, nonceSeg]) = 0
      ∧ asInt (find (delValue copiedLedgers) [ledger2Seg, balancesSeg, Seg.at 1]) = 22 := by
  native_decide

end Sanity

end StValue
end Theory
end Solidity
