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

The one lazy constructor is `merge`: KeY's `save(st, nil, v)`, which since
solkey's fold of `copyAt` into `save` is never collapsed but read through by
member sort, so that a struct written over a location keeps the location's
mapping members.  Its per-member decision needs a value from each of two
trees, which no single `SVal` leaf can hold.  The `save` section says why the
walk and the leaf are two definitions here.

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
  /-- `save(st, nil, v)`, the leaf of a write, left as a term: the location's
  old value beside the written one, read through by member sort.  The one
  **lazy** constructor here — see "The leaf of a write". -/
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

/-- `(Struct) t`.  A `save(st, nil, v)` leaf is `Struct`-sorted, so the cast is
`castDel` on it: dropping it here would drop the written value. -/
def asStruct : StValue -> StValue
  | storeSt st a v => storeSt st a v
  | sval v => sval v
  | merge o n => merge o n
  | _ => mtSt

/-- `(int) t` — `defValResolve` at `int`, then `defaultValueInt`.  The `merge`
arm *is* `saveOnEmptyPrim`: at a primitive sort a written location is the
written value. -/
def asInt : StValue -> Int
  | prim (PrimVal.int v) => v
  | sval (SVal.int v) => v
  | merge _ n => asInt n
  | _ => 0

/-- `(bool) t` — `defValResolve` at `bool`, then `defaultValueBool`;
`saveOnEmptyPrim` at `bool`. -/
def asBool : StValue -> Bool
  | prim (PrimVal.bool b) => b
  | sval (SVal.bool b) => b
  | merge _ n => asBool n
  | _ => false

/-! ## The shape dispatch

KeY discriminates a struct's members by the *field's* sort — `MapField`,
`RefField`, or a value member under `alphaPrim` — and both the delete family and
the leaf rules below read that sort off the segment.  A `Seg` does not carry
it, so both dispatch on the **value's** shape instead, which is what the
interpreter does (`SVal.defaultOf`) and what `docs/lean-key-rule-map.md` records
as the same semantics. -/

/-- The value a store chain is built over. -/
def base : StValue -> StValue
  | storeSt st _ _ => base st
  | merge _ n => base n
  | t => t

/-- The chain denotes a mapping: `delete` leaves it alone, a write keeps the
location's own. -/
def isMapping (t : StValue) : Bool :=
  match base t with
  | sval (SVal.map _ _) => true
  | _ => false

/-- The chain denotes an array: `delete` empties it, writes and all. -/
def isArray (t : StValue) : Bool :=
  match base t with
  | sval (SVal.array _) => true
  | _ => false

/-- The chain denotes a struct node: a write over it stays a leaf member by
member, since a nested struct may carry a mapping.  This is KeY's `RefField`,
read off the value.  An array member needs no marker even though its field is
a `RefField`: every read of a written array goes to the written side anyway
(`selectOnSaveEmptyIndexStruct` for `at(i)`, `selectOnSaveEmptyDefault` for
`size`). -/
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

/-- `selectSt<[α]>(st, a)`.  The `merge` arms are the four `selectOnSaveEmpty*`
taclets, with KeY's field sort replaced by the shape dispatch above: a mapping
member is the location's own, a struct member stays a leaf, everything else —
an element and every value member — is the written value's. -/
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

/-! ## `write`, `find`, and `save`

KeY's `save` walks the *store chain*, which is why its taclets split on
`mtSt` versus `storeSt`: the result is a chain in which the written path is
outermost-visible.  And it never collapses its leaf: `save(st, nil, v)` stays
as a term and the `selectOnSaveEmpty*` taclets read through it by member sort,
so that a struct written over a location keeps the location's mapping members
— Solidity never copies a mapping.  (Until solkey folded `copyAt` into `save`
that leaf was a separate `merge` symbol and `save(st, nil, v) ⇝ v` was a rule;
the fold is what makes every write a possible copy.)

Two definitions carry that here.  `write` is the walk without the leaf.  It
is not upstream's symbol: it is what the delete family and `Denote.lean` stay
eager over, and every `find`-over-`write` law below is exact.  `save` is
`write` with the leaf put back, `merge (asStruct (find st p)) v` — the
location's old value, at `Struct` as KeY's `st` is, beside the written one.
The `sval` arm of `write` has no KeY counterpart because KeY's `storage` is a
program variable, not a value; it expands the leaf one level, which is the
same shape `saveOnStoreCons` produces. -/

def write : StValue -> List Seg -> StValue -> StValue
  | _, [], v => v
  | storeSt st a1 v0, a2 :: flds, v1 =>
      if a1 = a2 then storeSt st a1 (write (asStruct v0) flds v1)
      else storeSt (write st (a2 :: flds) v1) a1 v0
  | sval sv, a :: flds, v =>
      storeSt (sval sv) a (write (asStruct (svalSelect sv a)) flds v)
  | merge o n, a :: flds, v =>
      storeSt (merge o n) a (write (asStruct (selectSt (merge o n) a)) flds v)
  | mtSt, a :: flds, v => storeSt mtSt a (write mtSt flds v)
  | prim _, a :: flds, v => storeSt mtSt a (write mtSt flds v)
  | dflt, a :: flds, v => storeSt mtSt a (write mtSt flds v)
termination_by st flds _ => (flds.length, st)

/-- `find<[α]>(st, flds)`.  The one-segment arm is KeY's `isEmpty(flds)`
branch, and it is not the same as recursing: the last step reads at the
*caller's* sort, so a primitive leaf survives it. -/
def find : StValue -> List Seg -> StValue
  | st, [] => st
  | st, [a] => selectSt st a
  | st, a :: b :: flds => find (selectSt st a) (b :: flds)

/-- `save(st, p, v)`: the walk, with the leaf left as a term. -/
def save (st : StValue) (p : List Seg) (v : StValue) : StValue :=
  write st p (merge (asStruct (find st p)) v)

/-- A cast to `Struct` is idempotent. -/
@[simp] theorem asStruct_asStruct (t : StValue) : asStruct (asStruct t) = asStruct t := by
  cases t <;> rfl

/-- One step of a read, in the form that does not split on the tail. -/
theorem find_cons (st : StValue) (a : Seg) (flds : List Seg) :
    find st (a :: flds) = find (selectSt st a) flds := by
  cases flds <;> rfl

/-- Reads compose along `++`. -/
theorem find_append (st : StValue) (p q : List Seg) :
    find st (p ++ q) = find (find st p) q := by
  induction p generalizing st with
  | nil => rfl
  | cons a rest ih => rw [List.cons_append, find_cons, ih, find_cons]

/-! ## The taclets of `structRules.key`

One theorem per taclet, in the file's order (the five that read the leaf are
in "The leaf of a write" below, after the `merge`-level facts they rest on).
Those that are the defining equations are `rfl`; `saveOnStoreCons` and
`findDefinitionCons` carry KeY's own shape, and `selectOnSaveCons` is the real
content. -/

/-- `defaultValue<[Struct]> ⇝ mtSt`. -/
@[simp] theorem defaultValueStruct : asStruct dflt = mtSt := rfl

/-- A primitive cast to `Struct` is the empty struct, the ill-sorted default. -/
@[simp] theorem asStruct_prim (q : PrimVal) : asStruct (prim q) = mtSt := rfl

/-- `selectSt<[α]>(storeSt(st, a1, v), a2)`. -/
@[simp] theorem selectOnStore (st : StValue) (a1 a2 : Seg) (v : StValue) :
    selectSt (storeSt st a1 v) a2 =
      if a1 = a2 then v else selectSt st a2 := rfl

/-- `selectSt<[α]>(mtSt, a) ⇝ defaultValue<[α]>`. -/
@[simp] theorem selectOnEmptyStorage (a : Seg) : selectSt mtSt a = dflt := rfl

/-- A cast to `Struct` is invisible to a selector. -/
@[simp] theorem selectSt_asStruct (t : StValue) (a : Seg) :
    selectSt (asStruct t) a = selectSt t a := by
  cases t <;> rfl

/-- …to a non-empty read. -/
theorem find_asStruct (t : StValue) {q : List Seg} (hq : q ≠ []) :
    find (asStruct t) q = find t q := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a rest => rw [find_cons, find_cons, selectSt_asStruct]

/-- …and, under a cast, to any read. -/
theorem asStruct_find_asStruct (t : StValue) (q : List Seg) :
    asStruct (find (asStruct t) q) = asStruct (find t q) := by
  cases q with
  | nil => simp [find]
  | cons a rest => rw [find_asStruct _ (by simp)]

/-- …and to the walk. -/
@[simp] theorem write_asStruct (t : StValue) (p : List Seg) (v : StValue) :
    write (asStruct t) p v = write t p v := by
  cases t <;> cases p <;> simp [write, asStruct]

/-- …and therefore to a write. -/
@[simp] theorem save_asStruct (t : StValue) (p : List Seg) (v : StValue) :
    save (asStruct t) p v = save t p v := by
  unfold save
  rw [write_asStruct, asStruct_find_asStruct]

/-- Reading into nothing is nothing. -/
@[simp] theorem find_dflt (q : List Seg) : find dflt q = dflt := by
  induction q with
  | nil => rfl
  | cons a rest ih => rw [find_cons]; exact ih

/-- …and so is reading a member of `mtSt`. -/
theorem find_mtSt {q : List Seg} (hq : q ≠ []) : find mtSt q = dflt := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a rest => rw [find_cons]; exact find_dflt rest

/-- …or of a primitive. -/
theorem find_prim (x : PrimVal) {q : List Seg} (hq : q ≠ []) : find (prim x) q = dflt := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a rest => rw [find_cons]; exact find_dflt rest

/-- One selector into an interpreter leaf: another leaf, nothing, or a
primitive (an array's `length`). -/
theorem svalSelect_shape (v : SVal) (a : Seg) :
    (∃ x, svalSelect v a = sval x) ∨ svalSelect v a = dflt ∨
      ∃ q, svalSelect v a = prim q := by
  match v, a with
  | SVal.struct fields, Seg.field n =>
      simp only [svalSelect]; cases lookupBy n fields <;> simp
  | SVal.array elems, Seg.field n =>
      by_cases hn : n = "length"
      · subst hn; simp [svalSelect]
      · simp [svalSelect, hn]
  | SVal.array elems, Seg.at i => simp only [svalSelect]; split <;> simp
  | SVal.map entries d, Seg.at i =>
      simp only [svalSelect]; cases lookupBy i entries <;> simp
  | SVal.prim _, Seg.field _ => simp [svalSelect]
  | SVal.prim _, Seg.at _ => simp [svalSelect]
  | SVal.struct _, Seg.at _ => simp [svalSelect]
  | SVal.map _ _, Seg.field _ => simp [svalSelect]

/-- What a read out of an interpreter leaf can be: another leaf, nothing, or
a primitive (an array's `length`).  Never a chain and never a `merge`, which
is what lets `Denote.lean` denote the leaf of a write over a pre-state tree. -/
theorem find_sval_shape (v : SVal) (p : List Seg) :
    (∃ x, find (sval v) p = sval x) ∨ find (sval v) p = dflt ∨
      ∃ q, find (sval v) p = prim q := by
  induction p generalizing v with
  | nil => exact Or.inl ⟨v, rfl⟩
  | cons a rest ih =>
      rw [find_cons]
      simp only [selectSt]
      rcases svalSelect_shape v a with ⟨x, hx⟩ | hd | ⟨q, hq⟩
      · rw [hx]; exact ih x
      · rw [hd, find_dflt]; exact Or.inr (Or.inl rfl)
      · rw [hq]
        cases rest with
        | nil => exact Or.inr (Or.inr ⟨q, rfl⟩)
        | cons b rest' => rw [find_prim _ (by simp)]; exact Or.inr (Or.inl rfl)

/-- `save(mtSt, cons(a, flds), v)`. -/
@[simp] theorem saveOnEmptyStorage (a : Seg) (flds : List Seg) (v : StValue) :
    save mtSt (a :: flds) v = storeSt mtSt a (save mtSt flds v) := by
  unfold save
  rw [write]
  cases flds with
  | nil => rfl
  | cons b rest => rw [find_mtSt (by simp), find_mtSt (by simp)]

/-- `save(storeSt(st, a1, v0), cons(a2, flds), v1)`, in KeY's own shape — no
`isEmpty(flds)` split any more, since the leaf is never collapsed. -/
theorem saveOnStoreCons (st : StValue) (a1 a2 : Seg) (flds : List Seg)
    (v0 v1 : StValue) :
    save (storeSt st a1 v0) (a2 :: flds) v1 =
      (if a1 = a2 then storeSt st a1 (save (asStruct v0) flds v1)
       else storeSt (save st (a2 :: flds) v1) a1 v0) := by
  unfold save
  by_cases h : a1 = a2
  · subst h
    rw [if_pos rfl, write, if_pos rfl, find_cons, selectOnStore, if_pos rfl,
      asStruct_find_asStruct]
  · rw [if_neg h, write, if_neg h, find_cons, selectOnStore, if_neg h, ← find_cons]

/-- `find<[α]>(st, nil) ⇝ (α) st`. -/
@[simp] theorem findDefinitionEmpty (st : StValue) : find st [] = st := rfl

/-- `find<[α]>(st, cons(a, flds))`, in KeY's own shape.  The `isEmpty` branch
is not decoration: the last step reads at the caller's sort, so a primitive
leaf survives it where `selectSt<[Struct]>` would not. -/
theorem findDefinitionCons (st : StValue) (a : Seg) (flds : List Seg) :
    find st (a :: flds) =
      if flds.isEmpty then selectSt st a else find (selectSt st a) flds := by
  cases flds <;> rfl

/-! ### `selectOnSaveCons`

The taclet that does the work, and the reason this module exists: reading one
selector out of a write.  The fundamentals repository proves its analogue
(`selectSave`) under an `isStruct` well-formedness hypothesis; here the
definitions are total, so there is none.  Proved for the walk first, then
lifted to `save`: the leaf is the same term on both sides. -/

/-- `selectOnSaveCons` for `write`. -/
theorem selectOnWriteCons (st : StValue) (a1 a2 : Seg) (flds : List Seg)
    (v : StValue) :
    selectSt (write st (a1 :: flds) v) a2 =
      if a1 = a2 then write (asStruct (selectSt st a1)) flds v
      else selectSt st a2 := by
  induction st with
  | storeSt st' b w ih =>
      by_cases hb : b = a1
      · subst hb
        by_cases h : b = a2 <;> simp [write, selectSt, h]
      · by_cases h : b = a2
        · subst h
          simp [write, selectSt, hb, Ne.symm hb]
        · simp only [write, if_neg hb, selectSt, if_neg h, ih]
  | _ => by_cases h : a1 = a2 <;> simp [write, selectSt, h]

/-- `selectSt<[α]>(save(st, cons(a1, flds), v), a2)`. -/
theorem selectOnSaveCons (st : StValue) (a1 a2 : Seg) (flds : List Seg)
    (v : StValue) :
    selectSt (save st (a1 :: flds) v) a2 =
      if a1 = a2 then save (asStruct (selectSt st a1)) flds v
      else selectSt st a2 := by
  unfold save
  rw [selectOnWriteCons]
  by_cases h : a1 = a2
  · rw [if_pos h, if_pos h, find_cons, asStruct_find_asStruct]
  · rw [if_neg h, if_neg h]

/-! ## `find` over `write`, and over `save`

solkey has no `find(save(…), …)` taclet: a read of a write is reached by
`findDefinitionCons` unfolding `find` into `selectSt` and `selectOnSaveCons`
then commuting one selector past the write.  Those four steps are what the
laws below package, one per way a read path can lie against a written one —
the same path, below it, above it, or off it.  For `write` they are exact;
for `save` the same path reads the leaf, and everything under it reads
through the leaf.  `Semantics` has only the first
(`SemanticsProperties.SVal.find_save_same`), and only in the form that
presupposes the write succeeded. -/

/-- **Reading below the walk.** Everything at or under the written path comes
out of the written value. -/
theorem find_write_extends (st : StValue) (p q : List Seg) (v : StValue) :
    find (write st p v) (p ++ q) = find v q := by
  induction p generalizing st with
  | nil => simp [write]
  | cons a rest ih =>
      rw [List.cons_append, findDefinitionCons, selectOnWriteCons, if_pos rfl,
        write_asStruct]
      cases hrq : rest ++ q with
      | nil =>
          have hr : rest = [] := List.eq_nil_of_append_eq_nil hrq |>.1
          have hq : q = [] := List.eq_nil_of_append_eq_nil hrq |>.2
          subst hr; subst hq; simp_all [write]
      | cons _ _ => rw [if_neg (by simp), ← hrq, ih]

/-- **Reading exactly the walk** — with no side condition at all.  The
fundamentals repository's `findOnSave` needs a well-formed path and a
well-formed store; totality buys both away. -/
theorem find_write_same (st : StValue) (p : List Seg) (v : StValue) :
    find (write st p v) p = v := by
  have := find_write_extends st p [] v
  simpa using this

/-- **Reading above the walk.** A prefix of the written path reads the
written subtree, i.e. the write pushed down to what is left of it. -/
theorem find_write_prefix (st : StValue) (q r : List Seg) (v : StValue) :
    find (write st (q ++ r) v) q = write (find st q) r v := by
  induction q generalizing st with
  | nil => simp
  | cons a q' ih =>
      rw [List.cons_append, findDefinitionCons, selectOnWriteCons, if_pos rfl,
        write_asStruct]
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
theorem find_write_frame (st : StValue) (v : StValue) :
    ∀ p q : List Seg, diverges p q = true -> find (write st p v) q = find st q := by
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
            rw [findDefinitionCons, findDefinitionCons, selectOnWriteCons,
              if_pos rfl, write_asStruct,
              if_neg (by simpa using hq'), if_neg (by simpa using hq'), ih _ _ h]
          · -- Off the path at the very first segment: `selectOnSaveCons`'s
            -- `\else` branch makes the two sides the same term.
            rw [findDefinitionCons, findDefinitionCons, selectOnWriteCons,
              if_neg hab]

/-- Below a write: the leaf, read on. -/
theorem find_save_extends (st : StValue) (p q : List Seg) (v : StValue) :
    find (save st p v) (p ++ q) = find (merge (asStruct (find st p)) v) q :=
  find_write_extends st p q _

/-- Exactly a write: the leaf. -/
theorem find_save_same (st : StValue) (p : List Seg) (v : StValue) :
    find (save st p v) p = merge (asStruct (find st p)) v :=
  find_write_same st p _

/-- …which at a primitive sort is the written value (`saveOnEmptyPrim`). -/
theorem find_save_same_asInt (st : StValue) (p : List Seg) (v : StValue) :
    asInt (find (save st p v) p) = asInt v := by
  rw [find_save_same]; rfl

/-- Above a write: the write pushed down. -/
theorem find_save_prefix (st : StValue) (q r : List Seg) (v : StValue) :
    find (save st (q ++ r) v) q = save (find st q) r v := by
  unfold save
  rw [find_write_prefix, find_append]

/-- Off a write: the frame. -/
theorem find_save_frame (st : StValue) (v : StValue) (p q : List Seg)
    (h : diverges p q = true) : find (save st p v) q = find st q :=
  find_write_frame st _ p q h

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

/-- No leaf on the chain's spine.  `delValue` pushes through a store chain
member by member; a `merge` is not a chain step, and on one the push is only
sound when the two sides agree on what is a mapping — which a well-sorted
write guarantees and this predicate assumes away. -/
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
marker and lets reads push it down; the eager reading is the walk with the
deleted subtree, which is `Semantics.storageDeleteUpd`'s shape exactly.  Over
`write`, not `save`: a delete is the one write whose leaf has nothing to keep
that `delValue` did not already keep. -/
def delAt (st : StValue) (p : List Seg) : StValue :=
  write st p (delValue (find st p))

/-- `delValue<[Struct]>(st) ⇝ delNode(st)`. -/
theorem delValueStruct (st : StValue) : delValue st = delNode st := rfl

/-- `delValue<[alphaPrim]>(x) ⇝ defaultValue<[alphaPrim]>`. -/
@[simp] theorem delValueDefault (p : PrimVal) : delValue (prim p) = dflt := rfl

/-- `delAt(st, nil) ⇝ delNode(st)`. -/
@[simp] theorem delAtEmpty (st : StValue) : delAt st [] = delNode st := by
  simp [delAt, write]

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

/-! ## The leaf of a write

A struct written over a location overwrites it, *except* that mapping members
keep what the location held: Solidity never copies a mapping.  solkey gives
that meaning to `save` itself — `save(st, nil, v)` is never collapsed, and
five taclets read through it by the member's sort (`selectOnSaveEmpty{Map,
Ref,IndexStruct,Default}` and `saveOnEmptyPrim`).  Until the fold that leaf
was a separate `merge` symbol written only by a `copyAt` the eight copy rules
used; now every write carries it, and every `*CopySource` / `…StoreRoot` rule
writes plain `save`.

The leaf is the one place this file is lazy, which is what departs from the
delete family above.  `delValue`'s decision is on a single value and can be
taken inside an `SVal` leaf; the leaf's is on a *pair* drawn from two
different trees, and rebuilding a struct whose members come from both cannot
stay inside one leaf.  So `merge` survives into the term and the read rules
are the arms of `selectSt` rather than theorems over a definition.  Keeping
`write` underneath is what lets `save` inherit the `find`-over-`write` laws.

One divergence from upstream, and it is the field sort again: KeY fires
`selectOnSaveEmptyRef` on a `RefField` whatever the location holds there, so a
member that is *absent* still recurses, and the nested mapping read lands on
an empty mapping.  The shape dispatch sees `dflt`, takes the written side, and
so copies the source's mapping.  The two differ exactly when the location's
member is absent while the source's carries a mapping — unreachable through
the interpreter, which materialises every member (`defaultForTy`) and refuses
a mapping-typed source outright (`Wp/TerminalUpdate.rhsSVal`). -/

/-- `save(st, nil, v)` is the leaf. -/
@[simp] theorem save_nil (st v : StValue) : save st [] v = merge (asStruct st) v := by
  simp [save, write]

/-- A struct node is already at `Struct`. -/
theorem asStruct_of_isNode {t : StValue} (h : isNode t = true) : asStruct t = t := by
  cases t <;> simp_all [isNode, base, asStruct]

/-- `saveOnEmptyPrim` at `int`: at a primitive sort a written location *is* the
written value.  Stated at the `merge` level too, since that is how `asInt`
computes. -/
@[simp] theorem mergePrimInt (o n : StValue) : asInt (merge o n) = asInt n := rfl

/-- `saveOnEmptyPrim` at `bool`. -/
@[simp] theorem mergePrimBool (o n : StValue) : asBool (merge o n) = asBool n := rfl

/-- `saveOnEmptyPrim`, for `save`: `(int) save(st, nil, v) ⇝ (int) v`. -/
@[simp] theorem saveOnEmptyPrimInt (st v : StValue) : asInt (save st [] v) = asInt v := by
  rw [save_nil]; rfl

/-- …and at `bool`. -/
@[simp] theorem saveOnEmptyPrimBool (st v : StValue) : asBool (save st [] v) = asBool v := by
  rw [save_nil]; rfl

/-- `selectOnSaveEmptyMap` at the `merge` level: a mapping member of a written
location is the location's own.  This is the half of the change no `.sol`
example can state — both front ends reject a copy whose type carries a
mapping — so `keyext.solidity.examples/storage/copyKeepsMapping.key` pins it
upstream and `Examples/Solkey/Rules.lean` here. -/
theorem selectStMergeMap {o n : StValue} {f : Name}
    (h : isMapping (selectSt o (Seg.field f)) = true) :
    selectSt (merge o n) (Seg.field f) = selectSt o (Seg.field f) := by
  simp [selectSt, h]

/-- `selectOnSaveEmptyRef` at the `merge` level: a struct member stays a leaf,
because a nested struct may itself carry a mapping. -/
theorem selectStMergeRef {o n : StValue} {f : Name}
    (hm : isMapping (selectSt o (Seg.field f)) = false)
    (h : isNode (selectSt o (Seg.field f)) = true) :
    selectSt (merge o n) (Seg.field f) =
      merge (selectSt o (Seg.field f)) (selectSt n (Seg.field f)) := by
  simp [selectSt, hm, h]

/-- `selectOnSaveEmptyIndexStruct` at the `merge` level: an element of a
written collection is the written one, with no shape test — upstream's
`Struct` and `alphaPrim` instances agree here. -/
@[simp] theorem selectStMergeIndexStruct (o n : StValue) (i : Int) :
    selectSt (merge o n) (Seg.at i) = selectSt n (Seg.at i) := rfl

/-- `selectOnSaveEmptyDefault` at the `merge` level: a value member of a
written location is the written one. -/
theorem selectStMergeDefault {o n : StValue} {f : Name}
    (hm : isMapping (selectSt o (Seg.field f)) = false)
    (hn : isNode (selectSt o (Seg.field f)) = false) :
    selectSt (merge o n) (Seg.field f) = selectSt n (Seg.field f) := by
  simp [selectSt, hm, hn]

/-- `selectStValueCast` and the cast a sort-free write leaves on either side of
the leaf: invisible to the read (`selectSt_asStruct` on both sides). -/
@[simp] theorem merge_asStruct (o n : StValue) (a : Seg) :
    selectSt (merge (asStruct o) (asStruct n)) a = selectSt (merge o n) a := by
  cases a <;> simp only [selectSt, selectSt_asStruct]

/-- The old side of the leaf is at `Struct`, which a read does not see. -/
@[simp] theorem selectSt_merge_asStruct_left (o n : StValue) (a : Seg) :
    selectSt (merge (asStruct o) n) a = selectSt (merge o n) a := by
  cases a <;> simp only [selectSt, selectSt_asStruct]

/-- `selectOnSaveEmptyMap`: `selectSt<[Struct]>(save(st, nil, v), mf) ⇝
selectSt<[Struct]>(st, mf)`, keyed on `isMapping` of the location's member
rather than on a `MapField` segment. -/
theorem selectOnSaveEmptyMap {st v : StValue} {f : Name}
    (h : isMapping (selectSt st (Seg.field f)) = true) :
    selectSt (save st [] v) (Seg.field f) = selectSt st (Seg.field f) := by
  rw [save_nil, selectSt_merge_asStruct_left, selectStMergeMap h]

/-- `selectOnSaveEmptyRef`: `selectSt<[Struct]>(save(st, nil, v), rf) ⇝
save(selectSt<[Struct]>(st, rf), nil, selectSt<[Struct]>((Struct) v, rf))`,
keyed on `isNode`. -/
theorem selectOnSaveEmptyRef {st v : StValue} {f : Name}
    (hm : isMapping (selectSt st (Seg.field f)) = false)
    (h : isNode (selectSt st (Seg.field f)) = true) :
    selectSt (save st [] v) (Seg.field f) =
      save (selectSt st (Seg.field f)) [] (selectSt (asStruct v) (Seg.field f)) := by
  rw [save_nil, selectSt_merge_asStruct_left, selectStMergeRef hm h, save_nil,
    asStruct_of_isNode h, selectSt_asStruct]

/-- `selectOnSaveEmptyIndexStruct`: `selectSt<[Struct]>(save(st, nil, v), at(iv))
⇝ selectSt<[Struct]>((Struct) v, at(iv))`. -/
@[simp] theorem selectOnSaveEmptyIndexStruct (st v : StValue) (i : Int) :
    selectSt (save st [] v) (Seg.at i) = selectSt v (Seg.at i) := by
  rw [save_nil]; rfl

/-- `selectOnSaveEmptyDefault`: `selectSt<[alphaPrim]>(save(st, nil, v), a) ⇝
selectSt<[alphaPrim]>((Struct) v, a)`. -/
theorem selectOnSaveEmptyDefault {st v : StValue} {f : Name}
    (hm : isMapping (selectSt st (Seg.field f)) = false)
    (hn : isNode (selectSt st (Seg.field f)) = false) :
    selectSt (save st [] v) (Seg.field f) = selectSt v (Seg.field f) := by
  rw [save_nil, selectSt_merge_asStruct_left, selectStMergeDefault hm hn]

/-- A value member read one step below a write is the written value's — the
`selectOnSaveEmptyDefault` step of a read, with the shape dispatch's side of
KeY's read-sort discipline as hypotheses: the location holds neither a
mapping nor a struct at that member.  (Over an arbitrary store the theorem
is false without them, and KeY's `find<[int]>` is what decides it there.) -/
theorem find_save_extends_field (st v : StValue) (p : List Seg) (f : Name)
    (hm : isMapping (selectSt (find st p) (Seg.field f)) = false)
    (hn : isNode (selectSt (find st p) (Seg.field f)) = false) :
    find (save st p v) (p ++ [Seg.field f]) = selectSt v (Seg.field f) := by
  rw [find_save_extends, find, selectSt_merge_asStruct_left, selectStMergeDefault hm hn]

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
`isStruct`-constrained one.  The read lands on the leaf, and at `int` the
leaf is the written value. -/
example (st : StValue) :
    asInt (find (save st [acct, bal] (int 10)) [acct, bal]) = 10 :=
  find_save_same_asInt st [acct, bal] (int 10)

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
  save twoLedgers [ledger2Seg] (find twoLedgers [ledgerSeg])

/-- A copy takes every value member from the source (`selectOnSaveEmptyDefault`)
and keeps the target's own mapping (`selectOnSaveEmptyMap`). -/
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
