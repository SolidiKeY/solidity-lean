import Solidity.Theory.Storage
import Solidity.Theory.Memory
import Solidity.Theory.CrossDomain

/-!
# The theory's rewrite rules, under the paper's names

The calculus layer has `Calculus/Rules.lean`: an enumeration of rule names, a table of
effects, and chains that write the rule on the arrow.  The theory layer had
none of that.  `Theory/Storage.lean`, `Theory/Memory.lean` and
`Theory/CrossDomain.lean` are the three algebras, each taclet a theorem named
after its `.key` original — and a derivation could not name one, because a
`theorem` is not a value.

This module is the missing enumeration.  `TheoryRule` is one constructor per
rewrite rule of the paper's signature (`sections/signature.tex`, plus the two
cross-domain sections), under **the paper's name** rather than KeY's, and
`theoryRuleLemma` says which theorem each one is.  That is what lets a
`sol_rewrite` chain write `=[.findOnSave]` on a line and have the name checked
rather than decorative.

## Why the paper's names and not KeY's

The theorems keep their upstream names: that is what makes
`docs/lean-key-rule-map.md` a map and what a reader comparing against
`structRules.key` needs.  A chain, though, is the *paper's* artefact, and its
prose names the rules it applies — "the sixth step is `readCopySt`"
(`sections/storage-to-memory.tex`).  A chain that said `findDefinitionCons`
where the paper says `findPath` would not be the paper's derivation.  So the
two naming schemes both exist and this table is the join; a name that is in
neither is a `theoryRuleLemma` that does not elaborate.

## Completeness

`theoryRuleLemma` is a total match, so a constructor without a lemma is a build
failure, and every right-hand side is a double-backtick name, so a lemma that
does not exist is one too.  What neither catches is a *paper* rule with no
constructor; `./scripts/check-theory-rules.mjs` is that check, reading the
`\namedRwRule` declarations out of the paper's sources.

Every rule of `sections/signature.tex` and the two cross-domain sections has
a constructor, with five exceptions, each deliberate.  `selectDelNodeMap` is
architectural: `Semantics.Seg` carries no `MapField` classification, so "a
mapping member survives `delete`" has no statement in this algebra (the
`Theory/Storage.lean` docstring, and `docs/lean-key-rule-map.md`, which files
solkey's `selectOnSaveEmptyMap` under the same gap).  The four
`expandInUintN`/`expandInIntN` rules are the arithmetic the paper's own
"not implemented" section lists.  `singletonPath` (`⟨f⟩ = ∅·f`) and
`delValueCast` (the cast pushed through the reset) *are* present: the first is
definitional, since a path is a `List Seg`, and the second is
`StValue.delValueCast` with its `int`/`bool` twins.
`./scripts/check-theory-rules.mjs` carries each of the five arguments beside
the name it excuses.

The other direction — a constructor the paper does not declare — is
`paperAbsent`: seven rules this package states and the paper is to gain, since
this repository is the source of truth the paper is ported from.  The script
reads that list too, and reports the seven rather than failing on them.

One spelling note.  The array length field is `Seg.field "length"` here where
solkey writes `size`; the paper's `findLength`/`saveLength` are abbreviations
of `find`/`save` on that field, as they are here, and `Sym.length` in the
calculus is the same abbreviation.
-/

namespace Solidity
namespace Theory

/-- A rewrite rule of the data-structure theories, under the name the paper's
signature gives it. -/
inductive TheoryRule where
  -- ### Storage: `select`/`store` (`sections/signature.tex`, "Storage core")
  | selectStoreEqual
  | selectStoreDifferent
  | selectEmptyStruct
  -- ### Storage: the lazy `find`/`save` pair
  | findEmptyPath
  | findPath
  | saveEmptyPath
  | savePath
  -- ### Storage: singleton paths
  | singletonPath
  | findSingleton
  | saveSingleton
  -- ### Storage: `find` over `save`
  -- The paper's signature reaches a read-of-a-write by unfolding; the slides
  -- state the four shortcuts directly, as `findOnSaveEqual`/`findOnSaveDifferent`.
  -- `docs/lean-key-rule-map.md` records that solkey has no taclet for them.
  /-- Reading exactly the written path. -/
  | findOnSave
  /-- Reading a path that leaves the written one. -/
  | findOnSaveDifferent
  /-- Reading above the write: a prefix sees the write pushed down. -/
  | findOnSavePrefix
  /-- Reading below the write: an extension reads out of the written value. -/
  | findOnSaveExtends
  -- ### Storage: `delete`
  | delAtEmpty
  | findDelAt
  | findDelAtOutside
  /-- Reading below the deleted path: out of the deleted value. -/
  | findDelAtExtends
  | defValResolve
  | delValueStruct
  | delValueDefault
  | delValueCast
  | selectDelNodeRef
  | selectDelNodeDefault
  | selectDelNodeIndex
  | selectOnDelAt
  -- ### Memory: `read`/`write`/`add`
  | readWriteEqual
  | readWriteDifferent
  | readAddEqual
  | readAddDifferent
  | readEmptyMem
  -- ### Memory: defaults
  | defaultPrim
  | defaultIdentity
  -- ### Memory: `readR`
  | readREmptyPath
  | readRSingleton
  | readRPath
  -- ### Memory: the `new` predicate
  | newAddSame
  | newAddDifferent
  | newWrite
  | newEmptyMem
  -- ### Cross-domain: the two copy views
  | readCopySt
  | readCopyStIdentity
  | readCopyStOther
  | findCopyMem
  deriving DecidableEq, Repr, Inhabited

namespace TheoryRule

/-- The theorems a rule is — one per sort it is stated at.

A paper rule is one rule, but this package states it once per algebra: `findPath`
is `StValue.find_cons` over `findSt`, the reader that stops at a memory view,
and `StValue.find_cons_view` over `find`, the one that crosses into it.  So
the table is a list, tried in order, and not a single name.

A total match, so the table cannot fall behind the enumeration; double-backtick
names, so it cannot fall behind the theories. -/
def lemmaNames : TheoryRule -> List Lean.Name
  | selectStoreEqual      => [``StValue.selectOnStore]
  | selectStoreDifferent  => [``StValue.selectOnStore]
  | selectEmptyStruct     => [``StValue.selectOnEmptyStorage]
  | findEmptyPath         => [``StValue.findDefinitionEmpty]
  | findPath              => [``StValue.find_cons, ``StValue.find_cons_view]
  | saveEmptyPath         => [``StValue.saveOnEmpty]
  | savePath              => [``StValue.save_cons]
  | singletonPath         => [``StValue.singletonPath]
  | findSingleton         => [``StValue.findDefinitionCons]
  | saveSingleton         => [``StValue.save_single]
  | findOnSave            => [``StValue.find_save_same]
  | findOnSaveDifferent   => [``StValue.find_save_frame]
  | findOnSavePrefix      => [``StValue.find_save_prefix]
  | findOnSaveExtends     => [``StValue.find_save_extends]
  | delAtEmpty            => [``StValue.delAtEmpty]
  | findDelAt             => [``StValue.find_delAt_same]
  | findDelAtOutside      => [``StValue.find_delAt_frame]
  | findDelAtExtends      => [``StValue.find_delAt_extends]
  | defValResolve         => [``StValue.defaultValueStruct, ``StValue.defaultValueInt,
                              ``StValue.defaultValueBool]
  | delValueStruct        => [``StValue.delValueStruct]
  | delValueDefault       => [``StValue.delValueDefault]
  | delValueCast          => [``StValue.delValueCast, ``StValue.delValueCast_asInt,
                              ``StValue.delValueCast_asBool]
  | selectDelNodeRef      => [``StValue.selectStDelNodeRef]
  | selectDelNodeDefault  => [``StValue.selectStDelNodeDefault]
  | selectDelNodeIndex    => [``StValue.selectStDelNodeIndexStruct]
  | selectOnDelAt         => [``StValue.selectOnDelAtCons]
  | readWriteEqual        => [``Memory.readOnWrite]
  | readWriteDifferent    => [``Memory.readOnWrite]
  | readAddEqual          => [``Memory.readAddEqual]
  | readAddDifferent      => [``Memory.readAddDifferent]
  | readEmptyMem          => [``Memory.readFromEmptyMemory]
  | defaultPrim           => [``Memory.defaultDefInt]
  | defaultIdentity       => [``Memory.defaultDefIdentity]
  | readREmptyPath        => [``Memory.readREmptyPath]
  | readRSingleton        => [``Memory.readREmpty]
  | readRPath             => [``Memory.readRCons]
  | newAddSame            => [``Memory.newAddSame]
  | newAddDifferent       => [``Memory.newAddDifferent]
  | newWrite              => [``Memory.newFromWrite]
  | newEmptyMem           => [``Memory.newFromEmptyMemory]
  | readCopySt            => [``Memory.readCopySt]
  | readCopyStIdentity    => [``Memory.readCopyStIdentity]
  | readCopyStOther       => [``Memory.readCopyStOther]
  | findCopyMem           => [``StValue.findCopyMem]

/-- Every rule of the enumeration, for the parity check and for `#theory_rules`. -/
def all : List TheoryRule :=
  [ .selectStoreEqual, .selectStoreDifferent, .selectEmptyStruct,
    .findEmptyPath, .findPath, .saveEmptyPath, .savePath,
    .singletonPath, .findSingleton, .saveSingleton,
    .findOnSave, .findOnSaveDifferent, .findOnSavePrefix, .findOnSaveExtends,
    .delAtEmpty, .findDelAt, .findDelAtOutside, .findDelAtExtends, .defValResolve,
    .delValueStruct, .delValueDefault, .delValueCast,
    .selectDelNodeRef, .selectDelNodeDefault, .selectDelNodeIndex, .selectOnDelAt,
    .readWriteEqual, .readWriteDifferent, .readAddEqual, .readAddDifferent,
    .readEmptyMem, .defaultPrim, .defaultIdentity,
    .readREmptyPath, .readRSingleton, .readRPath,
    .newAddSame, .newAddDifferent, .newWrite, .newEmptyMem,
    .readCopySt, .readCopyStIdentity, .readCopyStOther, .findCopyMem ]

/-- The rules this package states that the paper does not declare — Lean's
additions, which the paper is to gain: this repository is the source of truth
and the paper is ported from it.  `./scripts/check-theory-rules.mjs` reads the
list and reports these as "Lean-only (to add to the paper)" instead of
failing on them.  The four `findOnSave*` are the read-of-a-write shortcuts the
paper reaches by unfolding, `findDelAtExtends` is the fourth's twin over a
delete, `selectOnDelAt` is one selector out of a delete,
and `readRSingleton` the one-segment `readR`. -/
def paperAbsent : List TheoryRule :=
  [ .findOnSave, .findOnSaveDifferent, .findOnSavePrefix, .findOnSaveExtends,
    .findDelAtExtends, .selectOnDelAt, .readRSingleton ]

/-- Every Lean-only rule is a rule of the enumeration. -/
theorem paperAbsent_sub : paperAbsent.all (all.contains ·) = true := by decide

/-- The paper's own spelling of a rule name, which is the constructor's. -/
def paperName (r : TheoryRule) : String :=
  ((repr r).pretty.splitOn ".").getLast!

end TheoryRule

open Lean Elab Command in
/-- The rule table, one line per rule: the paper's name and the theorem it is.
Read it instead of grepping two files; it is also what tells you a rule exists
before you write it on an arrow. -/
elab "#theory_rules" : command => do
  let env <- getEnv
  let mut out : Array String := #[]
  for r in TheoryRule.all do
    for n in r.lemmaNames do
      let mark := if env.contains n then "" else "   -- MISSING"
      out := out.push s!"{r.paperName}  ->  {n}{mark}"
  logInfo (String.intercalate "\n" out.toList)

end Theory
end Solidity
