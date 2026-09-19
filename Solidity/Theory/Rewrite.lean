import Solidity.Theory.Storage
import Solidity.Theory.Memory
import Solidity.Theory.CrossDomain

/-!
# The theory's rewrite rules, under the paper's names

The calculus layer has `Rules.lean`: an enumeration of rule names, a table of
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

Four rules of `sections/signature.tex` have no constructor, deliberately:
`selectDelNodeMap` and `selectOnSaveEmptyMap` are the architectural gap
`docs/lean-key-rule-map.md` records (a `Seg` carries no `MapField`), and the
two `expandInUintN`/`expandInIntN` families are the arithmetic the paper's own
"not implemented" section lists.  `delValueCast` is subsumed by `asStruct`, and `singletonPath` by paths being
`List Seg` -- the paper's `⟨f⟩` is `[f]`, so the rule is `rfl`.
`./scripts/check-theory-rules.mjs` carries each of those arguments beside the
name it excuses.
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
  | defValResolve
  | delValueStruct
  | delValueDefault
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
is `StValue.find_cons` over a plain `Struct` and `XStruct.findPath` over one that
may hold a copy view, and a chain applies whichever its line is written in.  So
the table is a list, tried in order, and not a single name.

A total match, so the table cannot fall behind the enumeration; double-backtick
names, so it cannot fall behind the theories. -/
def lemmaNames : TheoryRule -> List Lean.Name
  | selectStoreEqual      => [``StValue.selectOnStore, ``XStruct.selectOnStore]
  | selectStoreDifferent  => [``StValue.selectOnStore, ``XStruct.selectOnStore]
  | selectEmptyStruct     => [``StValue.selectOnEmptyStorage]
  | findEmptyPath         => [``StValue.findDefinitionEmpty, ``XStruct.findEmptyPath]
  | findPath              => [``XStruct.findPath, ``StValue.find_cons]
  | saveEmptyPath         => [``StValue.saveOnEmpty]
  | savePath              => [``StValue.save_cons]
  | findSingleton         => [``XStruct.findSingleton, ``StValue.findDefinitionCons]
  | saveSingleton         => [``StValue.save_single]
  | findOnSave            => [``StValue.find_save_same]
  | findOnSaveDifferent   => [``StValue.find_save_frame]
  | findOnSavePrefix      => [``StValue.find_save_prefix]
  | findOnSaveExtends     => [``StValue.find_save_extends]
  | delAtEmpty            => [``StValue.delAtEmpty]
  | findDelAt             => [``StValue.find_delAt_same]
  | findDelAtOutside      => [``StValue.find_delAt_frame]
  | defValResolve         => [``StValue.defaultValueStruct, ``StValue.defaultValueInt,
                              ``StValue.defaultValueBool]
  | delValueStruct        => [``StValue.delValueStruct]
  | delValueDefault       => [``StValue.delValueDefault]
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
  | readCopySt            => [``XMemory.readCopySt]
  | readCopyStIdentity    => [``XMemory.readCopyStIdentity]
  | readCopyStOther       => [``XMemory.readCopyStOther]
  | findCopyMem           => [``XStruct.findCopyMem]

/-- Every rule of the enumeration, for the parity check and for `#theory_rules`. -/
def all : List TheoryRule :=
  [ .selectStoreEqual, .selectStoreDifferent, .selectEmptyStruct,
    .findEmptyPath, .findPath, .saveEmptyPath, .savePath,
    .findSingleton, .saveSingleton,
    .findOnSave, .findOnSaveDifferent, .findOnSavePrefix, .findOnSaveExtends,
    .delAtEmpty, .findDelAt, .findDelAtOutside, .defValResolve,
    .delValueStruct, .delValueDefault,
    .selectDelNodeRef, .selectDelNodeDefault, .selectDelNodeIndex, .selectOnDelAt,
    .readWriteEqual, .readWriteDifferent, .readAddEqual, .readAddDifferent,
    .readEmptyMem, .defaultPrim, .defaultIdentity,
    .readREmptyPath, .readRSingleton, .readRPath,
    .newAddSame, .newAddDifferent, .newWrite, .newEmptyMem,
    .readCopySt, .readCopyStIdentity, .readCopyStOther, .findCopyMem ]

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
