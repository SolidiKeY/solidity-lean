# Source definitions S00 and S01: grammar, declarations, typing

The first two independent source-definition workstreams of
[the roadmap](../coverage-plan.md) ("Independent source definitions"). They
define the source side of G01's `SourceSpec` (`Solidity/Roadmap/Contracts.lean`)
from the pinned language, independently of the compiler, of the intrinsic
programs and of the solc JSON importer. Checkpoints 2 and 3 of lane V03.

All modules live under `Solidity/Source/`. They import nothing outside it and
G01's contracts, which `scripts/check-noncircular.mjs` enforces
([roadmap-g07-gates.md](roadmap-g07-gates.md) §3). No existing intrinsic type
is reused, so no correspondence theorem is owed (the gate's `DATATYPES` list
is empty).

## S00: the pinned grammar as intrinsic syntax

### Inputs

- The ANTLR grammar of solc 0.8.38 (`SolidityParser.g4`, `SolidityLexer.g4`
  at `argotorg/solidity` commit `1835d247`), vendored unmodified in
  `tests/upstream/grammar-0.8.38/`. The repository's
  `tests/upstream/solidity-0.8.38.tar.gz` holds only the test tree, not
  `docs/grammar/`. The files were fetched from the pinned commit, and their
  SHA-256 hashes equal G00's pins in `docs/solidity-features.json`, which
  `scripts/check-source-grammar.mjs` checks on every run.
- G00's manifest (`docs/solidity-features.json`, 212 features) for the
  feature ids and scopes.

### Modules

| Module | Content |
|---|---|
| `Solidity/Source/Syntax.lean` | `Cat` (28 categories) and `Syn : Cat → Type` (112 constructors), with the datatypes for elementary types, operators, literals, visibility and locations |
| `Solidity/Source/Ctor.lean` | The constructor index `Ctor`, `Ctor.all` (complete: `Ctor.mem_all`), `Syn.ctor`, `Syn.children`, `Syn.nodes`, the exclusions `Excl` and the precise rejection `Syn.rejections` |
| `Solidity/Source/Upstream.lean` | The explicit mapping from grammar rules and labels, and from manifest features, to constructors (`grammarCtors`, `grammarData`, `featureCtors`, `featureLexical`) and `Ctor.grammar_covers` |
| `Solidity/Source/Decls.lean` | The typed declaration graph: `Decl`, `Syn.decls`, its edges `Decl.refs`, and `Syn.decls_ctor` |
| `Solidity/Source/Examples.lean` | Controls: an in-profile counter and four rejected programs, with their rejections and declarations computed by the kernel |

### Design

**Intrinsic by category.** `Syn c` is the syntax of category `c`. A slot holds
exactly the category the grammar names, so an expression never stands where
a statement or type name is expected. Repetition and options are the
categories `list c` and `opt c`, so the family is a single indexed inductive
without nesting: every function over it is structural and reduces in the
kernel. One exception: a function over a fixed non-variable index, such as
`Syn (.list (.part t))`, falls back to well-founded recursion, which does not
reduce. So `Syn.collect` walks every category.

**Intrinsic contexts.** Statements are indexed by `SCtx` (inside a loop,
inside `unchecked`). `break`/`continue` exist only at `loop = true`. An
`unchecked` block, a block item and not a statement as in the grammar, exists
only at `unchecked = false` and makes its body `unchecked = true`. These are
solc's syntax-checker rules ("break has to be in a loop"; unchecked blocks
cannot be nested), which the ANTLR grammar alone does not state. A body
(`SCtx.body`) starts outside both.

**Minimum counts and at-most-once flags.** Where the grammar demands one or
more elements, the first is a separate argument: struct members, enum values,
import aliases, call options, inline-array elements, catch clauses,
non-empty tuple slots, the first declaration of a tuple declaration, the
parameters of `fallback(...)` with `returns`. Flags the grammar allows at most
once are `Option`/`Bool` fields; their source order is lexical (G08–G11).
`elementaryTypeName[false]` positions (expressions and mapping keys) carry a
proof that the type is not `address payable`.

**Lexical content** is abstracted: identifiers are strings; a decimal literal
is its exact value (mantissa, fractional digits, exponent); a hexadecimal
literal keeps its digits and whether it is a checksummed address spelling;
strings are their concatenated fragments. `int`/`uint` are `int256`/`uint256`.
`fixedMxN` keeps the token's raw `M`, `N`; solc's bounds (8 ≤ M ≤ 256, 8 | M,
N ≤ 80) are a typing judgment (S01), as in solc's scanner.

**Yul** follows the grammar's rules, without its one- versus many-variable
restrictions and the "at least one case or a default" of `switch`. It is
rejected whole (`inlineAssembly`), so these approximations change no verdict.

### Precise rejection

`Syn.excl` classifies the root of a tree: assembly and every Yul constructor
(`inlineAssembly`); `layout at` (`storageLayout`), both approved exclusions
(G00 Q1); `>>>` and `>>>=` (`unsignedRightShift`); the `years` unit
(`removedUnits`); and `pragma experimental solidity`
(`removedGenericSolidity`). The last three are rejected by solc 0.8.38 itself
(manifest scope `upstream`). `Excl.id` is the manifest id; the script checks
each id's scope.

`Syn.rejections` collects the exclusions of all nodes. Two theorems state it:

- `Syn.rejections_of_sub`: an excluded construct anywhere in a tree (`Syn.Sub`,
  the reflexive-transitive subterm relation over `Syn.children`) is among the
  tree's rejections, with its feature.
- `Syn.rejections_witnessed`: every rejection is triggered by some node.

Both rest on `Syn.nodes_eq`: a tree's nodes are its root's and its
children's. The other 25 approved exclusions are not syntax. They are
builtins and members (`delegatecall`, `gasleft`, `block.number`, …) or
options (`{gas: …}`, `{salt: …}`), so S01's name resolution refuses them.

### Upstream mapping

`grammarCtors` relates each of the grammar's 101 structured rules and
labelled alternatives (every `expression#Label` among them) to the
constructors that represent it. `grammarData` relates the 18 rules
represented by a datatype or field: identifiers, paths, visibility,
mutability, operators, literals, assembly flags. The two tables partition the
grammar's 119 rules and labels.
`Ctor.grammar_covers` (`decide +kernel`) proves that every constructor except
the four structural ones represents some rule. `scripts/check-source-grammar.mjs`
checks the converse against the vendored file: every rule and label is a key
of exactly one table, every key exists, and every named constructor is a
`Syn` constructor.

`featureCtors` maps 103 manifest features to constructors. `featureLexical`
names the 3 syntax features below the abstract syntax (comments, invalid
lexemes, reserved keywords; G08). The script checks that every manifest
feature citing the parser grammar has a row, and that every id exists.

### Declaration graph

`Syn.decls` lists a unit's declarations (contracts, interfaces, libraries and
their members, file-level functions, constants and types). Each carries its
kind, name, enclosing contract, file-level flag and its own syntax at the
category its kind fixes (`DeclKind.cat`). `Syn.decls_ctor` proves that each
node's root constructor is its kind's. The edges are `Decl.refs`, the names a
declaration mentions (`Syn.paths`: type paths, bases, modifiers, `using`
targets, overrides, identifiers). S01 resolves them.

### Controls (`Solidity/Source/Examples.lean`)

| Theorem | Statement |
|---|---|
| `counter_inProfile` | `contract Counter { uint256 public count; function inc() external { count++; } }` has no rejection |
| `counter_decls`, `counter_refs` | its three declarations with kinds and scopes; its edges |
| `withAssembly_rejected` | an `assembly { }` inside a function is rejected as `inlineAssembly` |
| `withLayout_rejected`, `withShr_rejected`, `withYears_rejected` | `layout at 1`, `count >>> 1`, `1 years` |
| `loopBreak_inProfile` | `while (true) { break; }` |

The trees are written by hand from their text. Parsing text into `Syn`, the
`Parses` relation of `SourceSpec`, is G08–G11's: lexing and the grammar as a
relation with precedence and associativity. S00 fixes the target of that
relation.

### What S00 does not do

- No parser or printer, and no `Parses` relation (G08–G11).
- Comments, NatSpec, source locations and underscore spellings are not
  represented (G08).
- Struct fields, enum values and parameters are not graph nodes; they are
  members of their declaration's node.

### Gates (S00)

Recorded in [Handoff](#handoff-s00).

### Review (S00)

To be filled.

### Handoff (S00)

To be filled.
