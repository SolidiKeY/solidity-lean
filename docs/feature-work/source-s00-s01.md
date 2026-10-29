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

**What "intrinsic" means here.** `Syn` is the parse target, before any name
is resolved. It is indexed by syntactic category and by the statement
context, not by a typing context: names are strings, because binding them is
S01's judgment (its resolution module). It is the one
pre-resolution layer; no untyped intermediate layer follows it. S01's
judgments and S02's semantics are defined over resolutions
([intrinsic.md](../intrinsic.md)). Every invariant that the grammar and
solc's syntax checker decide by syntax alone is either encoded in the index
or decided by `Syn.rejections`. The rest are S01 judgments (table below).

**Intrinsic by category.** `Syn c` is the syntax of category `c`. A slot holds
exactly the category the grammar names, so an expression never stands where
a statement or type name is expected. Repetition and options are the
categories `list c` and `opt c`, so the family is a single indexed inductive
without nesting, and every function over it is structural. One caveat: a
function over a fixed, non-variable index, such as `Syn (.list (.part t))`,
falls back to well-founded recursion, which does not reduce. So `Syn.collect`
walks every category.

**Intrinsic contexts.** Statements are indexed by `SCtx` (inside a loop,
inside `unchecked`). `break`/`continue` exist only at `loop = true`. An
`unchecked` block, a block item and not a statement as in the grammar, exists
only at `unchecked = false` and makes its body `unchecked = true`. These are
solc's syntax-checker rules ("break has to be in a loop"; unchecked blocks
cannot be nested), which the ANTLR grammar alone does not state. The theorems
`no_break_outside_loop`, `no_continue_outside_loop` and `no_nested_unchecked`
(`Solidity/Source/Examples.lean`) state them. A body (`SCtx.body`) starts
outside both.

**Minimum counts and at-most-once flags.** Where the grammar demands one or
more elements, the first is a separate argument: struct members, enum values,
import aliases, call options, inline-array elements, catch clauses, the first
(possibly empty) tuple slot, the first declaration of a tuple declaration,
the parameters of `fallback(...)` with `returns`. Flags the grammar allows at
most once are `Option`/`Bool` fields; their source order is lexical
(G08–G11). `elementaryTypeName[false]` positions (expressions and mapping
keys) carry a proof that the type is not `address payable`.

**Lexical content** is abstracted (G08 owns spellings):

- identifiers are strings;
- a decimal literal is its exact value (mantissa, fractional digits,
  exponent), so one value has several spellings;
- a hexadecimal literal keeps its digits and whether its case is a valid
  EIP-55 checksum, a flag the lexer computes;
- string literals are the bytes of their fragments after escapes (`\xNN`
  may make them invalid UTF-8);
- pragmas are their words.

`int`/`uint` are `int256`/`uint256`. `fixedMxN` carries solc's bounds
(`FixDims`: `8 ≤ M ≤ 256`, `8 ∣ M`, `N ≤ 80`), since solc's scanner reads any
other spelling as an identifier. The ANTLR lexer's own `Fixed`/`Ufixed`
tokens (`N ≥ 1`, and two or more digits for `ufixed`) differ, and solc
decides. Paths, pragma words and identifiers are not checked non-empty.

**Yul** follows the grammar's rules with four over-approximations: no
one-versus-many-variable restriction, possibly empty assignment paths,
expression statements that may be any expression (not only a call), and a
`switch` that may have neither a case nor a default. Assembly is rejected
whole, except the canonical rethrow, which these approximations do not
reach.

**Kernel cost (Gate G0).** [Gate G0](../intrinsic.md#gate-g0-kernel-evaluated-code)
forbids `match` on an indexed family in *hot* kernel-evaluated code (the
typed run and symex). `Syn.ctor`, `children`, `placeholders`, `nodes`,
`excl`, `paths` and `collect` are `match`es on `Syn`. They are exempt as
static checks on one tree, evaluated once per source unit, not inside symex,
like the elaboration-time code G0 names. If G08–G11 or S05 evaluate them in
the kernel on large units, they move to the `Syn.rec` form with
`implemented_by` twins. The generated definitions keep that change
mechanical (`scripts/source-ctors.py`).

### SyntaxChecker rules and their owners

solc rejects some programs the grammar accepts: some in its syntax checker,
others in its type checker. Each is encoded, rejected or owned:

| Rule | Where | Owner |
|---|---|---|
| `break`/`continue` only inside a loop | `SCtx.loop` | S00 (intrinsic) |
| `unchecked` blocks do not nest | `SCtx.unchecked` | S00 (intrinsic) |
| a concrete modifier body has a placeholder; no placeholder inside `unchecked` | `Excl.invalidModifierBody` | S00 (rejection) |
| a placeholder only in a modifier | an undeclared `_` elsewhere | S01 (resolution) |
| a variable declaration only as a block item, not as an `if`/loop body | — | S01 well-formedness |
| free functions: no visibility, a body; contract functions: a visibility | — | S01 well-formedness |
| `using … for *` and `global` only where allowed | — | S01 well-formedness |
| no named returns in function types; no unit on a hex number | — | S01 well-formedness |
| known pragmas, one `abicoder` | `Syn.pragma` words | S01 (settings) |
| interface and library bodies; `receive` `external payable`; the fallback signature; `emit`/`revert` targets; `constant`/`immutable`/`transient` combinations | — | S01 (typing) |

### Precise rejection

`Syn.excl` classifies the root of a tree. It rejects:

- assembly (`inlineAssembly`), except the canonical whole-buffer rethrow
  `assembly { revert(add(D, 32), mload(D)) }` (`isRethrow`; manifest
  `canonicalRethrow`, in the profile). That `D` is a `bytes memory` variable
  is S01's check. The Yul body is rejected with its assembly;
- `layout at` with a non-literal base (`storageLayout`); a number-literal
  base is in the profile (`logicalStorageBase`, G00);
- `>>>` and `>>>=` (`unsignedRightShift`);
- the `years` unit (`removedUnits`);
- `pragma experimental solidity` (`removedGenericSolidity`);
- a concrete modifier body without a placeholder, and an `unchecked` block
  containing one (`invalidModifierBody`).

The first two are approved exclusions (G00 Q1); the other four are rejected
by solc 0.8.38 itself (manifest scope `upstream`). `Excl.id` is the manifest
id, and `Excl.ctors` lists the constructors at which each exclusion is
decided. `Syn.excl_ctor` proves that list exhaustive, and `Excl.mapped`
proves each listed constructor is in the feature's `featureCtors` row.

`Syn.rejections` collects the exclusions of all nodes. Two theorems state it:

- `Syn.rejections_of_sub`: an excluded construct anywhere in a tree
  (`Syn.Sub`, the reflexive-transitive subterm relation over `Syn.children`)
  is among the tree's rejections, with its feature.
- `Syn.rejections_witnessed`: every rejection is triggered by some node.

Both rest on `Syn.nodes_eq` (a tree's nodes are its root's and its
children's), and on `Syn.children` listing every `Syn`-typed field.
`scripts/source-ctors.py --check` fails when a generated block differs from
the constructors' signatures.

**Exclusions by stage.** The manifest has 30 `exclude` and 7 `upstream`
rows:

- S00 decides six on syntax: the two approved exclusions above and four
  upstream ones.
- `memoryLayout` and `transientLayout` are reachable only through assembly,
  so `inlineAssembly` covers them.
- `invalidLexemes` and `reservedKeywords` are lexical (G08).
- The remaining 25 are decided after syntax, as `featureElsewhere` records:
  - builtins and members (`gasleft`, `block.number`, `tx.origin`,
    `a.delegatecall`, `msg.data`, `selfdestruct`, …), the call options
    `{gas: …}`/`{salt: …}`, and `removedAliases`, by S01
    (`Builtin.status`, `addressMemberStatus`, `callOptionStatus`);
  - `eventLog`, an observation (S04.02);
  - `machineResources`, the G01 contracts' resource reading.

The manifest lists `fallback(bytes) …` both under `fallbackFunction`
(`model`) and under `rawCalldata`/`rawReturndata` (`exclude`). S00 admits the
syntax. Which reading applies is a manifest question for G00's owners
(recorded under Remaining).

### Upstream mapping

`grammarCtors` relates each of the grammar's 101 structured rules and
labelled alternatives (every `expression#Label` among them) to the
constructors that represent it. `grammarData` relates the 18 rules
represented by a datatype or field: identifiers, paths, visibility,
mutability, operators, literals, assembly flags. The two tables partition the
grammar's 119 rules and labels. `Ctor.grammar_covers` (`decide +kernel`)
proves that every constructor except the four structural ones represents
some rule.

`featureCtors` maps the manifest's syntax features to constructors.
`featureLexical` names the 3 lexical ones (G08). `featureElsewhere` names the
excluded features decided after syntax, with their stage.

`scripts/check-source-grammar.mjs` checks these tables against the files:

- the grammar files' hashes are G00's pins;
- every rule and label is a key of exactly one grammar table, and every key
  exists;
- every named constructor is a `Syn` constructor;
- each structured rule's constructors produce the rule's category: an
  expression label an expression, a statement rule a statement, a definition
  a body or top-level element, a Yul rule Yul;
- every feature id exists and is listed once;
- every manifest feature citing the grammar or of category `lexical` has a
  row;
- every `Excl` id has scope `exclude`/`upstream`;
- every excluded or upstream-rejected feature is an `Excl`, lexical, or in
  `featureElsewhere`.

The category check is coarse: it cannot tell `whileStatement` from
`forStatement`. The rows themselves were checked by the reviewers.

### Declaration graph

`Syn.decls` lists a unit's declarations in source order: contracts,
interfaces, libraries and their members, and file-level functions, constants
and types. Each carries its kind, name, enclosing contract, file-level flag
and its own syntax at the category its kind fixes (`DeclKind.cat`). Its
position is its identity (`Syn.graph`). `Syn.decls_ctor` proves that each
node's root constructor is its kind's.

The edges are `Decl.refs`, each with a kind:

- `inherit`: a contract's or interface's `is` bases;
- `use`: every other mention in a declaration's own node (types, modifiers,
  `using` targets, overrides, identifiers).

A contract's edges are its bases only; its members' mentions are the
members' edges. S01 resolves them. Not graph nodes:

- imports and `using` directives, which S01 reads from the tree;
- struct fields, enum values, parameters and locals, which are scopes of
  S01's typing.

Not proved: completeness, that every declaration constructor in a unit is
collected. `Syn.collect` walks every list and top-level element; a proof
against `Syn.Sub` is open.

### Controls (`Solidity/Source/Examples.lean`)

| Theorem | Statement |
|---|---|
| `counter_inProfile`, `counter_decls`, `counter_refs` | `contract Counter { uint256 public count; function inc() external { count++; } }`: no rejection; its three declarations with kinds and scopes; its edges |
| `withAssembly_rejected`, `notRethrow_rejected`, `rethrow_inProfile` | general assembly is rejected; the canonical rethrow is not |
| `withLayout_rejected`, `withLiteralLayout_inProfile` | `layout at B` is rejected; `layout at 1` is not |
| `withShr_rejected`, `withYears_rejected`, `withGeneric_rejected`, `pragmaVersion_inProfile` | `count >>> 1`, `1 years`, `pragma experimental solidity` are rejected; `pragma solidity ^0.8.0` is not |
| `modifier_inProfile`, `abstractModifier_inProfile`, `modifierNoPlaceholder_rejected`, `uncheckedPlaceholder_rejected` | modifier placeholders |
| `modifierShr_rejected`, `two_rejected` | an exclusion nested in a modifier; two rejections at once |
| `loopBreak_inProfile`, `no_break_outside_loop`, `no_continue_outside_loop`, `no_nested_unchecked` | the intrinsic contexts |

The trees are written by hand from their text. Parsing text into `Syn` (the
`Parses` relation of `SourceSpec`: lexing, and the grammar as a relation with
precedence and associativity) is G08–G11's. S00 fixes the target of that
relation.

### What S00 does not do

- No parser or printer, and no `Parses` relation (G08–G11).
- Comments, NatSpec, source locations and underscore spellings are not
  represented (G08).
- Struct fields, enum values and parameters are not graph nodes; they are
  members of their declaration's node.
- The syntax-level verdict decides only the six syntax exclusions; G01's
  `InProfile` is on resolutions (S01 and later).
- The `fallback(bytes)` manifest conflict (above) is not resolved.

### Gates (S00)

Recorded in [Handoff](#handoff-s00).

### Review (S00)

A read-only finder and a separate skeptic reviewed the first push
(`2aec5be`), neither using the Lean server. Their findings and what was done:

**Fixed**

- **Wrong verdicts.** Every `layout at` was rejected, although literal bases
  are in the profile (`logicalStorageBase`). Every assembly was rejected,
  although the canonical rethrow is (`canonicalRethrow`). Both are now
  admitted, with positive and negative controls.
- **A missed upstream rejection.** `invalidModifierBody` is now an `Excl`,
  computed from `Syn.placeholders`, with four controls.
- **Pragmas.** The text was split on spaces only, so `pragma experimental`
  with a tab or newline before `solidity` escaped, and `String.splitOn` does
  not reduce. Pragmas are now word lists.
- **Unrepresentable literals.** String literals with `\xNN` escapes (not valid
  UTF-8) had no tree. They are bytes now.
- **Fixed-point names.** Out-of-bounds `fixedMxN`, which solc lexes as an
  identifier, had two trees. `FixDims` now carries solc's bounds.
- **The script checked keys, not values.** It now checks each row's
  constructor categories; features cited from the lexer or of category
  `lexical`; every excluded or upstream feature (`Excl`, lexical, or
  `featureElsewhere` with its stage); `Excl` ids against `inductive Excl`;
  duplicate rows. It reads the tables without comments.
- **`Ctor`/`children` were hand-maintained.** They are generated and checked
  (`scripts/source-ctors.py --check`, run by `check-g07.mjs`).
- **`Excl.mapped` proved only that a row exists.** `Syn.excl_ctor` now proves
  `Excl.ctors` exhaustive, and `Excl.mapped` puts every listed constructor in
  the feature's row; `Excl.mem_all` is the completeness proof.
- **Feature rows.** Corrected: `stateMutability`, `visibility`,
  `overrideDeclarations`, `valueTypes`, `addressTypes`, `inlineAssembly`
  (every Yul constructor). Added: `addressLiterals`, `logicalStorageBase`,
  `modifierPlaceholder`, `invalidModifierBody`.
- **The declaration graph.** It had no identities and no edge kinds, and a
  contract repeated its members' mentions. Declarations now have positions
  (`Syn.graph`), edges have kinds (`inherit`/`use`), and a contract's edges
  are its bases.
- **The intrinsic contexts had no negative controls.** Added
  `no_break_outside_loop`, `no_continue_outside_loop` and
  `no_nested_unchecked`.
- **Docs.** The exclusion count (28, not 25, beyond the two S00 handled
  first) and the stage of each exclusion are now right. Added: the Yul
  approximations, the `FnName` docstring (a warning, not an error), the
  SyntaxChecker rule table, the Gate G0 exemption, and what "intrinsic"
  means for a pre-resolution layer.

**Not fixed, recorded**

- Not encoded intrinsically: the syntax-checker rules the table assigns to
  S01 (variable declarations as non-block bodies, free-function attributes,
  `using … for *`, named returns in function types, units on hex numbers).
  They are S01 well-formedness checks.
- Declaration-collection completeness against `Syn.Sub` is not proved.
- Rows are checked by category, not by exact rule.
- The `fallback(bytes)` conflict between manifest rows is G00's.
- No elaboration times measured per module beyond the build log (Handoff).

### Handoff (S00)

To be filled.
