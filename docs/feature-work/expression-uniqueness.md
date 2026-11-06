# SOL-EU: certified expression yield uniqueness

## Current status (Claude VM continuation, 2026-11-05)

This section supersedes the Codex-VM status text below wherever they differ.

- **Evidence moved out (H44).** Commit e48d82a2 removed 1137 generated files
  from `tests/sol-expression-uniqueness/`: everything under `evidence/` and the
  `kernel-{declarations,emissions,module-declarations}.json(.gz)` dumps. It
  removed no `.lean` file. Only `bulk-manifest.json` indexes them, and the copies
  stay on the Codex VM. Every later reference below to `evidence/…`, a
  `*.inside.json` or `*.outer.json`, or a review-verdict JSON names a file that
  is **not in git**; it is history, not something the repository can check now.
- **Codex tooling removed.** `bounded.py`, `inside.py`, `serial-build.py`,
  `runtime-bin/lake`, `runtime-lakefile.toml` and `runtime-mcp.sh` are deleted.
  The runtime-enforcement paragraphs below describe the Codex VM only.
- **Checker.** `scripts/check-sol-expression-uniqueness.py` reads the kernel axiom
  report from the `#guard_msgs` docstrings of `AxiomPins.lean`, which the
  library build re-checks. `--checkpoint --build-log LOG` requires a completed
  `./run-lean.sh` log from this checkout. The Codex evidence checks (kernel
  environment dumps, 130 solc parsing observations) run only with
  `--external-evidence`. They were not re-run here: the pinned soljson 0.8.38
  (sha256 `6c74ffba…`) cannot be downloaded from this VM, and the npm `solc@0.8.38`
  build hashes differently (`0b15fcb2…`).
- **Registration.** `register.sh` already lists all 100 modules in the library
  roots. The module-map rows are in `docs/module-map/frontend.d/expression-uniqueness.md`,
  and the axiom pins go through `scripts/g07-axiom-pins.d/` (`check-axiom-pins.mjs --write`).
- **Post-split reviews (read-only, no Lean server).** See "Claude-VM reviews" at the end.

Status: the original certified uniqueness theorem and accepted-tree corollaries
are kernel-checked by exhaustive intrinsic induction. All1241declaration axiom pins and
all2323unique logical declaration type/axiom audits pass. H26 runtime setup remains resolved without changing
limits. The full assignment is NOT complete: frozen integration and required
global gates remain open. No certified ambiguity has been found.

Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Branch: `codex/solidity-sol2-20261104/expression-uniqueness`.
Repository: `/workspace/solidity-lean`. The previous inventory-only commit
`7642fc89d68bc9ee12acceafcd829902d532f960` and its failed setup probes remain honest
history. The current immutable packet records its own exact committed head.

## Original theorem target (kernel-proved)

`CertifiedYieldUnique` in `Statement.lean` records this proposition in the existing
namespace `Solidity.Frontend.ExpressionUniqueness`:

```lean
∀ (a b : Solidity.Source.Syn .expr) (ts : List Solidity.Frontend.Checked.Tok),
  a.Derives ts → a.prec = true →
  b.Derives ts → b.prec = true → a = b
```

The original definition is preserved exactly. certifiedYieldUnique in the Certified module
inhabits it; certified_expression_yield_unique exposes the original premises. Layouts
are independently existential through the existing `Syn.Derives`. Equivalently
quantify `La Lb` and require `a.toks La = some ts` and `b.toks Lb = some ts`.
Layout equality is neither a premise nor a conclusion. Successful `Syn.toks`
consumes the entire layout. `LayoutBoundary` now constructs a genuine fully
consumed witness for the flattened word of any successful partial expression
yield. This does not equate that fresh witness with the original layout.
No second AST, parser edit, new producer assumption or theorem exclusion exists.

The accepted-tree corollary must combine `parseCat_sound` with the public
uniqueness theorem: an accepted `parseCat expr src` tree equals any certified
expression deriving that same successful lexical result's tokens. Parser
determinism alone does not establish this. parseCat_expression_accepted_unique in the Accepted module proves this using the original
parseCat_sound certificate, with a same-source cross-producer corollary as well.

## Exhaustive inventory and scope

`tests/sol-expression-uniqueness/constructors.json` enumerates all 29 expression
constructors in intrinsic declaration order, boundaries, root levels, root
conditions, layouts and proved reconstruction obligations. `constructor-controls.json`
assigns a kernel-checked accepted-root fixture to every constructor.
`declarations.json` enumerates all 1241 source declarations with source signatures;
`signatures.lean` and its kernel output report their actual types and axiom sets.
The one hundred modules are proposed for coordinator registration, with module-map rows,
in `registration-manifest.json`. Shared roots and maps remain frozen. The Bracket
kind also has its three constructors, recursors and deriving instances generated
by Lean; it describes token delimiters, not expression syntax.

Root conditions are conjoined with recursive `Syn.prec` for every child. The ten
left-associative levels require left level at least p and right level at least
p+1. Exponentiation requires left at least 13, right at least 12. Conditional
requires condition at least 2 and false branch at least 1; assignment requires
left at least 2. Unrestricted root slots still satisfy recursive precedence.

Reconstruction must include `nil`/`cons`, `none`/`some`, positional/named arguments,
`namedArg`, and recursive type/parameter dependencies (`elem`, `fnType`, `mapping`,
`userType`, `array`, `param`). Type arrays contain optional expression lengths.
These obligations remain within the original expression theorem, including
function types embedded in expressions. Statement/function/unit uniqueness is
outside scope. `metaType` refuses only a DIRECT forbidden type constructor;
arrays containing function, mapping or address-payable types must NOT be excluded.

Member name `address` emits `Tok.elem .address`; other names emit `Tok.ident`.
Tuple parentheses are syntax: `(e)` retains its one-component tuple node.
Empty tuple components and empty positional/named arguments retain their
commas, parentheses and braces. Inline arrays and call options have an intrinsic
first element and are nonempty. `expr_derives_nonempty` now rules out empty expression yields at arbitrary size.

Layout choices are consumed in preorder. String fragment lists are nonempty,
allow zero-length fragments and must consume the literal bytes exactly. The three
string token families retain distinct tags. Function-type descendants consume
`Choice.attrs` for visibility/mutability ordering. Other expression nodes consume
no choice at their own node. Contract-only `Choice.layoutFirst` cannot be consumed
by an expression derivation. Intrinsic proof fields are proof irrelevant.
Numeric spellings, elementary aliases, comments and whitespace are below tokens.

## Checked proof components

| Module | Actual result and remaining boundary |
|---|---|
| `TokenSplit` | Arbitrary-list delimiter execution, append and untouched-stack-suffix laws, equivalence of empty-stack balance and contextual balance, enclosure, mixed nesting, skipping enclosed markers and whole token-cut uniqueness. Later expression-category modules derive the scanner hypotheses from actual certificates. |
| `Refusals` | Whole-`Syn.prec` refusal for both prefix/postfix readings, both conditional-assignment readings, all postfix-base classes, direct-new alternatives and all left/right association classes, for arbitrary subtrees and parameterized operator values. These constrain trees; they do not reconstruct roots from tokens. |
| `Families` | Unbounded certified negative-prefix family with exact yields and injectivity in depth; arbitrary-depth grouping precedence preservation. Its grouping-yield obligation is now discharged by `Grouping`. |
| `Fragments` | Arbitrary-byte/length-list reconstruction, exact fragment count, independent-layout byte uniqueness, inhabited single and zero-length-leading fragment controls and distinct layouts. |
| `Primary` | Deterministic identifier/boolean/number/unit/elementary yields; identifier, boolean and numeric injectivity; all five literal families, including string tags, arbitrary payload lengths and independent layouts, have same-yield uniqueness. Certified closes other expression roots and recursive types. |
| `Statement` | The unchanged original uniqueness proposition, inhabited in Certified. |
| `Fixtures` | All 29 accepted-root controls, four documented refusals, four additional postfix bases and grouped accepted alternatives, proved with `decide +kernel`. |
| `YieldShape` | All 29 expression roots have exactly one nonempty item on every successful partial-layout execution; optional empty tokens identify absence, and `some e` preserves the expression printer. |
| `YieldBalance` | Compositional balance for items, flattening, separators, type spellings, operators and literal fragments. |
| `AttributeBalance` | Actual successful function-type attribute layouts preserve balance, including arbitrary order lengths. |
| `ExpressionBalance` | The expression/type/parameter/argument/list/option closure yields balanced items; `expr_derives_balanced` derives balance from the original token certificate. Arbitrary closing-token prefixes cannot be expression yields. |
| `DelimiterReconstruction` | Enclosing payload and suffix spans are reconstructed from actual certificates; closing-selector skip facts are derived, not supplied as premises. |
| `Grouping` | Actual group certificates invert to child certificates; group-prefix spans are unique. Arbitrary grouping depth has exact tokens, inhabited certification, token-depth injectivity and tree-depth injectivity for a fixed printable base. |
| `ReverseSplit` | Mirrored step/run/skip reversal at arbitrary stacks, suffix-scanned last-marker cuts, inhabited arbitrary mixed nesting with hidden add markers, and an explicit malformed-word negative control. Later precedence modules derive operator-selector freedom. |
| `SeparatorSplit` | Actual commaSep injectivity on nonempty component vectors, allowing empty words; arbitrary hole-count reconstruction; explicit zero-vector versus single-empty collision. |
| `CommaFreeAlgebra` | Comma-free token/item/attribute algebra; enclosures need only balanced interiors, allowing internal commas. |
| `ExpressionCommaFree` | Exhaustive expression closure yields have no top-level commas; original expression certificates supply every scanner condition in certified component-span reconstruction. This concludes word-vector equality, not child-tree equality. |
| `LowFreeAlgebra` | Joint question/assignment selector includes all 12 assignment operators; loose-root-free token, type-spelling and attribute algebra. |
| `ExpressionLowFree` | Existing recursive precedence plus level ≥ 2 derives loose-marker freedom for all expression roots; type and call-argument outer words are unconditionally free, including arbitrary enclosed descendants. |
| `LowRoot` | Existing certificates determine assignment versus conditional versus higher root class and the assignment operator. Assignment and conditional child spans are now proved in BinarySpans and ConditionalSpans; recursive tree identity is closed by Certified. |
| `LowControls` | Every assignment operator and arbitrary prefix depth inhabit a conditional middle branch with exact yield and whole precedence; the first marker is the outer question, never that middle assignment. |
| `BinaryFreeAlgebra` | Parameterized exact binary-rank markers and token/attribute algebra; prefix helper records its necessary rank-10 limitation. |
| `ExpressionBinaryFree` | Original certificates imply marker freedom above each rank 2–9, 11 and 12, across all constructors and reachable type/call syntax. Its raw-rank-10 limitation is handled by the later operand-sensitive `AddRoot` proof. |
| `BinaryRoot` | Nine left-associative root families derive their last same-rank marker; exponentiation derives its first marker. All scanner conditions follow from original child certificates and bounds. |
| `BinaryRank` | Exhaustive intrinsic root-rank cases distinguish those lower roots from any higher certified root; multiplicative/shift/order/equality operator values reconstruct from equal yields. |
| `BinaryControls` | Every nonzero negative-prefix depth inhabits a certificate that refutes only raw rank-10 marker freedom; grouping shields all those markers. This is not a certified-tree ambiguity. |
| `OperandMode` | A delimiter stack and completion bit have arbitrary-context execution laws; outer enclosures finish an operand and interior tokens do not affect the surrounding bit. |
| `OperandModeAlgebra` | Literal fragment nonemptiness, atom/type spelling and actual attribute layouts compose completion properties from arbitrary initial bits. |
| `ExpressionMode` | Every successful expression/type/call-argument yield finishes an operand from either initial bit, without a precedence premise. This is a shape property, not grammar recognition. |
| `AddScan` | Operand-sensitive additive skip and last-marker machines; arbitrary earlier prefix hits are allowed, and marker/cut uniqueness follows at arbitrary lengths. |
| `AddFreeAlgebra` | Explicit unfinished, finished, reset and prefix entry/exit properties compose; literals and enclosures finish from either bit, while attributes preserve a finished bit. |
| `ExpressionAddFree` | Original high-expression certificates derive additive freedom starting unfinished; all constructors and arbitrary type/argument/layout descendants are covered. |
| `AddRoot` | Additive root/operator reconstruction and higher-root disjointness close the rank-10 marker gap. Certified ordinary binary roots at all ranks 2–12 have equal levels when their yields agree. |
| `AddControls` | Every additive operator and arbitrary right-prefix depth have an inhabited exact-yield certificate and correct outer marker. The same unary prefix deliberately fails a skip begun finished. |
| `YieldSplit` | Actual successful StateT/Option executions invert into child successes, with arbitrary independent layout states. |
| `BinarySpans` | All eleven ordinary binary families plus assignment derive equal child token spans and actual state executions from parent certificates/yields; enum operators reconstruct. |
| `SpanControls` | Arbitrary mixed additive/prefix depths have partial-state operator/depth uniqueness and certified family-tree uniqueness. |
| `ConditionalBalance` | Delimiter/count-only machine and arbitrary successful-prefix/failing-colon cut reconstruction. |
| `ConditionalAlgebra` | Neutral tokens, literal fragments, actual attribute layouts and balanced enclosures preserve paired conditional punctuation. |
| `ExpressionConditional` | Every original expression/type/param/callargs yield pairs top-level question/colon punctuation; bare namedArg colons remain shielded in actual enclosures. |
| `ConditionalSpans` | Original certificates derive all three conditional child spans and layout states; optional index/slice payloads separate and slice colon cuts reconstruct. |
| `ConditionalControls` | Arbitrary nested true branches have inhabited certificates and correct outer-colon cuts; raw selectors choose an inner colon, and all bracket kinds shield arbitrary internal colons. |
| `UnaryFreeAlgebra` | Token/attribute algebra for all six prefix and both suffix markers; keyword delete is covered. |
| `ExpressionUnaryFree` | Original certified roots of level>=15, types and callargs exclude outer unary markers; enclosed unary descendants remain unrestricted. |
| `UnaryRoot` | Actual prefix/suffix child words and operators reconstruct; prefix marker0, suffix markerpositive and higher absence distinguish roots. |
| `UnaryControls` | All prefix/grouped-suffix operators have arbitrary-depth inhabited exact yields and markers, retaining ungrouped nesting refusals. |
| `LayoutBoundary` | Existing printer extension/trimming composition and complete expression-category closure; actual partial expression yields obtain fully consumed Derives witnesses. |
| `RootLevels` | Original certified root levels agree whenever either is<=14, also for independent partial layouts. AllRootLevels closes postfix15 versus primary16 from certified primary spines. |
| `LastEnclosure` | Arbitrary trailing balanced enclosures reconstruct their payload and preceding word using the existing mirrored first-cut theorem. |
| `PostfixYieldSplit` | Actual index/slice/call/options/namedArg executions invert into existing child states; callArgs gives its genuine balanced parentheses payload. |
| `PostfixSpans` | Actual index/slice/call/options children reconstruct; index and slice roots are disjoint; options preserve the full tail word vector. |
| `MemberSpans` | Member/namedArg names and child words reconstruct, including arbitrary strings and the special member address token. |
| `StartAlgebra` | Balanced first-token invariant forbids only an initial opening brace, allowing arbitrary later braces. |
| `ExpressionStart` | All29expression/type/param/argument closure derives that first-token invariant; callOptions uses its actual nonempty base. |
| `ArgumentWords` | Actual expr/namedArg list components are nonempty; full comma-vector uniqueness permits empty lists and handles the generic empty-word collision. |
| `ArgumentSpans` | Positional/named arguments are disjoint and reconstruct their actual component vectors, including empty lists. |
| `PostfixControls` | Arbitrary mixedall5postfix tower has exact inhabited certificates and family identity; arbitrary optional holes refute false nonemptiness generalization. |
| `PostfixRootKind` | Actual level15 words reconstruct exactly all five postfix constructor families; scalar tags dispatch through existing Source.Ctor. |
| `TypePrefixAlgebra` | Arbitrary maximal token-run and balanced square-spine cuts with concrete finite follower conditions. |
| `AttributeTokens` | Actual arbitrary function-type attribute orders produce only the existing visibility/mutability keyword run. |
| `TypeYieldSplit` | Actual mapping/array/function type executions recover fields and layout states; fn attributes/params/returns invariants are derived. |
| `TypeSpine` | Existing intrinsic non-array type node plus balanced dimension-token words reconstruct any successful type yield. |
| `TypeAtomStart` | Existing non-array type families distinguish their token heads using Source.Ctor dispatch. |
| `ElementaryPathPrefix` | Address/payable and arbitrary path words reconstruct maximal prefixes at concrete followers. |
| `FnTypePrefix` | Parameter, attribute and optional returns word cuts reconstruct at arbitrary layouts; whole function prefix follows. |
| `TypeAtomPrefix` | All four existing non-array type families have actual maximal word-prefix cuts. |
| `TypePrefix` | Arbitrary type words reconstruct maximal prefixes from actual atom/spine executions and concrete followers. |
| `TypePrefixControls` | Arbitrary array/new witnesses; original direct-new-index refusal rejects a kernel-proved raw collision; follower countercontrols. |
| `PostfixFollowers` | Concrete first-postfix token followers retain the original isNew guard; new followers derive TypeBoundary internally. |
| `PrimarySpine` | All certified high expressions expose an existing level16primary, actual independent layout execution and exact postfix word; empty postfix words imply the original node is primary. |
| `PrimaryYieldSplit` | All new/payable/meta/tuple/inline actual printer parts and balanced payloads recover existing child states. |
| `LiteralPrefix` | Arbitrary same-kind literal token runs reconstruct maximal prefixes; unit denomination separates ordinary numeric literals under derived postfix followers. |
| `PrimaryPrefixParts` | Scalar, keyword and balanced-enclosure primary prefix cuts; new types use the internally derived follower boundary. |
| `PrimaryStart` | Existing unindexed Ctor and actual first-token classes distinguish primary families; literal/unit share a header class until the proved follower-sensitive cut. |
| `PrimaryPrefix` | Exhaustive9primary families reconstruct actual word prefixes, including literal/unit crosscase disjointness; recursive tree identity is closed by Certified. |
| `AllRootLevels` | All certified root levels0through16 reconstruct at independent actual layouts; primary spine and prefix cut derive15versus16 separation. |
| `RootLevelControls` | Arbitrary postfix towers and new-array depths reconstruct levels against any certified competitor; direct-new square/period first followers refuted, call/options heads permitted without arbitrary-tail validity. |
| `RecursiveProperty` | Word/vector structural induction predicates on existing Syn; list vectors preserve holes. No public instance asserted. |
| `ContainerIdentity` | Generic nil/cons vector identity and none/some.expr word identity using actual child IHs/nonempty expression words. |
| `ArgumentIdentity` | Actual namedArg, positional and named argument identity steps from recovered names/vectors and structural children. |
| `ContainerControls` | Arbitrary optional-hole vectors determine any certified competitor; raw flattening collision remains list-only. |
| `ParameterIdentity` | Parameter type boundaries follow from actual optional location/name fields; exact fields and child IH recover identity. |
| `ParameterWords` | Actual type/parameter words and arbitrary parameter-list components are nonempty via existing completion invariant. |
| `TypeArrayIdentity` | Actual array/non-array type disjointness, array child-word cuts and structural array identity step. |
| `AttributeOrderIdentity` | Arbitrary successful empty/one/two-field layout orders are exhaustive, with no assumed order length/canonical order. |
| `AttributeFieldIdentity` | Disjoint token filters recover existing optional visibility/mutability fields under independent successful layouts. |
| `FunctionTypeIdentity` | Actual function parameters/returns vectors and attribute fields reconstruct; structural listchild IHs give same-constructor identity. |
| `TypeLeafIdentity` | Actual atom family classification, arbitrary elementary/path intrinsic leaf identity and function WordUnique against every type competitor. |
| `MappingKeyIdentity` | Existing unindexed MapKey word prefix, key/name/arrow reconstruction and arbitrary elementary/path key identity. |
| `MappingIdentity` | Actual key/value/name fields recover mapping identity using only structural valuechild IH, against all type competitors. |
| `TypeIdentityControls` | Arbitrary array family WordUnique against ANY certified competitor, plus empty function type child-premise closure. |
| `BinaryIdentity` | All12ordinarybinary/assignment expression identity steps, arbitrary operators/trees, actual original root and child cuts. |
| `BoundaryIdentity` | All6prefix/all2suffix operator and conditional identity steps from actual root levels/children. |
| `PostfixIdentity` | All5postfix identity steps; optional/list child types and full options-tail vectors preserved. |
| `PrimaryLeafIdentity` | Identifier, elementary, all5literal families and units compare against every certified root; independent fragments and original follower separation. |
| `PrimaryChildIdentity` | New/meta/payable/tuple/inline identity steps, arbitrary component lengths and empty tuple holes retained. |
| `Certified` | Exhaustive intrinsic mutual induction and exact original public CertifiedYieldUnique theorem, no added premise or parser assumption. |
| `Accepted` | Original parseCat_sound supplies actual lexical/yield/precedence facts; accepted trees equal any certified competitor, including cross-producer same-source equality. |
| `CertifiedControls` | Arbitrary arraydepth/paramcount/optionalreturns/attributeorder wrapped function expressions and tupleholes are inhabited; original directfunctionmeta refusal retained. |
| `AxiomPins` | Exact `#guard_msgs` axiom pins for all 1241 source declarations; actual sets use only `propext`, `Classical.choice` and `Quot.sound`, or no axioms. |

`firstTop_cut_unique` has token-machine `skip` hypotheses. They are NOT assumed in
the original expression target. Delimiter/grouping corollaries now derive their
skip facts from certificates, while Certified closes recursive tree
reconstruction. Likewise
`mkPayload` in a fragment helper is a token-constructor left-inverse condition;
all three concrete string instantiations discharge it by `rfl`.

The preserved refusal examples are `-a++`, `a ? b : c = d`, `a++.f` and `a++ ++`.
Additional postfix index/slice/options/call bases are refused. `-(a++)`,
`a ? b : (c = d)` and `(a++).f` retain their accepted verdicts. No expected
verdict or read-only producer input changed.

## External observations and proof boundary

`compiler-controls.mjs` checks the exact solc 0.8.38 pin already listed in the
repository: SHA-256 `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The setup cache holds the fetched official soljson; no compiler binary is committed.
All 130 parsing observations passed: representative operators across 11 binary
levels, both orders of every level pair, association, conditional/assignment
association, and the documented disagreements/grouping. Every source and its hash,
expected shape, actual shape and parser errors are saved. `stopAfter: parsing`
means these are external parser observations, not type checking, semantic compiler
correctness, every operator spelling, every conditional/assignment cross-boundary,
or kernel uniqueness proofs. Kernel uniqueness and all intrinsic operator/association classes are proved
separately. Semantic compiler correctness and type-checking are not claimed by
these external parsing observations.

## Runtime and measured validation

H26 authorizes equivalent Docker enforcement without changing any resource
requirement. The exact approved image digest is
`ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`.
`bounded.py` acquires the repository writer lock, checks the parent's 4 GiB reserve,
runs one owned container with 12 GiB hard memory and zero swap, and stops that
container on parent pressure. Inside, `inside.py` asserts `memory.max=12884901888`,
`memory.swap.max=0` and `LEAN_NUM_THREADS=1` after activation. A scoped Lake config
adds explicit `-j1`; dependency compilation is topological and serial. Lean MCP
uses at most three files. No heartbeat, timeout or trust budget was raised.

Actual versions: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
`checkpoint-proof-complete-final.log` records the passing permitted KeySort result BEFORE
`RUNTIME_GATE_PASS`: 377 taclets parsed, 131 read-bearing, 131 matched. Runtime
success is not full assignment acceptance. The same command passed MCP diagnostics
and the per-file kernel axiom-pin gate at the exact module hashes recorded in
`checkpoint-proof-complete-final.inside.json`. This command took 49.745508seconds, childRSS274040KiB,
exactcgrouppeak844828672bytes, minimumparentheadroom9594183680bytes,
with zeroOOM/resource stop. These figures describe that command,
not all earlier builds. Every other run has separate command/exit/time/RSS records;
failed attempts and unavailable-tool probes remain retained. Sampled cgroup usage
is labeled separately from exact memory.peak and per-child RSS.

`check-sol-expression-uniqueness.py --inventory` validates all source/base pins,
constructors, modules, declarations, proposed rows, fixture references and axiom
guard inventory. `--checkpoint` additionally requires current-source kernel
signature/axiom evidence, runtime bounds, KeySort and compiler observations.
Default full acceptance remains exit1 while frozen integration/global gates are open. Changing
ledger statuses alone cannot turn the partial checkpoint into full acceptance.
The actual `./run-lean.sh` attempt exited 1 before building, at the frozen-root
check: exactly these one hundred modules lack central root imports. The orphan gate
reported the same one hundred. Source trust passed (3772 sources, zero findings), and
layers passed (559 core modules, none reaching elaboration or checked adapters).
The global axiom-source gate reported zero errors but exited 1 for 1241 unrecorded
new standard pins. Proposed module/map rows and the exact axiom registration
reference are in the manifest for coordinator integration; the worker did not
edit frozen roots or trust inventory. These failed global gates are not counted
as passes. Full library/TestSuite confirmation has not run past registration.
They remain distinct from this passing partial proof checkpoint.

## Reviews and next work

Separate read-only finder and skeptic reviews used no Lean server. No certified
ambiguity has been found. Review findings were fixed and rechecked; no remaining
findings are reported for the current partial checkpoint. They caught stale inventory-only
documentation/manifest/checker claims (F2/F3); these were replaced with the actual
proof state and current-source evidence checks. Final review also found missing
fixture-statement linkage (F4/S3) and unchecked signature-command success (S2).
The checker now binds each constructor fixture to its exact theorem/input/root
signature, requires successful bounded signature execution and its kernel gate,
and has explicit corruption controls for these findings. The earlier missing pin-set check
(F1/S1) remains fixed and has deletion/corruption controls. Final checkpoint review
results are saved under the evidence directory; future proof checkpoints still
require their own reviews.

All expression/category delimiter, comma, precedence-marker and operand-state
invariants, actual root/child cuts and recursive identities are proved.
recursive_yield_property in the Certified module exhaustively discharges all child hypotheses;
certifiedYieldUnique inhabits the exact original target, and Accepted derives
accepted-tree equality. Final source/signature/axiom and complete logical-declaration evidence passes.
Bounded streamed proof acceptance/corruption controls PASS; global registration
failures are confirmed. Independent finder/skeptic final metadata reviews PASS with no remaining findings. Frozen registration-dependent global gates and the full task
handoff remain open. No push, merge, PR, producer edit or scope expansion.


The complete kernel environment inventory has2323unique owned logical declarations
(1241explicit source declarations plus1082generated logical declarations).
All2447module metadata emissions were actually audited;124re-emissions have
identical types/axioms and are canonicalized by Lean's actual declaration-owner
map. Every defining-owner emission and explicit source name/owner is checked.
The387extra compiler metadata names overlap34audited logical names; the353
remaining compiler-only names have no separate kernel declaration/type claim.
Both verifier tools are confined to owned tests and import Lean there only;
actual command-start tool hashes, current library snapshots, full type Exprs,
actual standard axiom sets, gates and resources bind the inventory. Corruption
controls reject missing/duplicate emissions, poisoned ownership, changed target,
circular public premise, stale tools, omitted boundaries/operators and hidden
overlap. This tooling is evidence collection, not an extra mathematical premise.

Two eager metadata validation attempts breached H1reserve and were stopped by
the monitor (outerexit137/resource_stoptrue; wrapperexit125); they are failures,
not passing proof gates. Full type trace size497393242bytes caused eager copying
pressure. Lossless compression preserves all bytes in9983027bytes, with raw and
compressed SHA256s; compact indexes retain type hashes/lengths and actual axioms.
The reader streams the full trace, compares repeated FULL type strings and hashes
every raw byte. Each acceptance rehashes compressed bytes; only verified compact
rows may be memoized under raw/compressed hashes and exact expected multiplicities.
Current library and actually executed verifier snapshots are checked before cache
use. This may change validation speed; history had no speed-motivated implementation
to undo. Formal proofs/budgets are unchanged. Recovery proof acceptance passes
at39628KiB RSS/reserve10347106304bytes; allcorruptioncontrols at50040KiB RSS/
reserve10334318592bytes. Complete failure/resource/preservation evidence is in
`tests/sol-expression-uniqueness/evidence/memory-recovery.json`.

## Balance and grouping checkpoint

The continuation adds six proof modules and 80 source declarations, bringing the
that checkpoint totals to 14 modules and 218 declarations. Both independent read-only
reviews accepted the new components, without Lean-server use. Their precision
limits are retained: optional results reconstruct absence/presence, not complete
lists; grouping tree-depth injectivity has a fixed base with an actual yield;
there is no theorem equating arbitrary grouped child trees from equal yields.
The global `CertifiedYieldUnique` obligation and parseCat corollary are unchanged
and open. `refresh-audit.py` regenerates only owned metadata and pins from the
actual successful kernel signature report. `audit-runs.json` selects the current
bounded evidence; the checker requires matching current module hashes and passing
signature/axiom gates, and rejects stale run references. Central registry files
remain untouched.

The balance-checkpoint metadata review caught a signature-snapshot mismatch:
pre-refresh snapshots include the previous generated `AxiomPins.lean`. The checker
now excludes that exact path from both sides of the signature-source comparison;
the current axiom-pin gate still checks its refreshed hash exactly. Every other
extra/missing signature path is rejected. Controls now assert a successful
positive inventory/checkpoint baseline before and after corruption tests, so a
broken baseline cannot make the negative tests pass vacuously. The failed first
balance acceptance command is retained as evidence.

Final finder and skeptic verdicts for this checkpoint are recorded in
`tests/sol-expression-uniqueness/evidence/reviews-balance.json`. Both independently
accepted the corrected audit; neither used Lean or edited sources. The corrected
positive baseline, corruption controls and checkpoint acceptance pass. Default
full acceptance remains exit 1 with the original proof obligations open.

## Separator checkpoint

Four further modules add 85 declarations, bringing that checkpoint inventory to 18
modules and 303 declarations. `expr_derives_commaFree` derives top-level comma
freedom directly from the existing fully consumed certificate, across all 29
constructors and recursive type/argument syntax. Component token spans therefore
reconstruct without caller-supplied split or scanner assumptions. Tree equality,
list-to-layout inversion and operator-root selectors remain separate open work.

`lastTop` means depth zero in the mirrored suffix scan. On malformed words it
need not agree with forward top-level status; the unmatched-parenthesis negative
control records this exactly. No general forward/reverse consistency theorem is
claimed. The inhabited hidden-add family quantifies arbitrary nesting, payload
marker count and prefix length. Nonempty comma vectors permit arbitrary empty
holes; the empty vector and one empty word collision prevents an invalid stronger
statement. These helpers do not weaken the original uniqueness target.

Separate finder/skeptic reviews accepted this partial proof work without Lean
server or edits. The known `congrArg₂` name error was replaced with an independently
tested core congruence proof and diagnostics passed. Current verdicts are in
`evidence/reviews-separators.json`. The first full-gate command failed at missing
Node PATH (exit 127); its corrected invocation reached the same frozen-registration
check (exit 1), now for 18 modules. All failed checks remain in evidence. The full
public theorem, accepted-tree corollary and full final acceptance remain open.

## Loose-root checkpoint

Four modules add 71 declarations, bringing that checkpoint total to 22 modules and
374 declarations. The original `Syn.prec` certificate and root level, rather than
new producer conditions, yield the loose-marker invariant. Taking the first
joint question/assignment marker handles arbitrary assignments in conditional
middle branches. `certified_firstLow_none_iff` characterizes the higher-root class
without a root-class premise. Assignment/conditional disjointness and assignment
operator reconstruction are proved at arbitrary tree sizes. Full operand spans,
conditional colon reconstruction, remaining operator levels and global tree
uniqueness are still open. The all-operator middle-assignment family proves
actual inhabited certificates at every prefix depth; documented false-branch
refusals remain unchanged.

Failed constructor-simplification attempts hit the unchanged 200000-heartbeat
limit. Closed per-constructor arithmetic contradictions and compositional
precedence joins discharge the exact same statements; no budget or statement
changed. The high-expression invariant took about 130 seconds in MCP and its
serial kernel build passed. A duplicate unused simp argument in `ReverseSplit`
was removed. No owned-module linter warning remains in the successful signature
build; frozen upstream `Source/Ctor` warnings remain untouched.

Actual kernel axiom sets now include `Classical.choice` as well as `propext` and
`Quot.sound`, all within the standard whitelist. Lean wrapped ten three-axiom
messages across lines, exposing a single-line report-reader assumption. The
parser now reads complete lists and rejects duplicate names. Guard comments
preserve exact raw kernel messages; no printing/whitespace setting was relaxed.
The first parser failure and the first guard-format failure are retained under
separate evidence names. Both static inventory and checkpoint acceptance compare
the entire reported axiom dictionary to the pins; the checkpoint additionally
binds every current proof source hash and successful kernel guard run. Wrapped
positive reports and duplicate/forbidden/unterminated negative controls pass.
Separate finder/skeptic reviews accepted the source and audit changes without
Lean-server use. Verdicts are in `evidence/reviews-lowroots.json`.

## Binary marker and root-rank checkpoint

Five modules add 87 declarations, bringing that checkpoint total to 27 modules and
461 declarations. The parameterized helper covers exact binary ranks 2–9, 11
and 12. Every child certificate and bound comes from original `Syn.prec`; no
scanner cut is assumed by the public certified-root results. Nine left-associative
families derive the last same-rank marker, while exponentiation derives the first.
Lower/higher root disjointness holds for arbitrary intrinsic subtrees, and every
multiplicative, shift, relational and equality operator value reconstructs from
shared yields. These are marker/rank/operator results, not complete child-tree
or operand-span equality.

At that checkpoint the rank-ten operand-state proof remained open. The arbitrary `negFamily (n+1)`
control is inhabited and certified, but begins with the same raw subtraction token
as a binary subtraction. Thus the intermediate raw-selector freedom lemma cannot
cover rank ten. Grouping shields all such prefix tokens. No original premise,
refusal or target was narrowed; there is no certified-tree ambiguity here. The
operand-sensitive scanner and certificate proof below now discharge that marker
obligation; complete child spans and the original tree theorem remain open.

Direct natural-number bound composition keeps the new expression invariant check
to about 11.5 seconds including serial setup; no heartbeat or timeout changed.
All five new modules pass diagnostics and the actual kernel signature/pin gates.
Their exact axiom sets are recorded; the overall lane standard union remains
`propext`, `Classical.choice`, `Quot.sound`. Independent finder and skeptic
accepted the source without Lean-server use. Verdicts are recorded in
`evidence/reviews-binary.json`. Full operand/conditional-colon spans, high-root
reconstruction, recursive type/argument/tree uniqueness and the parseCat corollary
remain open, as do full registration-dependent global gates.

## Operand-sensitive additive checkpoint

Eight modules add 146 declarations, bringing that checkpoint inventory to 35 modules
and 607 declarations. The stack/bit machine stores no syntax tree. Successful
intrinsic expression, type and call-argument words finish an operand from either
initial bit; fragment vectors must be nonempty according to their actual layout,
and function-type attribute layouts preserve a finished state. This completion
property does not assert grammar recognition or marker freedom from either bit.

Additive freedom for a higher expression starts with `finished=false`, derived
from its original `Syn.prec` and level > 10. A leading unary subtraction then
remains a prefix; after an actual completed left operand, subtraction is selected
as binary. The root proof derives left completion and right freedom internally.
It allows arbitrarily many earlier additive hits on the left. Types and bracketed
arguments finish safely from either bit. The explicit finished-entry prefix
countercontrol prevents silently strengthening that intermediate invariant.

`binary_higher_root_disjoint` now covers every ordinary binary rank 2–12, and
`certified_binary_root_levels_equal` proves equal root levels for arbitrary
certified binary trees with the same yield. Additive operator values reconstruct
too. The mixed-add/prefix family certifies both operators at arbitrary depth,
with exact tokens and outer marker position. Full operand/conditional-colon spans,
higher-root reconstruction, recursive type/list/argument/tree uniqueness and the
public theorem remain open. No original premise, interface, refusal, exclusion
or proof budget changed; all earlier raw-selector controls remain true.

All eight modules pass diagnostics and exact kernel signature/axiom gates. The
complete current-source checkpoint, corruption controls, source pins and KeySort
pass under unchanged hard bounds. Independent read-only finder/skeptic source
reviews accepted the state invariants, all-constructor coverage and root/control
proofs, using no Lean server. Verdicts are in `evidence/reviews-additive.json`.
Failed first enclosure normalizations and one file-assembly/missing-file attempt
remain separate evidence. No incomplete Lean proof is counted as passing.


## Actual binary child-span checkpoint

Three modules add 34 declarations, giving 38 modules and 641 declarations.
`YieldSplit` inverts successful existing printer binds and pure results. It
recovers each child execution and its intermediate layout state from the actual
parent success, even with an unconsumed layout suffix. `BinarySpans` uses those
executions and the original recursive precedence certificate to derive the
necessary marker freedom internally. Nine left-associative families use the
last same-rank cut, additive roots use operand-sensitive last cuts, and
exponentiation/assignment use first cuts. All twelve families conclude equal
left/right child words; enum families also recover the operator. Independent
layouts are not equated. No desired root split or uniqueness premise is assumed.

The arbitrary mixed-add/prefix family reconstructs both operator and depth from
shared partial successes, and hence proves equality within that inhabited family.
This does not prove general child-tree identity. Conditional colon matching,
higher-root/postfix/primary reconstruction, recursive type/list/argument/tree
uniqueness, the public theorem and accepted-tree corollary remain open. The
original target, source interfaces, exclusions, refusals and budgets are unchanged.

All three modules pass per-file diagnostics and serial kernel signature/axiom
gates. Exact actual standard-only axiom sets cover all 641 declarations. Separate
finder and skeptic source reviews accepted the partial checkpoint without
defects or Lean-server use; records are in `evidence/reviews-spans.json`. Failed
first bind inversion and missing direct import diagnostics remain retained.


## Conditional colon and actual child-span checkpoint

Five modules add 84 declarations, giving 43 modules and 725 declarations. A
delimiter stack plus natural counter pairs question marks and colons outside
brackets; balanced enclosures shield arbitrary internal colons. The generic
first-failure machine also detects malformed raw delimiters, explicitly distinct
from the certificate-derived outer-colon result. Successful original expression,
type, parameter and call-argument yields preserve the counter for every initial
depth, by exhaustive intrinsic induction over all 29 expression constructors.
Bare named arguments necessarily carry an unpaired colon and are omitted only
from that intermediate invariant; their actual surrounding braces are handled
using raw balance. No original expression/certificate/target is excluded.

The actual conditional printer inversion derives all child executions. Existing
condition precedence supplies low-marker freedom and reconstructs the question
cut; true-branch conditional balance reconstructs the outer colon. All three
child words follow, for independently chosen partial layout states. Optional
expression payloads also distinguish index from slice, including absent
endpoints, and uniquely split the slice colon. Complete postfix bases/enclosures
and child-tree identities remain open. Arbitrarily nested true branches have
exact inhabited certificates. The paired scanner selects the outer colon after
4*n+1 tokens; a raw colon scanner selects an earlier colon at 2*n+1 for n>0.
All three bracket kinds shield arbitrary runs of internal colons.

Diagnostics and serial kernel signature/axiom gates pass with exact standard
sets for all 725 declarations. Independent read-only finder/skeptic source
reviews accepted the partial checkpoint without defects or Lean-server use;
records are in `evidence/reviews-conditional.json`. Earlier failed nil-map
normalizations, reserved-name syntax and redundant-tactic attempts are retained.
High-root reconstruction, recursive type/list/argument/tree uniqueness, the
public theorem and parseCat corollary remain open.

The coordinator-published master was fetched and verified at
`b419c3cf4f642ae519b66bebc26cdf2f7cf93574`, descending from the assigned base.
All six assignment read-only master inputs are unchanged there; the integrated
`Fragments.lean` matches this branch. No merge/rebase/reset was performed and
the assigned branch still descends from its exact pinned base. Remaining work
is not claimed integrated. Fetch evidence is `evidence/published-master-fetch.log`.


## Unary roots and layout-boundary checkpoint

Six modules add 89 declarations, giving 49 modules and 814 declarations. Every
outer prefix/suffix token, including keyword delete, is absent from certified
roots of level at least15. The proof covers all29 expression constructors and
type/call-argument closure using actual layouts and enclosures. Prefix markers
select position zero; suffix markers select a positive position because the
original certificate supplies a nonempty higher-root operand. Actual unary
printer inversion reconstructs operator and child word/execution, independently
of the two layouts. Every prefix operator has arbitrary direct nesting; every
suffix operator has arbitrary grouped nesting and exact inhabited certificates.
The existing ungrouped suffix refusal remains unchanged.

Generic printer extension/trimming laws cover pure/lift/pop/bind and all three
existing Choice constructors. The complete expression-category yield closure
satisfies them. Thus every partial expression success has a fresh fully consumed
Derives witness for its flattened word, with no assumed child printability or
layout equality. This supplies the missing bridge from recovered child-state
executions to the original existential certificate interface. Statement, function
and unit uniqueness are not claimed or added to this closure.

Combining the original loose/binary results with unary separation proves equal
certified root levels whenever either level is at most14; the same result holds
for independently chosen partial executions. Postfix15 versus primary16, their
complete decompositions and recursive type/list/argument/child-tree identities
remain open. The public theorem and parseCat accepted-tree corollary stay open.
No original target, premise, exclusion, refusal, producer interface or budget
changed. One broad control simplification exhausted the fixed200000 heartbeats;
using a closed root fact fixed it at the same budget. Failed attempts are kept.
A deprecated length lemma in the first successful signature build was replaced
by its identical current API; final diagnostics/kernel logs have no owned warning.

Independent read-only finder/skeptic source reviews accepted this partial work
without defects or Lean-server use. Records are in `evidence/reviews-unary.json`.
Exact standard-only kernel signatures/axiom pins cover all814 declarations.
The local49 registration count describes the original pinned checkout and
includes Fragments already integrated on published master; the manifest records
that integration separately so the coordinator can deduplicate registration.
No remaining work is claimed integrated and no rebase/reset/merge occurred.


## Postfix and argument child-word checkpoint

Nine modules add103 declarations, giving58modules and917 declarations. Trailing
balanced enclosures reconstruct arbitrary preceding words and balanced payloads
by mirroring the existing first-cut theorem. Actual existing printer inversions
supply child executions/states. Index, slice, member, options and call each
recover their child words; slices recover both optional endpoints through the
conditional-colon result. Index and slice roots are disjoint from actual yields,
even before precedence checking. Member/namedArg names reconstruct at every
string, including the special member address token. Options reconstruct their
first argument word and entire tail word vector, retaining individual words.

The complete29expression/type/parameter/argument closure cannot begin with an
opening brace. This is strictly a first-token fact: later and enclosed braces
remain allowed; callOptions uses its nonempty actual base. Actual expr/namedArg
list components are nonempty while empty lists remain allowed. Derived comma
freedom/nonemptiness reconstructs positional/named argument vectors without a
split premise, and the two argument constructors are disjoint. Optional tuple
holes are not subjected to that nonemptiness property: an arbitrary-hole family
prints empty components and refutes any such extension.

An arbitrary-depth mixed postfix tower includes all five postfix constructors
per step, has an inhabited original certificate and exact14*n+1 token length,
and has same-yield family-tree uniqueness. This is an intrinsic syntax control,
not an additional external compiler or semantic claim. All130 previous exactpin
external parsing observations remain separate. General postfix cross-root
classification, postfix15 versus primary16, primary/new-type greedy boundaries
and recursive type/list/argument/child-tree identities remain open, as do the
public theorem and parseCat accepted-tree corollary. No original premise, scope,
exclusion, refusal, source interface or budget changed.

All nine modules pass diagnostics and exact actual kernel signature/axiom gates.
The first broad control simplification exhausted the unchanged200000heartbeats;
explicit original-node certificate assembly fixed it at the same budget.
Initial indexed-induction, token normalization and overloaded-negation attempts
remain retained. One unused mirror simp argument was removed; final kernel
signature logs have no owned warning. Independent read-only finder/skeptic source
reviews accepted this partial checkpoint without defects or Lean-server use;
records are in `evidence/reviews-postfix.json`. That checkpoint source acceptance and
917 exact standard-only axiom pins pass. Fresh published-master verification
hashes all8pinnedinputs and the integrated Fragments against this checkout;
all match (`evidence/published-master-verification.json`).


## Postfix kind and type-prefix checkpoint

Eleven modules add90 declarations, giving69modules and1007 declarations. Actual
postfix words now identify all five existing constructor families: trailing
tokens separate call/options/member/square forms, and the conditional-colon
proof separates index/slice. No precedence assumption is needed once both
roots have level15. The15versus16 distinction remains open.

Actual type execution decomposes into an existing non-array Syn.typeName node
and balanced dimension-token words; this is not a second AST. All elementary
values including address/payable, arbitrary identifier paths, mapping enclosure
and function parameter/attribute/returns words have maximal prefix cuts. Actual
function layouts supply the attribute keyword run and balanced payloads; no
canonical attribute order is assumed. Arbitrary array spines then reconstruct
full type prefixes. TypeAtomBoundary/TypeBoundary are explicit finite TOKEN
follower conditions of these intermediate lemmas. They are not producer or
global uniqueness premises. Deriving them inside the original certified
primary/postfix context is still OPEN, as are recursive type/tree identity and
the original public theorem/corollary. No original target was narrowed.

The arbitrary array/new families are inhabited with exact tokens. A kernel proof
shows the raw new-array/direct-new-index token collision, while the ORIGINAL
certificate rejects the direct-new-index tree. This is not a certified ambiguity
and does not change any expected refusal. Square/payable/view follower controls
show why maximal helper cuts need their concrete boundaries. These are intrinsic
controls, separate from the unchanged130external parsing observations.

The skeptic identified direct indexed Syn matches in three scalar classifiers
under [Gate G0](../intrinsic.md#gate-g0-kernel-evaluated-code). They were replaced
with dispatch on the existing unindexed Source.Ctor result, with explicit imports.
Source/Ctor itself remains frozen and retains its inherited matcher/cost; no
match-free dependency closure, new exemption or speed improvement is claimed.
The source history contained only S00 creation/review commits (2aec5be9 and
cccc1086), so no speed-motivated implementation was undone. The user was warned
before the potential reduction-cost change. Both read-only reviewers accepted
the corrected route; final diagnostics/kernel gates cover the final definitions.
Old/new command timings are retained but cache differences prevent a speed claim.

All eleven modules pass final diagnostics and actual kernel signature/axiom
gates, with1007exact standard-only pins and no owned warning. Failed dependent
match/type-annotation/normalization and edit-script attempts remain retained;
unused simp arguments were removed. Independent finder/skeptic source verdicts
and the G0 resolution are in `evidence/reviews-typeprefix.json`. Full primary
root reconstruction and recursive expression/type/list/argument uniqueness,
parseCat corollary and registration-dependent full gates remain open.


## Primary prefixes and complete root levels checkpoint

Nine modules add 57 declarations, totaling78 modules/1064 declarations.
Actual certified high expressions expose an existing level16primary node and
its exact executed token word, followed by actual postfix tokens. Original
not-new checks derive first-follower restrictions internally; calls/options
remain permitted for new bases. No second AST, desired span, desired uniqueness
or new producer/target premise is introduced. Existing type boundary helpers are
now discharged inside the original certified new-primary context.

Every one of the9primary families has a maximal prefix cut from actual
independent layouts. Literal fragments form arbitrary same-kind maximal runs;
unit and ordinary numeric primaries are separated by the denomination token and
actual postfix followers. Existing unindexed Ctor classifies primary roots; its
inherited Source matcher/cost remains unchanged. Keyword/enclosure helpers and
first-token classes give exhaustive primary-prefix reconstruction. These cuts
with the certified primary spine close15versus16. All certified expression root
LEVELS0through16 now agree for equal yields; this does not establish recursive
tree identity. CertifiedYieldUnique and the parseCat corollary remain OPEN.

Arbitrary postfix towers and new-array depths reconstruct levels against any
certified competitor. Direct-new square/member first followers are refuted;
call/options followers remain permitted at every depth. These intrinsic controls
are separate from the unchanged130external parsing-only observations.

A general levelbound simplification hit the unchanged200000heartbeat budget;
29explicit closed constructor bounds fixed it without raising budgets. Earlier
missing precedence import and control enclosure-versus-head mismatches remain
retained in failed logs. Both independent source reviewers found the latter;
direct token-follower constructors fix the proofs with statements unchanged.
Final signatures and all1064exact standard-only axiom guards pass kernel and
MCP checks without owned warnings. Actual Lean4.24.0/Lake5.0.0-src+797c613 and
KeySort377/131 pass before RUNTIME_GATE_PASS under approved hard limits.
Acceptance, metadata reviews and global gates are being refreshed. The
call/options controls permit first-token followers only; they do not assert
that an arbitrary tail is a valid call/options payload. No complete assignment
claim is made here.


### Primary checkpoint handoff

Final independent finder and skeptic source/metadata verdicts accept this partial
checkpoint after the follower-proof and stale-current-summary fixes. Their
records are `tests/sol-expression-uniqueness/evidence/reviews-primary.json`.
Final bounded commands are signature-audit-primary-final (kernel types/axioms),
checkpoint-proof-primary-final (versions, KeySort, MCP and exact pin guards),
primary-acceptance, primary-controls and primary-doc-paths-final: all PASS.
The primary-full-acceptance command exits1 ACCEPTANCE_OPEN. Global run-lean and
orphans exit1 at78frozen registrations before full library/TestSuite build;
trust3750zero and layers559zero pass, central axiom-source has zero errors but
1064unrecorded pins and exits1. These outcomes are preserved, not waived.

The checkpoint commit contains actual proofs/tests and exhaustive78/1064
registration/signature/axiom artifacts, all29constructor fixtures and8exactsource
pins. The immutable packet beside this checkout records its full committed head,
exact original base/branch/repository, full original patch/bundle, command
exits/times/RSS/cgroup peaks and SHA256 manifest. Continue the original goal on
the same branch: recursive tree identity, public uniqueness, accepted-tree
corollary and full integration gates remain unfinished. No goal completion.


## Recursive container and type identity checkpoint

Fourteen new modules add78declarations, totaling92modules/1142declarations.
WordUnique and VectorUnique are structural induction predicates on the original
Syn categories, not a new AST or producer interface. Lists retain item vectors;
empty optional tuple components cannot be flattened away. Generic list and
optional expression steps, actual argument/name cuts and parameter optional
location/name boundaries recover intrinsic identity from actual child IHs.
The global mutual induction has not yet supplied all expression cases.

Every one of the5typeconstructors now has an identity step against any certified
type competitor, conditional only on structural identity for its actual children.
Array/atom disjointness derives the original type spine/atom cut and nonempty
dimensions. Elementary dimensions and identifier paths are arbitrary. Mapping
keys use the existing unindexed MapKey; actual key-name/arrow/value-name syntax
derives all concrete boundaries. Parameter nonemptiness follows from the existing
unconditional operand completion invariant. Arbitrary successful attribute order
lists invert to0/1/2existing fields without an assumed length or canonical order;
disjoint token filters recover optional visibility/mutability independently of
layout witnesses. Function params/returns vectors reconstruct, including empty
vectors, before listchild IHs apply. These conditional steps are not a public
uniqueness instance or a new global premise.

Arbitrary arrayTypeFamily depths discharge all recursive identity premises and
compare against ANY certified type competitor, not only another family member.
Existing exact family certificates establish non-vacuity. Arbitrary optional-hole
vectors similarly identify any certified competitor; their flattened word is
empty for every length, a negative list control, not an expression ambiguity.
All original refusals, observations, budgets and public target remain unchanged.
Initial induction-context/Boolean-parenthesization, dependent MapKey match and
append/filter normalization errors are retained. All1142exact standard-only axiom guards, actual kernel signatures and MCP
checks pass without owned warnings. Versions/KeySort pass before RUNTIME_GATE_PASS
under the unchanged hard memory/no-swap/thread/reserve limits. Checkpoint acceptance, corruption controls and documentation paths PASS. Full
default acceptance exits1 ACCEPTANCE_OPEN; global roots/orphans stop at92frozen
registrations before library/TestSuite build. Trust3764zero/layers559zero PASS;
central source-axiom inventory has zeroerrors but1142unrecorded pins and exits1.
Independent finder/skeptic final metadata reviews accept92/1142after separate
checkpoint/corruption reruns, no remaining findings; public target remainsopen.


### Recursive checkpoint handoff

The substantive checkpoint contains all14newmodules, exact92/1142kernel
type/axiom inventory, exhaustive registration proposals and actual bounded gate
evidence. Separate read-only finder/skeptic source and metadata verdicts accept
this partial work, no Lean server/edits; records are evidence/reviews-recursive.json.
Signature-audit-recursive, checkpoint-proof-recursive, recursive-acceptance,
recursive-controls and recursive-doc-paths PASS. Full/default acceptance remains
exit1; actualglobalroot/orphan failures92 and central1142unrecorded standardpins
are not waived. Trust3764zero/layers559zero PASS. Exact versions, KeySort before
RUNTIME_GATE_PASS, sourcehashes/exits/times/RSS/cgrouppeaks and failed attempts are
retained in commands-proof/evidence. The immutable packet records committed
head/base/branch/repository, original patch/bundle and checksum manifest.

Continue the same goal/branch: all expression constructor identity steps and the
exhaustive mutual induction, public CertifiedYieldUnique, parseCat corollary,
scope-complete final acceptance and registration-dependent full gates remainOPEN.
No target/premise/exclusion/refusal/observation/budget change or goal completion.


## Complete original proof checkpoint

Eight added modules bring the lane to100modules/1241source declarations.
All29expression constructors have actual structural identity steps. Certified's
exhaustive Syn induction closes every required expression/type/parameter/list/
optional/argument cycle; no child uniqueness premise remains in the public
theorem. CertifiedYieldUnique's original definition and premises are unchanged.
Accepted-tree corollaries use original parseCat_sound and the proved uniqueness,
not parser determinism. Per-file MCP reports zeroerrors for assembled proofs;
actual final kernel/signature/axiom gates PASS without owned warnings.

The checker now binds the unchanged original target text, exact public theorem
signatures,29constructor identity steps and induction cases,17root levels and
all34intrinsic operator constructors, plus actual kernel types/axiom guards and
current source/runtime/fixture pins. It rejects an extra circular public premise,
a changed target, missing/remapped step, missing operator or boundary. The pinned
AssignOp has12constructors; a previous prose count13was corrected without any
syntax, observation, refusal or theorem change. Full/default task acceptance
remains closed until frozen registration-dependent global gates pass.

New inhabited arbitrary-family controls vary type array depth, parameter count,
optional returns and both successful visibility/mutability orders inside a
meta-type ARRAY wrapper. The original DIRECTfunction-type meta refusal remains
proved, with no broadened exclusion. Arbitrary tuplehole counts preserve all
commas and compare against any certified competitor. Earlier string/layout,
unary/postfix/group/mixedbinary/conditional/array controls and all130exactexternal
parsing-only observations remain unchanged. Initial comma-vector normalization,
missing-import/optional-category and flatten normalization failures, including
assembled diagnostics_unavailable, are retained and never counted as passes.


### Complete proof checkpoint handoff (integration pending)

The unchanged CertifiedYieldUnique target is inhabited by certifiedYieldUnique;
certified_expression_yield_unique exposes exactly independent Derives+prec
premises. parseCat_expression_accepted_unique and parseCat_expression_same_source
follow from original parseCat_sound. Actual axiom sets for these public theorems
are exactly propext, Classical.choice and Quot.sound. No sorry/admit/unsafe or new axiom declarations were introduced; no premise,
exclusion, refusal, observation or proof budget was weakened or raised.

All100modules/1241explicit source declarations have actual kernel signatures and
exact standard-only axiom guards. All2323unique owned logical declarations have
full actual type/axiom evidence, through2447audited emissions/124consistent repeats.
The full type trace is losslessly archived;387extra metadata names distinguish
34already-audited logical overlaps from353compiler-only names. The Lean-importing
auditors are verification tests only, never dependencies of the library. Source
proof versus external130parsing-only observations versus compiler-codegen metadata
remain distinct. All29expression/all13recursive cases,17levels,34operators,
8frozen source pins, fixtures and arbitrary inhabited/negative controls are bound
by acceptance, including adversarial provenance/owner/archive/target checks.

Clean signature-audit-complete-final and checkpoint-proof-complete-final PASS;
actual Lean4.24.0/Lake5.0.0-src+797c613 and KeySort377/131 PASS before
RUNTIME_GATE_PASS. Streamed bounded proof acceptance and corruption checks PASS
with zero resource stop; two eager reserve-stopped attempts are preserved as
failures and explicitly recovered. Environment enumeration/audit tools and all
library hashes are bound to successful resource-limited execution evidence.

Actual globalrun-lean/orphans exit1at100frozen local registrations BEFORE full
library/TestSuite confirmation. Trust3772sources/285sites/zero findings and
layers559core/zero violations PASS. Central axiom-source inventory has zeroerrors
but1241unrecorded standard pins and exits1. No integration gate is waived. The
owned manifest proposes registration/map/pins and records already-published
Fragments for coordinator deduplication. Full/global task acceptance and final
integration gates remainOPEN; the original persistent goal is not completed.

The checkpoint commit and immutable packet record exact base/head/branch/repository,
full original patch/bundle, actual signatures/axioms/commands/exits/timings/RSS/
cgroup peaks, independent reviews, complete source pins and SHA256 manifest.
Continue on the same branch after coordinator integration; do not create/reset a
goal, push, merge, change frozen roots/registries or expand scope.


Final independent finder and skeptic source/streaming/metadata verdicts PASS,
each with an independent current streamed proof-audit rerun and no remaining
findings. Their actual verdicts and boundaries are in evidence/reviews-complete.json.
This is a complete original SOURCE PROOF checkpoint with an integration-blocked
assignment status, not full RUNTIME/task acceptance. Required global registrations,
central pins and library/TestSuite/corpus/strict integration validation remainOPEN.
The goal is retained and not marked complete. No scope question is pending.

## Claude-VM reviews

**Post-split finder and skeptic (2026-11-05).** Both were read-only and neither
used the Lean server.

- **Skeptic: no refutation.**
  - `CertifiedYieldUnique` is unchanged, and `Syn`, `Derives`, `prec` and `Tok`
    are the existing definitions.
  - There are no smuggled premises: no sorry, axiom, opaque, native_decide,
    set_option, variable or class anywhere in the area.
  - `AxiomPins.lean` imports all 99 other modules and holds 1241 pins. Their
    axiom union is {propext, Classical.choice, Quot.sound}.
  - e48d82a2 deleted no `.lean` file, and the layer check is clean.
- **Finder: no `.lean` file deleted.** e48d82a2 deleted 671 json, 376 log,
  43 tsv, 43 HEAD and 4 gz files. Every root import resolves, the EU-01 count is
  29 = 29, and no file uses forbidden constructs.
- **Confirmed findings, all fixed:**
  1. This document still claimed the externalized evidence and the removed
     tooling as present. Fixed by the current status section above.
  2. `checker-controls.py` read deleted evidence and failed its positive
     baseline. It is rewritten: synthetic gate logs exercise the build-log
     checks (stale digest, failed exit, partial gate, error lines, missing log),
     the axiom-report controls corrupt `AxiomPins.lean`, and the kernel
     environment controls run only when the evidence is restored.
  3. `refresh-audit.py pins` read a deleted log. It now takes `--report`.
  4. `--checkpoint` accepted any log that said "Build completed successfully".
     It now requires a `gate.sh` log whose `SOL_EU_SOURCES` digest equals the
     current sources, `SOL_EU_FULL_GATE ./run-lean.sh`, `SOL_EU_EXIT 0` and no
     error or failed job.
  5. The `--proof` docstring overstated what it checks. It now says that mode is
     static only.
  6. `obligations.json` (EU-12, EU-13) and `registration-manifest.json` (rows
     file, note, central pins, kernel inventory) were stale. They are updated.

## Sealed handoff (Claude VM)

- **Branch:** `cloud/moved4-20261105/expression-uniqueness`.
- **Start:** `cloud/expression-uniqueness-move` (c2e862c1) merged, plus master
  aec9adf1, which was already contained.
- **Toolchain:** Lean 4.24.0, Lake 5.0.0-src+797c613. The VM had 4 cores and
  15 GB of RAM; Lake ran in its default parallel mode.

**Headline theorems, kernel-checked by the library build.** Each pins
`[propext, Classical.choice, Quot.sound]` in `AxiomPins.lean`:

```lean
theorem certified_expression_yield_unique (a b : Syn .expr) (ts : List Tok)
    (da : a.Derives ts) (ha : a.prec = true) (db : b.Derives ts) (hb : b.prec = true) : a = b
theorem certifiedYieldUnique : CertifiedYieldUnique
theorem parseCat_expression_accepted_unique {p : Nat → P (Syn .expr)} {src : Bytes}
    {tree : Syn .expr} {layout : List Choice} (accepted : parseCat p src = .ok (tree, layout)) :
    ∃ ps, lex src = .ok ps ∧ tree.toks layout = some (tokensOf ps) ∧ tree.prec = true ∧
      ∀ other : Syn .expr, other.Derives (tokensOf ps) → other.prec = true → tree = other
```

All 1241 declarations of the area are pinned with standard axioms only, and
recorded centrally in
`scripts/g07-axiom-pins.d/Solidity/Frontend/ExpressionUniqueness/AxiomPins.json`.

**Gates, all passing:**

| Gate | Result |
|---|---|
| `tests/sol-expression-uniqueness/gate.sh LOG`, which runs `./run-lean.sh` with `SOLKEY_RULES` set to the pinned snapshot | exit 0; build completed (5922 jobs); KeySort 377 taclets, 131 read-bearing, OK |
| `python3 scripts/check-sol-expression-uniqueness.py --build-log LOG` | CHECKPOINT_PASS (1241 guards, 100 modules); ACCEPTANCE_PASS |
| `python3 tests/sol-expression-uniqueness/checker-controls.py` | all controls pass; the kernel-environment controls are skipped because their evidence is externalized |
| `node scripts/check-orphans.mjs` | 5906 reachable, 0 orphaned |
| `register.sh --check`, `fragments.sh --check` | pass |
| `sha256sum -c tests/sol-expression-uniqueness/SOURCE-SHA256SUMS` | pass |
| EU-01: constructor list against current `Syntax.lean` | 29 = 29 |

`gate-logs.sha256` lists the hashes of the gate logs; the logs themselves are
not in git.

**KeySort and the sibling checkout.** Without `SOLKEY_RULES`, `check-solkey.sh`
reads `../solkey`, which on this VM is upstream `main` (b8d5f88), not the pin
`473da8944c`. Against that checkout it reports 167 mismatches. The check is
defined against the pinned snapshot (`docs/solkey-migration.md`), and at the pin
it passes. The mismatches come from the unpinned checkout, not from this lane.

**Slow modules.** These took over 60 s as dependency builds while four jobs ran
in parallel: `ExpressionUniqueness.Families` 118 s (the Codex VM recorded about
188 s) and `ExpressionUniqueness.ExpressionLowFree` 99 s. Nothing in this lane
changed them.

**Not re-run.** The 130 external solc parsing observations and the
kernel-environment dump audit depend on the H44 evidence and on the pinned
soljson (sha256 `6c74ffba…`), and neither can be reached from this VM. They are
external tests, not part of the kernel proof.
