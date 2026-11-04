# SOL-EU: certified expression yield uniqueness

Status: substantive partial proof checkpoint. H26 resolved runtime setup on this
same VM; EU-R1 is closed without changing limits. The full assignment is NOT
complete. Expression root reconstruction, public uniqueness and the accepted-tree
corollary remain open. No ambiguity has been established.

Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Branch: `codex/solidity-sol2-20261104/expression-uniqueness`.
Repository: `/workspace/solidity-lean`. The previous inventory-only commit
`7642fc89d68bc9ee12acceafcd829902d532f960` and its failed setup probes remain honest
history. The current immutable packet records its own exact committed head.

## Original theorem target (open)

`CertifiedYieldUnique` in `Statement.lean` records this proposition in the existing
namespace `Solidity.Frontend.ExpressionUniqueness`:

```lean
∀ (a b : Solidity.Source.Syn .expr) (ts : List Solidity.Frontend.Checked.Tok),
  a.Derives ts → a.prec = true →
  b.Derives ts → b.prec = true → a = b
```

It is a definition of an OPEN obligation, not a theorem inhabiting it. Layouts
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
determinism alone does not establish this. The corollary is still open.

## Exhaustive inventory and scope

`tests/sol-expression-uniqueness/constructors.json` enumerates all 29 expression
constructors in intrinsic declaration order, boundaries, root levels, root
conditions, layouts and open reconstruction obligations. `constructor-controls.json`
assigns a kernel-checked accepted-root fixture to every constructor.
`declarations.json` enumerates all 917 source declarations with source signatures;
`signatures.lean` and its kernel output report their actual types and axiom sets.
The fifty-eight modules are proposed for coordinator registration, with module-map rows,
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
| `TokenSplit` | Arbitrary-list delimiter execution, append and untouched-stack-suffix laws, equivalence of empty-stack balance and contextual balance, enclosure, mixed nesting, skipping enclosed markers and whole token-cut uniqueness. Deriving scanner hypotheses from every expression certificate remains open. |
| `Refusals` | Whole-`Syn.prec` refusal for both prefix/postfix readings, both conditional-assignment readings, all postfix-base classes, direct-new alternatives and all left/right association classes, for arbitrary subtrees and parameterized operator values. These constrain trees; they do not reconstruct roots from tokens. |
| `Families` | Unbounded certified negative-prefix family with exact yields and injectivity in depth; arbitrary-depth grouping precedence preservation. Its grouping-yield obligation is now discharged by `Grouping`. |
| `Fragments` | Arbitrary-byte/length-list reconstruction, exact fragment count, independent-layout byte uniqueness, inhabited single and zero-length-leading fragment controls and distinct layouts. |
| `Primary` | Deterministic identifier/boolean/number/unit/elementary yields; identifier, boolean and numeric injectivity; all five literal families, including string tags, arbitrary payload lengths and independent layouts, have same-yield uniqueness. Other expression roots and recursive types remain open. |
| `Statement` | The original open uniqueness proposition; no proof value. |
| `Fixtures` | All 29 accepted-root controls, four documented refusals, four additional postfix bases and grouped accepted alternatives, proved with `decide +kernel`. |
| `YieldShape` | All 29 expression roots have exactly one nonempty item on every successful partial-layout execution; optional empty tokens identify absence, and `some e` preserves the expression printer. |
| `YieldBalance` | Compositional balance for items, flattening, separators, type spellings, operators and literal fragments. |
| `AttributeBalance` | Actual successful function-type attribute layouts preserve balance, including arbitrary order lengths. |
| `ExpressionBalance` | The expression/type/parameter/argument/list/option closure yields balanced items; `expr_derives_balanced` derives balance from the original token certificate. Arbitrary closing-token prefixes cannot be expression yields. |
| `DelimiterReconstruction` | Enclosing payload and suffix spans are reconstructed from actual certificates; closing-selector skip facts are derived, not supplied as premises. |
| `Grouping` | Actual group certificates invert to child certificates; group-prefix spans are unique. Arbitrary grouping depth has exact tokens, inhabited certification, token-depth injectivity and tree-depth injectivity for a fixed printable base. |
| `ReverseSplit` | Mirrored step/run/skip reversal at arbitrary stacks, suffix-scanned last-marker cuts, inhabited arbitrary mixed nesting with hidden add markers, and an explicit malformed-word negative control. Operator-selector freedom from precedence remains open. |
| `SeparatorSplit` | Actual commaSep injectivity on nonempty component vectors, allowing empty words; arbitrary hole-count reconstruction; explicit zero-vector versus single-empty collision. |
| `CommaFreeAlgebra` | Comma-free token/item/attribute algebra; enclosures need only balanced interiors, allowing internal commas. |
| `ExpressionCommaFree` | Exhaustive expression closure yields have no top-level commas; original expression certificates supply every scanner condition in certified component-span reconstruction. This concludes word-vector equality, not child-tree equality. |
| `LowFreeAlgebra` | Joint question/assignment selector includes all 13 assignment operators; loose-root-free token, type-spelling and attribute algebra. |
| `ExpressionLowFree` | Existing recursive precedence plus level ≥ 2 derives loose-marker freedom for all expression roots; type and call-argument outer words are unconditionally free, including arbitrary enclosed descendants. |
| `LowRoot` | Existing certificates determine assignment versus conditional versus higher root class and the assignment operator. Assignment and conditional child spans are now proved in BinarySpans and ConditionalSpans; recursive tree identity remains open. |
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
| `RootLevels` | Original certified root levels agree whenever either is<=14, also for independent partial layouts. Postfix15 versus primary16 remains open. |
| `LastEnclosure` | Arbitrary trailing balanced enclosures reconstruct their payload and preceding word using the existing mirrored first-cut theorem. |
| `PostfixYieldSplit` | Actual index/slice/call/options/namedArg executions invert into existing child states; callArgs gives its genuine balanced parentheses payload. |
| `PostfixSpans` | Actual index/slice/call/options children reconstruct; index and slice roots are disjoint; options preserve the full tail word vector. |
| `MemberSpans` | Member/namedArg names and child words reconstruct, including arbitrary strings and the special member address token. |
| `StartAlgebra` | Balanced first-token invariant forbids only an initial opening brace, allowing arbitrary later braces. |
| `ExpressionStart` | All29expression/type/param/argument closure derives that first-token invariant; callOptions uses its actual nonempty base. |
| `ArgumentWords` | Actual expr/namedArg list components are nonempty; full comma-vector uniqueness permits empty lists and handles the generic empty-word collision. |
| `ArgumentSpans` | Positional/named arguments are disjoint and reconstruct their actual component vectors, including empty lists. |
| `PostfixControls` | Arbitrary mixedall5postfix tower has exact inhabited certificates and family identity; arbitrary optional holes refute false nonemptiness generalization. |
| `AxiomPins` | Exact `#guard_msgs` axiom pins for all 917 source declarations; actual sets use only `propext`, `Classical.choice` and `Quot.sound`, or no axioms. |

`firstTop_cut_unique` has token-machine `skip` hypotheses. They are NOT assumed in
the original expression target. Delimiter/grouping corollaries now derive their
skip facts from certificates, while arbitrary precedence-operator root
reconstruction remains open. Likewise
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
or kernel uniqueness proofs. Those broader obligations remain open.

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
`checkpoint-proof-postfix-final.log` records the passing permitted KeySort result BEFORE
`RUNTIME_GATE_PASS`: 377 taclets parsed, 131 read-bearing, 131 matched. Runtime
success is not full assignment acceptance. The same command passed MCP diagnostics
and the per-file kernel axiom-pin gate at the exact module hashes recorded in
`checkpoint-proof-postfix-final.inside.json`. It took 38.161475 seconds, child peak RSS
260780 KiB, exact container peak 856805376 bytes, minimum parent headroom
15530790912 bytes, with zero OOM events. These figures describe that command,
not all earlier builds. Every other run has separate command/exit/time/RSS records;
failed attempts and unavailable-tool probes remain retained. Sampled cgroup usage
is labeled separately from exact memory.peak and per-child RSS.

`check-sol-expression-uniqueness.py --inventory` validates all source/base pins,
constructors, modules, declarations, proposed rows, fixture references and axiom
guard inventory. `--checkpoint` additionally requires current-source kernel
signature/axiom evidence, runtime bounds, KeySort and compiler observations.
Default full acceptance remains exit 1 while the original target is open. Changing
ledger statuses alone cannot turn the partial checkpoint into full acceptance.
The actual `./run-lean.sh` attempt exited 1 before building, at the frozen-root
check: exactly these fifty-eight modules lack central root imports. The orphan gate
reported the same fifty-eight. Source trust passed (3730 sources, zero findings), and
layers passed (559 core modules, none reaching elaboration or checked adapters).
The global axiom-source gate reported zero errors but exited 1 for 917 unrecorded
new standard pins. Proposed module/map rows and the exact axiom registration
reference are in the manifest for coordinator integration; the worker did not
edit frozen roots or trust inventory. These failed global gates are not counted
as passes. Full library/TestSuite confirmation has not run past registration.
They remain distinct from this passing partial proof checkpoint.

## Reviews and next work

Separate read-only finder and skeptic reviews used no Lean server. Neither found
an ambiguity or a defect in the helper proofs. They caught stale inventory-only
documentation/manifest/checker claims (F2/F3); these were replaced with the actual
proof state and current-source evidence checks. Final review also found missing
fixture-statement linkage (F4/S3) and unchecked signature-command success (S2).
The checker now binds each constructor fixture to its exact theorem/input/root
signature, requires successful bounded signature execution and its kernel gate,
and has explicit corruption controls for these findings. The earlier missing pin-set check
(F1/S1) remains fixed and has deletion/corruption controls. Final checkpoint review
results are saved under the evidence directory; future proof checkpoints still
require their own reviews.

The expression-closure delimiter invariant and grouped/enclosed span reconstruction
are now proved. The comma separator and joint loose/non-minus binary marker invariants are now
derived from certificates. The rank-ten operand-state invariant is now proved. Conditional colon spans are now proved. Next complete high-root span
decomposition and recursive child identities. A raw
punctuation split is insufficient: `-` is both a prefix and binary token, and
conditional middle expressions mask nested assignments/colons. Prove those facts;
do not add a desired split, parse completeness or uniqueness as a premise.
Then finish multi-component tuple/list reconstruction, primary cross-root disjointness, member/index/
slice/call/options reconstruction and recursive type uniqueness, derive the public
theorem and accepted-tree corollary, and complete full boundary controls and gates.
The full sealed proof handoff remains open. Current artifacts are explicitly a
partial proof checkpoint. No push, merge, PR, producer edit or scope expansion.

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
records are in `evidence/reviews-postfix.json`. Current-source acceptance and
917 exact standard-only axiom pins pass. Fresh published-master verification
hashes all8pinnedinputs and the integrated Fragments against this checkout;
all match (`evidence/published-master-verification.json`).
