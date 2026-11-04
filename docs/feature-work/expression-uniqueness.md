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
consumes the entire layout; an unconsumed `Syn.yield` suffix is insufficient.
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
`declarations.json` enumerates all 138 source declarations with source signatures;
`signatures.lean` and its kernel output report their actual types and axiom sets.
The eight modules are proposed for coordinator registration, with module-map rows,
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
first element and are nonempty. No expression-empty-yield theorem is claimed yet.

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
| `Families` | Unbounded certified negative-prefix family with exact yields and injectivity in depth; arbitrary-depth grouping precedence preservation. Grouping-family yields are not yet proved. |
| `Fragments` | Arbitrary-byte/length-list reconstruction, exact fragment count, independent-layout byte uniqueness, inhabited single and zero-length-leading fragment controls and distinct layouts. |
| `Primary` | Deterministic identifier/boolean/number/unit/elementary yields; identifier, boolean and numeric injectivity; all five literal families, including string tags, arbitrary payload lengths and independent layouts, have same-yield uniqueness. Other expression roots and recursive types remain open. |
| `Statement` | The original open uniqueness proposition; no proof value. |
| `Fixtures` | All 29 accepted-root controls, four documented refusals, four additional postfix bases and grouped accepted alternatives, proved with `decide +kernel`. |
| `AxiomPins` | Exact `#guard_msgs` axiom pins for all 138 source declarations; actual sets use only `propext` and `Quot.sound`, or no axioms. |

`firstTop_cut_unique` has token-machine `skip` hypotheses. They are NOT assumed in
the original expression target and do NOT close root reconstruction. Likewise
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
`checkpoint-proof-final.log` records the passing permitted KeySort result BEFORE
`RUNTIME_GATE_PASS`: 377 taclets parsed, 131 read-bearing, 131 matched. Runtime
success is not full assignment acceptance. The same command passed MCP diagnostics
and the per-file kernel axiom-pin gate at the exact module hashes recorded in
`checkpoint-proof-final.inside.json`. It took 13.235280 seconds, child peak RSS
233444 KiB, exact container peak 699457536 bytes, minimum parent headroom
15813529600 bytes, with zero OOM events. These figures describe that command,
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
check: exactly these eight modules lack central root imports. The orphan gate
reported the same eight. Source trust passed (3680 sources, zero findings), and
layers passed (559 core modules, none reaching elaboration or checked adapters).
The global axiom-source gate reported zero errors but exited 1 for 138 unrecorded
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

Next, derive delimiter and scanner invariants from arbitrary certified expression,
type, argument, list and option yields, then reconstruct precedence roots. A raw
punctuation split is insufficient: `-` is both a prefix and binary token, and
conditional middle expressions mask nested assignments/colons. Prove those facts;
do not add a desired split, parse completeness or uniqueness as a premise.
Then finish grouping/tuple holes, primary cross-root disjointness, member/index/
slice/call/options reconstruction and recursive type uniqueness, derive the public
theorem and accepted-tree corollary, and complete full boundary controls and gates.
The full sealed proof handoff remains open. Current artifacts are explicitly a
partial proof checkpoint. No push, merge, PR, producer edit or scope expansion.
