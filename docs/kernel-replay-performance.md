# Kernel replay and the 100× target

A 100× improvement to the complete IDE has **not** been achieved. Generated C
already runs the small symbolic walk very quickly; that phase's speed cannot
be substituted for a checked program proof or extrapolated to startup, Solidity
compilation and editor transport.

## Why the current certificate replays computation

Lean must check evidence, but it need not repeat the search that found that
evidence. Our reflective certificate is an equality such as
`residueWithin ... = some []`, proved with `Eq.refl (some [])`. Accepting it
requires reducing the left side. The native C result is an oracle; the kernel
does not trust it in place of that reduction. Removing kernel validation or
using a trusted native-decision axiom would change the trust contract.

A certificate containing selected rule applications and small local witnesses
could avoid replaying the complete strategy. It still needs efficient leaf
evidence. Earlier explicit per-rule tactics were slower; changing to `⊢` alone
does not solve this. The new measurements locate the remaining work more
precisely.

## Uncached phase measurements

[Raw evidence](benchmarks/kernel-replay-2026-11-03.json) includes every trial,
source hashes, runner, helper hashes, failed prototypes and extension reports.
`ReplayCosts.lean` disables `mkAuxLemma` caching for **every** timed stage. A
fresh contract namespace alone is insufficient: two transformations within
one case can produce the same expression. Initial sub-millisecond sliced
results were cache hits and were discarded.

The diagnostic retains branch refutation in the walk, but leaves terminal
leaves open. It checks that walk's result and then checks each terminal leaf
separately. Values below are medians of rounds 1–2, in milliseconds. Independent
stages are checked on quoted intermediate formulas; their times should not be
summed as a prediction of a monolithic certificate.

| Program | Walk + refutation | Original leaf | Lower leaf | Decide lowered leaf | Remove trivial premises | Decide trimmed leaf |
|---|---:|---:|---:|---:|---:|---:|
| constant | 28 | 119 | 11 | 117 | 3 | 22 |
| identity | 41 | 171 | 24 | 144 | 2 | 51 |
| assignment | 38 | 221 | 48 | 152 | 5 | 121 |
| increment | 67 | 606 | 70 | 471 | 7 | 320 |
| branch | 101 | 943 | 48 | 914 | 4 | 535 |
| false constant | 34 | 220 | 14 | 205 | 3 | 37 |

Terminal leaf checking dominates. Dependency slicing had little consistent
benefit with caching disabled. Dropping every premise made several simple
checks cheaper, but left increment unproved. Removing only literal
`true = true` premises kept all four previously closing examples closed;
branch and false constant remained open. A staged dependency-slice prototype
also constructed and audited complete proofs for the four closed examples,
but its total cost did not justify shipping it.

These are diagnostic component certificates, **not** complete specification
proof timings or new SolKey comparisons. Their native plugin is the recorded
optional C-inspection build; helper callbacks are local Lean definitions.
Only kernel checking intervals are compared here, not native execution versus
interpreted callback timings. Sampling and timing order matter; the raw data
also retains earlier exploratory runs with different namespaces.

## Change kept in the extension

Version 0.5.2 uses a proved trimmed-leaf checker in the existing bounded
closed-spec proposal. It retains the original bounds, the original leaf checker
as fallback, the final synchronous kernel check, the standard-axiom audit and
saved-state retry. Dropping premises strengthens the formula; `dropPrem_holds`
proves the connection. The normal `sol_prove` implementation is unchanged.

The proposal remains restricted to small specified state-writing programs.
The website's default keeps this optional route disabled. Failed proposals
consume part of the original allowance, so fallback does not guarantee every
previous near-budget success.

Matched extension-worker measurements use the same 18 source variants before
and after, with one real Lean LSP process per run and document versions 1–18.
They include IPC and proof checking with precompiled solc ASTs; they exclude
Solidity compilation and GUI latency. Warm medians, milliseconds:

| Program | 0.5.1 proposal | 0.5.2 proposal |
|---|---:|---:|
| constant | 385 | 364 |
| identity | 444 | 458 |
| assignment | 419 | 359 |
| increment | 801 | 648 |
| branch | 1145 | 1033 |
| false constant | 310 | 311 |

Assignment latency decreased 14%; increment decreased 19%. Only state-writing
cases activate this change. Other differences, including first checks of
3236 and 2510 ms, cannot be attributed to the change from these small samples.
This is a further improvement, not a 100× speedup or established SolKey parity.

## Reproduction

Prepare the pinned fixtures with `SOLJSON_DIR` set to the local compiler cache:

```sh
node scripts/measure-simple.mjs
python3 scripts/measure-replay-costs.py /path/to/lean-4.24.0-linux \
  --plugin /path/to/optional/frontend-plugin.so
node vscode/test/measure-proof-speed.cjs .lake/proof-speed.json
```

The optional plugin's hash is recorded. Omit `--plugin` to run without it;
those execution-envelope times are not native performance measurements.
Use the repository's writer lock, memory guard and thread limits. The phase
benchmark is diagnostic and deliberately not added to the default CI suite.

The positive regression asserts the new `SpecProposal.sound` proof constant.
The corrupted-oracle test now corrupts the **new** `SpecProposal.quoteResidue`
C entry point: the kernel rejects falseStore, semantic fallback leaves it
pending, and a subsequent true store proof succeeds. Read-only finder/skeptic
reviews found the initial cache confound and stale negative-control target;
both were corrected before accepting the evidence.

## Final validation

The frontend, positive regression and diagnostic helper pass per-file Lean
MCP checks. The frontend target builds; the layer check remains 194 core
modules with zero elaborator reachability. Extension tests pass 83 checks with
two optional checks skipped, and all 11 real LSP checks pass. The 0.5.2 VSIX was
built and its packaged worker verified against the tested source; no new VS
Code GUI-host run was performed.

The rebuilt single-file website passes all 14 offline regressions, including
proofs in a fresh runtime after disconnecting the static host. Peak owned RSS
was 4.20 GiB under the unchanged memory guard. Earlier multi-file cache-
preparation attempts and a RAM-profile run stopped by the memory guard are
not counted as passes. The accepted browser result is for the single-file
artifact with the proposal option disabled.
