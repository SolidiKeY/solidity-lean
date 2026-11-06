# Extension proof-checking improvement

The VS Code worker in version 0.5.1 opts into a bounded closed-derivation
proposal for small state-writing specifications. It improves warm assignment
and increment verification in the real extension worker while retaining the
original source obligation, synchronous kernel check and standard-axiom audit.

This is an initial improvement, not elimination of the main certificate cost.
The [generated-C measurements](generated-c-performance.md) found a native walk
roughly 100–300 times faster than its kernel replay. The new path still has to
check a residue certificate in the kernel. Its **end-to-end worker improvement
is 1.6–1.8 times**, not 100 times. A compact typed certificate checker remains
the larger architectural target; trusting unchecked C is not this change.

## Selection and checking

`sol.testing.closedSpecs` defaults to false. The desktop worker enables it;
the static website retains its existing default path. The proposal visits at
most 2048 existing expression nodes, considers programs containing `Stmt.assign`
or `Stmt.assignMem`, and computes a walk bounded to 128 steps. The oracle step
uses at most five million raw heartbeats, capped by the enclosing allowance.
Structural bounds and heartbeat checks do not guarantee a wall-time limit for
compiled execution; the existing worker timeout remains active.

Only an empty residue produces a candidate. Open residues immediately retain
the original semantic tactic, avoiding an expensive kernel replay before a
known-open result. Successful proposals construct `SpecProposal.sound`
and apply `Proves.fmlValid`. Since 0.5.2, the proposal first tries a leaf with
literal `true = true` premises removed; a proved strengthening theorem connects
that smaller leaf to the original. See [kernel replay measurements](kernel-replay-performance.md). An explicitly typed `id` keeps the exact residue
equality certificate in the proof term. The final `addDecl` checks it in the final declaration rather than creating
a separate auxiliary theorem.

The native oracle is not trusted as a proof. Kernel or axiom rejection restores
the saved environment and retries the original tactic under the same absolute
heartbeat deadline. Oracle/checking work consumes that original allowance;
this does not guarantee preservation of every previous near-budget success.
Callbacks, recursion and ordinary non-specified obligations retain their prior
strategies. Internal `options.closedSpecs=false` permits a worker control; no
new implementation setting is exposed in the editor UI.

The extension continues to use its standard Lean/Lake LSP session. It does not
load the optional C benchmark plugin; this release is not a full AOT backend.
The C measurements motivated the checking-strategy change.

## Worker measurements

[Raw evidence](benchmarks/extension-proof-speed-2026-11-02.json) retains the
exact source hashes, result rows, Lean PIDs/document versions, test output and
negative-control output. Each off/on run verifies three rounds of six matched
programs. Changing source hashes and document versions force real checks; no
cached-report retrieval is timed. Each run retains one Lean process, while the
off and on runs use separate processes. The same compiled frontend is used.

The table gives medians of rounds 1–2 in milliseconds. It includes extension
worker IPC and proof execution using precompiled pinned solc AST fixtures;
Solidity compilation and editor UI latency are excluded. These are local
samples, not throughput guarantees.

| Program | Proposal disabled | Proposal enabled |
|---|---:|---:|
| constant | 363 | 341 |
| identity | 494 | 450 |
| assignment | 766 | 478 |
| increment | 1453 | 821 |
| branch | 1121 | 1018 |
| false-constant | 330 | 259 |

Only state-writing cases receive the new strategy. Other small differences
are sampling variation. Cold first checks, including Lean session startup,
were 2.77 and 2.79 seconds: this change does not solve cold startup.

The earlier all-specification prototype added avoidable overhead on trivial
returns and false constants. It was narrowed before release. Eight additional
fixture functions cover branches, two sequential choices, storage after a
branch, a straight storage write and three false postconditions.

## Validation and use

The rebuilt static website passes all 14 offline regressions with the default
proposal option disabled. The 0.5.1 VSIX was built and its packaged worker
verified against the tested source. No new VS Code GUI-host run was performed.
The real persistent LSP regression passes all 11 checks, including live edits,
cache identity, cancellation and certified counterexamples. The extension
suite passes 83 checks with two optional integration checks skipped. The
closed-specification regression verifies both statuses and the checked proof's
derivation head. Per-file Lean MCP diagnostics pass.

`scripts/check-spec-proposal.py LEAN_PREFIX` builds a deliberately corrupted
native oracle in a separate test plugin. Logical definitions are unchanged.
The oracle falsely reports the false storage claim as closed: the final kernel
rejects it, the worker retries semantic checking, and the claim remains pending.
The test checks that the rejected declaration does not leak and that a later
valid storage proof succeeds. Runtime markers assert that the corrupted oracle
was actually called. This control passes; the ordinary positive/false regression
is also wired into the Pages workflow.

Rebuild `Solidity.Frontend.Testing` with the pinned toolchain and install the
matching extension package. The benchmark can be repeated with:

```sh
PROOF_SPEED_CLOSED_SPECS=0 node vscode/test/measure-proof-speed.cjs before.json
node vscode/test/measure-proof-speed.cjs after.json
```

Generate the standard fixtures first with `scripts/measure-simple.mjs`. Follow
the repository's thread/memory guards. Read-only finder and skeptic reviews
checked proof certificates, rollback, deadlines, benchmark cache isolation and
scope. Their budget-completeness and timing-scope caveats are retained above.
