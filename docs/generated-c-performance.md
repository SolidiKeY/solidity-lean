# What the generated C spends time doing

The native walk is already fast on the six small programs. The dominant cost
is the separate kernel check of its residue certificate. These measurements
inspect native C; they do not establish browser/WASM performance or complete
program-proof timings.

## The call paths

The generated `ProvesDerive.c` contains a direct native call chain:

```text
Seq.residueQuoteWithin___redArg
  → Seq.run___redArg
    → Seq.runK___redArg
  → leafQuoteS → leafCheckS
```

The callbacks are C function pointers. The generated wrapper also erases an
unused context argument before calling the reduced-argument implementation.
No handoff to Lean's project-code interpreter was found inside this measured
walk. Allocation/reference-count operations are present, but their presence
alone does not identify the bottleneck.

A different path creates the certificate:

```text
Seq.prove.lemmaFor
  → Derive.kernelLemma
    → Lean.Meta.mkAuxLemma
      → addDecl → kernel declaration checking
```

The certificate has the form `residueWithin ... = some leaves`. Its value is
`Eq.refl (some leaves)`. To accept that value at the stated equality type, the
kernel must establish definitional equality by reducing `residueWithin`.
The kernel's C++ normalizer unfolds Lean expression bodies and reduces
recursors; it does not substitute the result of our generated C function.
Thus the compiled walk and logical certificate check perform related work
through different evaluators.

There is another boundary before the C walk: `Meta.evalExpr` instantiates
metavariables, infers/checks types, creates and compiles a temporary declaration,
then evaluates it and its arguments. The earlier 15–40 ms measurement covered
that entire envelope, not just the native walk or just wrapper compilation.

## Measurements

[Raw evidence](benchmarks/generated-c-2026-11-02.json) contains both builds,
source hashes, all C events, per-case results and the profiler summary. Each
build runs three rounds of the six identical Solidity fixtures. Every case
uses a fresh contract namespace to prevent auxiliary-lemma cache reuse. The
walk has a fixed bound of 128 steps. The table reports the **O0** build.
Values are milliseconds, using medians
of rounds 1–2; the small sample is not a throughput guarantee.

| Program | Native C walk | Auxiliary certificate creation/check |
|---|---:|---:|
| constant | 0.55 | 122.22 |
| identity | 0.86 | 183.95 |
| assignment | 1.13 | 240.92 |
| increment | 1.89 | 613.19 |
| branch | 8.44 | 996.96 |
| false constant | 1.98 | 214.77 |

These are **residue certificates**, not complete source-specification proofs.
Branch and false-constant residues still have an open leaf. The native walk
alone cannot be compared with a full SolKey proof as evidence of parity.

The C timers forward the original arguments and result unchanged, and stop
before printing. Each main run records exactly 18 walk events and 18 auxiliary
checker events. All 36 residue certificates pass kernel checking and the
standard-axiom audit. No heartbeat limit, kernel check or axiom policy is
weakened.

`C_AUX` includes auxiliary-cache lookup, naming and environment bookkeeping as
well as checking. A separate threshold-zero profile of increment and branch
confirms that checking dominates: the two largest kernel blocks are 824.91 and
1279.23 ms, while their enclosing C auxiliary calls take 825.28 and 1279.65 ms.
The aggregate kernel scope also includes temporary declarations, so aggregate
kernel time is not an exact measurement of auxiliary checking alone. Profiling
adds overhead; its absolute times are separate from the table.

## Optimization control and implications

The earlier native diagnostic was compiled with `-O0`. This experiment also
uses `-O2` for the two instrumented translation units, `ProvesDerive` and
`TacticSyntax`; the other 310 units remain at `-O0`. That limited change shows
no consistent improvement and does not remove the certificate bottleneck. It
is not a fully optimized end-to-end build.

The evidence supports changing the certificate strategy before blaming the
speed of generated C. A useful next experiment is a compact typed rule
certificate whose checker validates the selected steps, rather than replaying
the complete symbolic walk and leaf decisions through definitional reduction.
The individual-rule route measured previously was not yet faster, so merely
changing tactics or writing `⊢` is insufficient. Trusting an unchecked C result
would change the trust contract and is not this optimization.

## Reproduction

Build `Solidity.Frontend.Testing`, then generate the standard inputs with
`scripts/measure-simple.mjs`. The diagnostic command is in
`tests/automation/DerivationCertificate.lean`. The raw report retains the exact
runner, with one fresh namespace per source/repetition.

`scripts/profile-generated-c.py LEAN_PREFIX OUTPUT` builds a diagnostic plugin
with C timers around `Seq.residueQuoteWithin___redArg` and
`Derive.kernelLemma`. `BENCH_HOT_OPT=-O0` or `-O2` selects the two hot units;
`BENCH_C_OPT` controls the remaining units, defaulting to `-O0`. The plugin and
build metadata are written under OUTPUT. It uses the existing Lean monotonic
clock and preserves the original generated files. Run the retained runner
with `-j1 --tstack=131072 -DElab.async=false --plugin=OUTPUT/libSolidity_Frontend_Testing.so`
under the repository's memory guards.

The helper passed per-file MCP diagnostics. Read-only finder and skeptic
reviews checked wrapper forwarding, event counts, cache isolation and timing
scope. They correctly distinguished the complete `evalExpr` envelope from C
execution, and auxiliary checking from its surrounding bookkeeping. The
kernel profile resolves the latter attribution for the two profiled cases.
