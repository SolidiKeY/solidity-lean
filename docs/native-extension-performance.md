# Generated C in the extension

Version 0.5.3 defaults to direct verifier results in the desktop extension and
offline website. This follows the requested trust model: run the verifier and
report correct, wrong (a concrete counterexample), or unknown. These results
trust the verifier implementation; they do not claim independent Lean-kernel
certification. The CLI default and API requests with `certify: true` retain the
certificate-producing path.

## Direct mode measurements

The generated-C direct checker runs symbolic execution and a bounded executable
leaf checker. It searches for a concrete falsifying prestate when it cannot
close the obligation. A pending result can use the existing symbolic/arithmetic
solver with temporary proof checking disabled; its saved state is restored and
no result theorem is retained. Unsupported recursive/callback readings stay
unknown. The fallback still constructs intermediate Lean expressions, so this
is not yet an entirely first-order C solver.

A condition initially invoked that fallback even for already-decided results:
Lean's lifted monadic expression in a Boolean condition ran before the Boolean
test. Explicit nested conditions removed that unnecessary work. The C checker
itself took about 1.4 ms for increment; the mistaken fallback added nearly one
second. The regression fixture checks eight true/false source specifications,
uncertified witness identity, absence of result theorem declarations and scoped
option restoration.

Current clean-library measurements use the same 18 source snapshots and an
active generated-C library, once with certification and once without. Warm
medians (rounds 1–2, two samples per case), milliseconds:

| Program | Certified | Direct |
|---|---:|---:|
| constant | 313 | 101 |
| identity | 402 | 91 |
| assignment | 365 | 94 |
| increment | 630 | 106 |
| branch | 998 | 820 |
| false constant | 252 | 98 |

These are worker request times with precompiled ASTs; compiler and GUI latency
are excluded. Packaging work overlapped part of the run, and the small sample
is not a stable throughput claim. A separate diagnostic run measured increment
at 94 ms end to end, 24 ms in the frontend direct helper and 1.43 ms inside the
C checker. The branch needs the slower semantic fallback. No 100× end-to-end
improvement or new comparison against SolKey is claimed. Cold startup still
loads Lean and its environment.

[Direct-mode evidence](benchmarks/direct-extension-2026-11-03.json) preserves
both clean runs and the instrumented phase run. The `direct-formula` and
`direct-classify` phases are cumulative from the same start; do not add them.
`direct-executable` is a separate interval including expression preparation,
compilation and C execution. `direct` covers the helper including any fallback.
The clean library has no diagnostic timers. Both libraries use `-O0`.

The website uses the same direct entry point through its existing WebAssembly
Lean runtime. It does not load the desktop native `.so`; desktop timings must
not be read as browser timings.

## Final validation of direct mode

The extension unit suite passed 96 tests (two environment-dependent cases
skipped). The real LSP suite passed all 12 checks with native activation required,
including direct true/false results and isolation from certified cache entries.
The browser protocol/server suites passed all 16 checks. Per-file Lean diagnostics
passed for both changed modules and the eight-case direct regression; the
frontend dependency target built successfully. The layer check reports 194 core
modules with no elaborator reachability. The VSIX executable sources match the
current source files.

The rebuilt single-file website passed all 14 Chromium checks without backend
connections, including cancellation, changed false specifications, uncertified
counterexample identity and fresh edited-source verification with the network
disabled. Peak aggregate browser RSS was 4.16 GiB. Its fresh four-function
browser check took 15.78 seconds; the disconnected fresh check took 14.44 seconds.
The 6 ms repeated request was a cache hit, not solver throughput. This leaves a
substantial browser startup/environment-loading cost; the desktop timings do
not demonstrate native-C speed in WebAssembly.

The new browser screenshot was inspected against the existing VS Code reference:
editor geometry, colors, testing tree and Problems layout remain similar. The
reference screenshot predates direct mode and therefore shows the older
proved/pending labels; the new browser shows correct/wrong. Its historical
status report is not used as an equivalent-mode verdict comparison.

## Historical certified-mode investigation

The following measurements predate the direct-default change. They isolate
loading generated C while retaining certification, which produced only modest
gains. They explain the redundant replay that direct mode now omits.

## What the C inspection found

The native walk is fast on the measured small state-writing programs. The
expensive boundary comes later, when Lean checks the generated certificate.
The generated `Solidity/Frontend/Testing.c` has this direct native call chain:

```text
SpecProposal.quoteResidue___redArg
  → Seq.run___redArg → Seq.runK___redArg
  → SpecProposal.quoteLeaf → SpecProposal.check
      → Fml.toLSM
      → LFml.boundsOk
      → SpecProposal.trim → LFml.dropPremM
      → LFml.decideLift
```

The leaf callback is a C function pointer. The full `quoteResidue` wrapper
omits the unused context argument when calling `___redArg`. Reference counting
and closure allocation are present; the measured time bounds their cost here.
No project-code interpreter handoff occurs inside this measured C walk.

The frontend separately calls `Lean.addDecl` for final proof validation. Its
certificate contains a reflexivity proof of a residue equality. Establishing
that equality requires reducing the logical Lean definitions, including leaf
lowering and decision checking. The C implementation uses compiled twins such
as `Fml.toLSM`; the kernel evaluates the logical definitions used by the proof.

The pinned kernel's `type_checker::unfold_definition_core` obtains a definition
body with `instantiate_value_lparams`. Its `reduce_recursor` invokes
`inductive_reduce_rec`, supplying normalization, inference and definitional-
equality callbacks. These routines operate on Lean expressions; they do not
call our generated C function to validate this equality. The kernel being
written in C++ does not make these expression reductions equivalent to direct
execution of the specialized, type-erased C walk.

## Timings at the actual LSP boundary

A diagnostic library marks execution of the C frontend command and times
`SpecProposal.quoteResidue___redArg`. The wrapper forwards all original arguments
and the original result. Its timer stops before printing to stderr. The frontend
marker was checked on all 18 requests; the compiled walk was also confirmed on
the assignment/increment requests. A separate phase run records exactly one C
walk timer for each of those six checks and the synchronous declaration-check
phase. Warm medians of rounds 1–2, milliseconds:

| Program | Generated-C walk | Declaration checking |
|---|---:|---:|
| assignment | 0.72 | 210.38 |
| increment | 1.66 | 481.68 |

The walk timer covers computation of the proposed residue. It is not a complete
checked proof. The declaration phase includes synchronous `addDecl` and its
small surrounding bookkeeping. The search phase also includes the native walk,
so the two must not be added as independent costs. The exact phase rows and C
excerpts are retained in [the evidence archive](benchmarks/native-extension-2026-11-03.json).

Optimizing only this walk can save less than 2 ms on these examples, even if it
were instantaneous. Avoiding the hundreds of milliseconds of replay needs a
cheaper checked proof certificate; loading the native library alone does not
change the certificate representation or the kernel's reduction algorithm.

## Complete worker checks

Four unprofiled runs use the order off/on/on/off. Each contains the same 18
source variants: three rounds of six programs, one Lean process and document
versions 1–18. Both modes use the same backend and retain final kernel and
standard-axiom checks. Every report verifies its source hash and expected status.
The on runs assert that native loading was active; off runs explicitly disable
it. The clean library has no diagnostic markers or timers.

These warm medians pool rounds 1–2 of both runs: four samples per program per
mode. Times include extension-worker IPC and real proof checking with pinned,
precompiled solc ASTs. Solidity compilation and GUI latency are excluded.

| Program | Native disabled | Native enabled |
|---|---:|---:|
| constant | 361 ms | 300 ms |
| identity | 442 ms | 409 ms |
| assignment | 382 ms | 363 ms |
| increment | 688 ms | 652 ms |
| branch | 1053 ms | 1012 ms |
| false constant | 282 ms | 231 ms |

State-write latency improved about 5% in this sample. Constant and false-constant
checks improved more; there is still sampling variability. Cold first checks
were 3143/2847 ms with native disabled and 2912/2735 ms enabled. These small
samples do not establish a startup improvement or a general throughput bound.
No new SolKey comparison was run.

Both timed native builds use `-O0` for all 312 project modules. A full `-O2`
build was started and stopped before completion; no fully optimized result is
claimed. The evidence for the bottleneck is the separation of sub-2-ms native
work from hundreds of milliseconds of declaration checking.

## Loading and rebuilding

Version 0.5.3 discovers a matching prebuilt library in `.lake/frontend-native`.
Build the current Lean frontend before compiling the optional library:

```sh
lake build Solidity.Frontend.Testing
python3 scripts/build-frontend-plugin.py "$(lake env lean --print-prefix)"
```

Loading checks platform, architecture, pinned toolchain, actual runtime commit,
module closure, source/C/serialized artifact identities and the library hash.
Unchanged files reuse hashes bound to device, inode, size and nanosecond
modification/change times; changed identities cause byte hashing. Cache
fingerprints cover all inspected artifact variants and the native manifest.

The builder serializes writes to its output directory. New compilations use
captured C snapshots; all backend inputs are rechecked before publication.
Libraries live in digest-named directories with the conventional module library
basename, which Lean needs to find its initializer. The manifest is published
atomically. Missing, stale or incompatible libraries use the ordinary backend.
A native process failure retries once without the library inside the original
monotonic request deadline. Healthy-process RPC errors and timeouts do not
permanently disable native execution.

`SOLIDITY_LEAN_NATIVE=0` selects the control mode.
`SOLIDITY_LEAN_NATIVE_DIR` selects a separate build directory. Backend metadata
reports native activation and the exact library hash. Native compilation is a
build step; it is not performed as part of a first proof check. This is a desktop
integration; the offline website cannot load the platform-specific `.so`.

## Validation

Native-selection tests cover stale inputs and library data, all serialized
variants, runtime mismatch, ordinary RPC errors/timeouts, process failure during
initialization/check, version reset and the original startup deadline. Builder
fault tests mutate C during compilation and a private artifact during linking;
publication is rejected and the previous library/manifest remain intact.

The earlier certified LSP regression passed all 11 checks with native activation explicitly
required. It covers in-memory edits, warm reuse, cancellation, restart and
certified counterexamples. The deliberately corrupted native-oracle control
still passes: the kernel rejects falseStore, semantic fallback leaves it pending,
and a subsequent true proof succeeds. That negative control applies to certified mode only. Direct mode deliberately
trusts the executable verifier instead. Final read-only finder and skeptic
reviews found no remaining verdict/state/cache blocker; their UI and measurement
clarifications were addressed.
