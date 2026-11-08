# Test vectors as theorems

## Verdict

**Go for source compression; no-go for proof-size reduction with this pilot.**
A literal table expanded by a small Lean command macro saves **1,441/1,963
physical lines (73.4%) and 208,759/394,147 UTF-8 bytes (53.0%)** across two real
files, including both copies of the macro. All **1,947 existing theorem names
and literal statements survive**, with identical elaborated axiom dependencies.
There is no new mathematical abstraction: the macro emits the original
`decide +kernel` proof for each vector. Native constants and compiled size
increase. This does not establish the parent study's estimated 30k → 1k saving.
Only this document, the [reproducer](size-tools/test-vectors/measure.py), the
[pilot patch](size-tools/test-vectors/pilot.patch), and the parent link are
proposed for integration; the patch's `Solidity/` changes stay in scratch trees.

## Boundary and inventory

All new counts pin **772806909ec30c93a85a95c01130a70b6bcc83ca**.
Reuse the [direction audit](direction.md), [parent study](size-reduction.md),
[declaration graph](direction-tools/declgraph/summary.json) and
[statement/provenance summary](direction-tools/statements/summary.json).
The graph's older `d6fd95f08` result (zero Yul declarations reached from the 21
facade roots) is not a deletion proof. No reachability audit is repeated here.

`measure.py --static --inventory` scans every tracked Lean blob at the frozen
base, including Bridge and vendor files. Its raw lexical `:= by decide` search
allows whitespace and optional `+kernel`; it does not strip comments, prove
finiteness or limit matches to theorem bodies. Whole-file lines in the following
table are candidate footprints, **not savings**, and categories overlap.

| Family | Files containing direct decide sites | Whole-file lines | Direct decide sites |
|---|---:|---:|---:|
| Yul | 411 | 48,937 | 8,791 |
| Backend | 461 | 89,927 | 1,808 |
| Lowering | 147 | 23,909 | 489 |
| SolcValidation | 9 | 1,220 | 20 |
| Corpus (direct decide only) | 1 | 140 | 1 |

The full scan finds **14,437** direct sites repository-wide. It also separately
finds **1,762 `*Controls.lean` files**, 245,104 lines, 16,898 lexical theorem/lemma
headers and 2,733 direct sites, including optional Bridge families. Controls
include semantic transports, refusal cases and open-state theorems; treating
them all as finite vectors would be wrong. Corpus has **4,204 lines / 592 theorem
headers**: 70 `corpus_decide` sites (68 in generated example modules, two in
Basic), plus 518 TestSuite wrappers already using generic transfer lemmas.
The direct-decide search alone misses this family. See
[Corpus expressions](../../Solidity/Corpus/SolcExpressions.lean),
[Corpus transfers](../../Solidity/Corpus/Imported.lean),
[Backend controls](../../Solidity/Backend/WorldCalls/SelfControls.lean) and
[SolcValidation](../../Solidity/SolcValidation/DataLayout.lean).

The tightly identifiable Yul vector corpus has **6,903 named `vNNNN` theorems /
6,975 lines in nine files**: Arithmetic 2,008, Shifts 3,885, Bytes 947, Powers 63
theorems. **5,599** match the pilot's binary-input template. Unary and ternary
vectors remain outside that template; none is discarded.

## Ranked ideas

Rank considers measured saving relative to implementation effort; only rank 1
has a measured pilot. Other savings are explicitly uncredited, not zero-cost
promises. Every option must preserve the old named types, including negative
controls and every premise, rather than merely preserve headline coverage.

| Rank / idea and mechanism | Target / effort | Measured saving | Extrapolation | Strength risk / verdict |
|---|---|---|---|---|
| 1. Literal tables + kernel-checked macro expansion, sharing opcode and first input per row | Binary Yul vectors; small parser/converter, two files piloted | 1,441 lines; 208,759 bytes; **0 theorem constants removed** | 4,555 lines across the seven matching files; no checking-time or byte saving extrapolated | Literal outputs retained; **go for source only**, no-go for proof/artifact reduction |
| 2. Universal theorem per operation, with named vector specializations | `Solidity/Yul/Words.lean`, Arithmetic/Shifts; modest for definitional operations, harder for EXP/signed semantics | Not piloted; 0 savings credited | Existing one-line wrappers still need expected-answer data; no automatic line saving | A universal formula can be stronger, but does not discharge independent expected outputs by itself; **no-go as a standalone size replacement** |
| 3. One data list + one `decide`, deriving every old theorem by soundness/projection | Yul vectors, finite Backend/SolcValidation checks; medium | Not piloted; 0 credited | Could share proof work; wrappers and data remain; no numerical forecast | Long list reduction and repeated projections can exceed existing budgets; **no-go for rollout before a bounded-memory pilot** |
| 4. Description type + generic induction lemmas; parameters for pipeline variants | Controls in Yul/Views, Backend and Lowering; large | Not piloted; 0 credited | Controls footprint above is a search space, not a deletion budget | Preserve frame, dirty-bit, allocation and refusal premises for each instance; **no-go for blanket conversion**, pilot separately with the views lane |
| 5. Reuse existing Theory/model lemmas or exact theorem aliases | Corpus, Backend controls, SolcValidation; per-family review | No pilot; direct vector proofs already occupy one physical line | 0 line saving credited for tactic-only substitution | Corpus already reuses transfer lemmas; Theory domains may differ; **no-go as the main size strategy** |
| 6. Verified translation validator + certificates | Backend, Lowering and Yul compilation checks; large, existing H258 lanes | Not piloted here; 0 credited | No independent savings added to those lanes' claims | Need soundness and the original statement's completeness/acceptance boundary; **no-go for replacing vectors without those proofs** |
| 7. Delete apparently unused vectors | All families; rebuild alone is insufficient | 0 | 0 under this assignment | Would lose existing theorem names even when no facade uses them; **no-go** |

A universal add theorem can expose `word`'s modulo arithmetic by reduction,
while `powWord_correct` already states an unbounded EXP formula. These are model
facts, not new evidence of agreement with deployed EVM or an independent oracle.
No duplicated arithmetic framework is justified merely to restate `Pure.eval`.

## Measured pilot

The patch converts 960 binary vectors in
[Arithmetic Part00](../../Solidity/Yul/Checks/Arithmetic/Part00.lean) and 691 in
[Bytes](../../Solidity/Yul/Checks/Bytes.lean). All 296 remaining unary theorems
stay verbatim. Each table row shares the opcode and first input, with at most
16 `(name, second input, literal expected output)` entries. This layout accounts
for part of the line saving; the independent **53.0% byte reduction** establishes
that it is more than newline removal. No data/proof sidecar is omitted from the
source denominator. The 505,280-byte patch is below 1 MB.

| Metric | Arithmetic before → after | Bytes before → after |
|---|---:|---:|
| Physical lines | 1,008 → 178 | 955 → 344 |
| UTF-8 bytes | 230,716 → 95,208 | 163,431 → 90,180 |
| Named vector theorems | 1,000 → 1,000 | 947 → 947 |
| Native constants under original namespace | 2,000 → 2,005 | 1,894 → 1,899 |
| `.olean` bytes | 1,499,120 → 1,843,152 | 1,361,896 → 1,710,984 |
| Serial elaboration seconds, median of two | 17.034 → 17.340 | 12.465 → 13.026 |
| Largest child-process peak RSS, KiB | 1,560,608 → 1,937,428 | 789,600 → 1,167,252 |

The namespace count includes per-theorem decision helpers and five extra macro
implementation/parser constants per file. It is an elaborated count, distinct
from lexical theorem headers. Compiled artifacts grow **24.2% combined**.
Runtime changes (+1.8% / +4.5%) do not establish a speedup: Bytes after samples
were 14.655 and 11.398 seconds, so two samples are especially noisy. Arithmetic
before samples were 16.976/17.092, after 16.967/17.713; Bytes before were
12.362/12.567. Peak process RSS grows 24.1% / 47.8%; it is not summed VM/cgroup
memory. `resource.getrusage(RUSAGE_CHILDREN).ru_maxrss` is measured in a fresh
Python wrapper for each invocation because GNU time is absent.

Lean is **4.24.0**, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake **5.0.0-src+797c613**. Warm imports, identical base/toolchain and resource
flags, two actual elaborations per variant, no cached target-result timing.
The cache was fetched first (pack `ffa76e1c0b`); Words and KeySort imports were
then fetched/built and restored before timing. The VM has about 17 GiB RAM,
no swap; Lean uses `LEAN_NUM_THREADS=1 -j1 -M12288 --tstack=131072`.
No systemd scope on the cloud VM (H232). The 12 GiB Lean allocation setting is
not a systemd resident-memory cap; host integration still applies its own gate.

The reproducer reconstructs and compares **every literal old statement**, then
compiles each variant, imports it, checks all 1,947 old types against the named
constants, prints their axiom lists and requires before/after lists to match.
All list exactly `[propext]`; zero new axioms, admissions, native decisions or
heartbeat increases. These are kernel proofs of finite model outcomes, not
external oracle provenance, solc execution or production EVM conformance tests.
No semantics changed, so the historical mutation score is neither rerun nor
claimed for this documentation-only lane.

## Execution proposal and reproduction

1. Start with Arithmetic Part00 and Bytes, retaining the exact types checked by
   the pilot. Warn about the observed RSS/artifact increase before production
   rollout; existing file history contains generated-control fixes, not a
   speed-motivated consolidation this patch would undo.
2. Extend only the same binary template to Shifts and Powers. For each file
   require the original named equality with the same operands and expected
   numeral, identical axiom lists, per-file diagnostics and serial timings.
   Seven matching files predict `5,599 - 974 rows - 7 × 10 overhead = 4,555`
   fewer lines: **6,975 → 2,420 (65.3%)** for the entire nine-file vector corpus.
   This is a source-layout extrapolation, **not an elaborated rollout**; no
   saving is assigned to the two nonmatching Arithmetic files or other areas.
3. Pilot unary/ternary syntax separately. Consider a universal semantic lemma
   only when it supplies reusable mathematics, retaining each finite oracle
   check. Test aggregate-list proofs separately before changing proof budgets.
4. For Corpus, preserve each `Diamond`/box statement and initialization premise;
   for Controls, preserve the complete open-state/refusal theorem. Require a
   second measured pilot before extending rank 1's saving to either. Register
   any eventual new modules through repository tools, never by hand-editing
   generated roots. A production Lean rollout needs its library/full gates;
   this study integrates no Lean source changes.

From the lane checkout with the pinned Lean/Lake binaries on PATH:

```sh
T=docs/audits/size-tools/test-vectors
python3 "$T/measure.py" --static --inventory
# Supply a NEW external scratch path and an external output directory.
# A configured LAKE_CACHE_DIR also avoids requiring elan for artifact restoration.
LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=/path/to/lake/cache \
  python3 "$T/measure.py" --worktree /path/to/new-scratch --out /path/to/output
# --cache-ready skips the fetch only when a successful fetch is already recorded.
python3 "$T/measure.py" --audit-results /path/to/output
python3 scripts/check-doc-navigation.py
scripts/check-doc-paths.sh
```

The runner obtains the repository writer lock, refuses an existing scratch tree,
and keeps logs, timing samples, type/axiom checks and inventory outside Git.
Absolute timings and RSS vary by machine; source counts and preserved types
must reproduce exactly. After applying the patch, the repository's per-file
`lean-mcp diag` bridge provides the complementary editor diagnostics; neither
independent review needs a Lean server.
