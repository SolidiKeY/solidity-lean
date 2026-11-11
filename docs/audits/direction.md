# Direction audit

## Verdict

The project has a sound core direction, but its expansion is ahead of its demonstrated compiler coverage. The calculus and intrinsic semantics justify substantial proof code; source volume alone does not show waste. Backend, Yul and lowering should now prioritize composition into a usable compiler endpoint over more certificate transports and scenario-specific layers. The duplication inventory identifies a concrete consolidation search space, not a proved deletion budget.

## Measurement boundary and headline facts

This audit measures the launch base `dfdfa238b5bf63955048999fefd291d9d55dbd56`.
The input lanes describe the older frozen `d4ad633a9624263a59b14fd2c520b9bc602f88f3`:
37 Lean paths changed between them; the exact paths are in [README-results.json](direction-tools/README-results.json).
Area counts below are remeasured at launch; older duplication, dependency and statement findings retain their own base. No fresh Lean check or full build was run.

Physical lines include comments and blanks. “Unmarked” means total minus detected generated lines, **not proven handwritten**. Roots, Corpus, AxiomPins and marked generator output are separated by the committed counters; chain/agreement filenames alone do not prove generation. The statement lane additionally separates unresolved chain/agreement files from untraced source. Reference counts use the existing reference scanner, with `.sol` fixtures and `.vp` templates included by the new wrapper. Declaration/theorem columns are lexical estimates: local comments/strings are stripped, reference header matching is raw; these are neither native declaration counts nor comparable proof effort. Zero theorem headers in Java, K or Solidity does not mean absence of verification.

- **Scale confirmed:** 1,310,403 tracked Lean lines in 8,287 files, of which 1,122,634 are under `Solidity/`. Detected generated lines: 31,793 (2.43%); 97.57% remain outside that marker classification. The claim 'about 95% not marked generated' is approximate and classifier-dependent; '95% handwritten' is unsupported.
- **The CompCert multiplier needs its denominator:** 9.99× the 131,126 project Coq lines in the existing representative-target [calibration](direction-tools/reachability/calibration.json), versus 5.22× the whole tracked source inventory below. This repository includes tests, optional bridges and vendored code; neither multiplier measures compiler-proof efficiency.
- **Import-unreachable directories refuted:** `Solidity.lean` directly imports the named families: Backend/InternalFlow 300, Frontend/SolcJson 55, SolcValidation 30, Yul/Views 882. These count direct root imports, not declaration uses.
  The older reachability lane instead reports *declaration source spans* without a lexical/implicit reference path: Yul/Views 10,146; Backend/InternalFlow 6,100; SolcValidation 4,878; Frontend/SolcJson 4,440. These are partial directory spans, not module import failures or safe deletion totals. Its CI import closure includes 6,722 modules / 1,124,917 physical lines.
- **Duplication confirmed at the input base:** 2,743 same-statement clusters, 57 exact canonical file groups, and 88 near-file clusters covering 26,599 physical lines. Canonicalization and transitive clustering can merge semantically different cases; the latter figure is the candidate footprint, not the saving.
- **Growth confirmed, lack of goal accounting confirmed:** census history records Backend 0 → 279,224 and Yul 0 → 197,432 lines. Goals moved is `null`, not zero: the frozen inventory has no goal attributes or goals registry. Do not infer that no useful theorem was proved.

## Reference portfolio

The links pin the measured sources. This is a portfolio scale table; the area table supplies subsystem comparisons. All reference source was fetched shallowly and counted, not compiled. `P/D` is the scanner's proof-region/definition-region estimate; the local scanner uses nonblank command spans, while reference regions retain blanks/comments. Do not compare those ratios as proof productivity. Generated shares are marker lower bounds, not historical authorship measurements.

| Source and scope | Lines | Generated % | Declarations / theorem headers | P/D estimate | Trust and guarantee boundary |
|---|---:|---:|---:|---:|---|
| This repository, all tracked Lean | 1,310,403 | 2.43 | 130,694 / 75,083 | 2.51 | Lean kernel; core intrinsic model; optional external/native execution has a separate trust boundary |
| [CompCert](https://github.com/AbsInt/CompCert/tree/2685140bf72c959446981fb99b5e44a8975021bc) | 251,215 | 0.94 | 12,492 / 7,144 | 1.81 | Coq proofs of C-to-assembly semantic preservation; extraction and external assembler/linker boundary |
| [CakeML](https://github.com/CakeML/cakeml/tree/b3e6ea34ca1aed91a57703a30549260ce6f6448e) | 937,974 | 0.34 | 44,983 / 28,188 | 3.00 | HOL4 compiler correctness and verified backend; HOL4, runtime/FFI and configuration assumptions |
| [EvmYul](https://github.com/NethermindEth/EVMYulLean/tree/047f63070309f436b66c61e276ab3b6d1169265a) | 11,602 | 0.00 | 1,113 / 39 | 0.02 | Lean EVM/Yul executable model; conformance tests supply external evidence, not compiler correctness |
| [Clear](https://github.com/NethermindEth/Clear/tree/6ef2e7eda01080e5d5fd7474354c1a71adab5071) | 9,615 | 10.77 | 675 / 367 | 0.68 | Lean Yul verification toolkit plus external Haskell VC generator; generated obligations remain obligations |
| [KEVM](https://github.com/runtimeverification/evm-semantics/tree/fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1) | 58,753 | 0.00 | 5,431 / 0 | 0.00 | K EVM semantics and reachability tooling; K/backend and external conformance boundary |
| [Isabelle-Solidity](https://github.com/isabelle-prover/mirror-afp-devel/tree/f81741033ad5e782a0e0aba461b292ea1c860b3d) | 19,238 | 0.00 | 1,259 / 716 | 3.52 | AFP Solidity theories only; Isabelle/HOL proofs of the modeled language |
| [SolKey](https://github.com/SolidiKeY/solkey/tree/5c448df67f6fab14c5f9c1c5d0c63249b5fe78b8) | 806,966 | 1.07 | 2,879 / 0 | 0.00 | Whole KeY-derived platform plus Solidity extension; Java implementation and taclet rule trust |
| [solc](https://github.com/ethereum/solidity/tree/403c39f86c3c0c9d4779b97892a3661016b45455) | 367,461 | 0.01 | 14,643 / 0 | 0.00 | Production Solidity compiler and tests; implementation/testing, not a compiler-correctness proof |

Local source scans find one `axiom` declaration across the repository, zero `sorry` tokens and zero `native_decide` tokens; that is a source inventory, not an elaborated axiom audit. The core theorem facade retains fragment, simulation and capacity premises. Its axiom pins distinguish ordinary Lean axioms from executable overrides. Recovery `.admit` API calls and the optional vendored `trust_smt` in `Bridge/vendor/Loom/SMT.lean` require separate scrutiny; zero `sorry` tokens is not a hole-free assurance and recovery calls alone do not establish admitted public theorems. External conformance, solc agreement, differential tests and mutation tests do not prove the model matches deployed EVM behavior.

## Ten largest areas

Rank by unmarked physical lines, adding the optional `Bridge/SolidityBridge/` area to the `Solidity/` areas (other bridge libraries and fixtures stay in the repository total). `L/G/D/T` means physical lines / detected generated lines / lexical declarations / theorem-or-lemma headers. Ratios use unmarked lines on both sides. Verdicts concern engineering direction; a size outlier alone is not evidence of redundancy. Subsystem selections overlap and must not be summed. Each row compares complete selected subsystems, never an individual local leaf against a large reference file.

| Local area: L / G / D / T | Whole reference subsystem: L / G / D / T; ratio | Verdict and missing/extra obligations |
|---|---|---|
| Backend: 279,224 / 2,451 / 28,662 / 15,750 | `backend-x86`: 67,414 / 794 / 3,674 / 1,951; 4.15× | **wrong-direction**: prioritize a composed source/world or byte-level compiler endpoint over further runtime-frame/certificate transports in `Solidity/Backend/InternalFlow/`. CompCert proves an actual optimizing pipeline; `Solidity/Backend/Passes/CompilerWholeScope.lean` already proves intrinsic-program acceptance/adequacy, expressly not SourceSpec/world adequacy. Preserve that result while connecting the broader endpoint. CakeML backend is a second, larger compiler-proof counterpart, so size alone is not the objection. |
| Yul: 197,439 / 6,975 / 28,242 / 19,185 | `yul`: 3,178 / 0 / 278 / 18; 59.93× | **wrong-direction**: make the producers construct `Solidity/Yul/Compilation/Artifact.lean` evidence for a defined accepted language before expanding `Solidity/Yul/Views/`. EvmYul supplies Yul execution semantics; local code additionally proves transports and partial compilation. The Artifact fields require forward/backward evidence and do not themselves prove every statement compiles. |
| Calculus: 169,330 / 1,550 / 11,745 / 6,280 | `calculus`: 42,645 / 272 / 1 / 0; 3.96× | **justified**: KeY/SolKey rule resources are the calculus counterpart; Lean adds intrinsic typing, rule soundness and decision procedures in `Solidity/Calculus/`. The reference rule catalog is not a kernel-checked soundness development, so the excess is not a like-for-like proof-effort penalty. |
| Lowering: 103,527 / 58 / 11,743 / 5,836 | `lowering`: 5,305 / 0 / 262 / 149; 19.50× | **wrong-direction**: prioritize reusable, composed source-to-intrinsic pass invariants in `Solidity/Lowering/` over scenario-indexed G families. Cshmgen/Cminorgen include implementations and their complete correctness proofs; local scope also includes Solidity-specific memory/type obligations. The full C frontend sensitivity below prevents mistaking those two passes for a complete Solidity compiler. |
| Frontend: 102,235 / 4,360 / 7,963 / 4,889 | `frontend`: 31,123 / 0 / 1,449 / 688; 3.14× | **justified**: `Solidity/Frontend/` includes intrinsic acceptance/typing agreement and solc JSON handling in addition to parsing. CompCert cfrontend proves C frontend transformations, which this area does not replace; local Solidity layout and qualified-name obligations are extra. Treat the outlier as an explicit scope cost. |
| Bridge: 64,746 / 0 / 6,005 / 3,575 | `bridge`: 9,615 / 1,036 / 675 / 367; 7.55× | **inconclusive**: `Bridge/SolidityBridge/` contains external-model agreement/adapters, whereas Clear is a Yul verification toolkit and generator. The ratio is a portfolio proxy, not an adapter-proof calibration. Settle with a count of the transitive declaration slice proving the same EVM state relation in both frameworks. |
| Examples: 61,471 / 0 / 6,150 / 3,375 | `examples`: 44,038 / 9 / 4,447 / 0; 1.40× | **justified** (within the size band): `Solidity/Examples/` contains kernel-checked finite examples and controls; solc semanticTests executes production compiler cases. Neither establishes universal language coverage; the reference exercises a real compiler/toolchain, while local examples can prove exact modeled outcomes. |
| Source: 50,041 / 620 / 5,484 / 3,172 | `source`: 31,481 / 0 / 251 / 0; 1.57× | **justified** (within the size band): `Solidity/Source/` includes Solidity types and semantic properties; solc AST/analysis implements production type analysis without theorem counterparts. Local proofs add guarantees about the model; reference implementation covers production language acceptance. |
| Evm: 45,857 / 0 / 4,396 / 2,395 | `evm`: 2,703 / 0 / 155 / 0; 16.97× | **justified**: `Solidity/Evm/` includes compilation, simulation and correctness in addition to machine execution. EvmYul EVM models execution and gas but supplies no compiler-correctness counterpart in this slice. Local compiler proofs do not establish full Ethereum fork/gas/precompile conformance. |
| Semantics: 25,790 / 0 / 2,250 / 1,313 | `semantics`: 22,851 / 0 / 1,490 / 969; 1.13× | **justified** (within the size band): `Solidity/Semantics/` is the intrinsic runtime model; CompCert common supplies values, memory, events and simulations. C pointers/events and Solidity storage/callback behavior differ; neither proves the other language semantics. This is a whole runtime-infrastructure scale check. |

Sensitivity: Backend / multi-target CompCert backend = 2.30×; Backend / complete CakeML `compiler/backend/` = 0.81×. Lowering / complete CompCert `cfrontend/` = 3.32×. Ratios crossing the outlier threshold under a different subsystem boundary cannot justify a deletion verdict. Reference paths, pins and both generated/unmarked components are in the result JSON.

## Top ten corrections

These are proposed follow-up work, not authorization to alter proofs or delete modules. A gain names a reviewable endpoint or measurement. No Lean reduction has been proved safe in this read-only audit.

1. **Compose Backend acceptance to execution.** Reorient the 279,224-line `Solidity/Backend/` portfolio around the checked compiler entry and `Backend/Passes/`; gain: a named source/world or byte-level endpoint with explicit refusal cases beyond the existing `CompilerWholeScope.lean` intrinsic-program theorem. Guaranteed deletion: zero.
2. **Make Yul certificates produced evidence.** For the 197,439-line `Solidity/Yul/` area, connect `Yul/Compilation/Artifact.lean` constructors to producers before adding Views transports; gain: measured accepted syntax and composed forward/backward preservation. Guaranteed deletion: zero.
3. **Consolidate lowering by pass invariant.** `Solidity/Lowering/` is 103,527 lines versus 5,305 for complete Cshmgen/Cminorgen implementation/proof subsystems. Merge repeated G-family transport scaffolding only after checking statement equivalence; gain: a single reusable interface per transformation, with existing refusals preserved. No numerical saving is yet established.
4. **Review near-file candidates before adding parallel variants.** The 88 clusters cover 26,599 lines. Use `reachability/reach.py` to locate pairs; merge common lemmas at their existing area paths after checking hypotheses and consumers. Candidate-footprint ceiling: 26,599 lines; actual saving unknown, never the whole footprint.
5. **Canonicalize same-statement reuse.** Review the 2,743 declaration clusters across `Solidity/Backend/`, `Solidity/Yul/` and other reported paths, redirecting equivalent consumers to shared lemmas. Gain: one canonical declaration per genuinely equivalent case; cluster count is not a removable declaration count.
6. **Account for orphan candidate spans.** Start with the 10,146 Yul/Views and 6,100 Backend/InternalFlow source-span lines above. Give every retained family a theorem/test owner or establish unused elaborated dependencies before removal. Gain: an explicit purpose for each candidate; build imports alone do not settle this.
7. **Close frontend validation intent.** Review 4,440 Frontend/SolcJson and 4,878 SolcValidation candidate-span lines. Connect retained validators to tests/entrypoints and document external execution assumptions; gain: exercised validation, not a claim of model correctness.
8. **Separate authorship from generation.** The statement provenance inventory has 157 unresolved chain/agreement files / 25,420 lines. Trace producers in the reported `Solidity/` and `Bridge/` paths before using LOC as handwritten effort; gain: auditable generation provenance. These frozen figures are not launch-base authorship totals.
9. **Track accepted-language progress.** The statement lane finds zero goal attributes; history cannot compute goals moved for the rapidly grown Backend/Yul portfolios. Add a user-approved endpoint/coverage metric rather than inferring progress from lines; gain: a monthly numerator tied to correctness statements.
10. **Keep regenerable detail out of Git.** Delete the 38 permitted split census/duplicate files, saving exactly 6,452,407 committed bytes from the 8,952,242-byte launch input. Keep every script and summary. The retained input floor is 2,499,835 bytes before this audit's small files; the lease does not permit deleting other data to reach a stricter cap. Regenerate on demand using the commands below.

## Making it smaller

Findings from the second audit round (`direction-tools/declgraph`, `endpoint`, `mutation-run`, base `d6fd95f08`) and the investigation that follows it. Numbers are declaration-graph or source-span counts, not verified deletions.

- **The proof core is nearly done; the size is in the compiler layers.** Endpoint (a) already derives 552 of 566 SolKey TestSuite obligations (97.5%) and claims 342 of 377 taclets (90.7%). Backend, Yul and Lowering (about 580k lines) serve endpoint (b), whose source-to-bytes chain is still open (`direction-tools/endpoint/summary.json`). Size should be judged against the endpoint chosen.
- **Large families no headline theorem uses.** No declaration of `Backend/InternalFlow/` (9,092), `Frontend/SolcJson/` (4,526) or `SolcValidation/` (4,090) is reached from the 21 facade theorems. Unreached spans: 11,081, 8,923 and 5,814 lines; another 12,772 InternalFlow lines are used only by their own policy checks. Deletion still needs a removal rebuild; until then these families must not grow.
- **The proofs constrain the semantics.** All 39 executed mutants (30 in Semantics) were killed. Shrinking must preserve that: re-run `direction-tools/mutation-run/run.py` after each consolidation.
- **Replace per-scenario proofs by proved checkers (translation validation).** Prove once that a checker is sound (and, for a universal theorem, complete on the accepted fragment); the per-program check runs in the kernel (`decide`, never `native_decide`). Accept a pass only if checker plus proofs are at least 3x smaller than the per-scenario proofs it replaces and the kernel check of a real contract stays within the gate budget. Pilots: `lowering-checker-p1` (lowerLoops) and batch `shrink-pilots-1108` (Yul, Backend, Lowering families).
- **Merge near-copies behind generic interfaces.** 88 near-file clusters (26,599 lines) and 2,743 same-statement clusters; plan steps `t1-yul-views-generic` and `t3-dedup-rollout`.
- **Stop drift.** New code in Backend, Yul or Lowering names the `@[goal]` it advances; a CI line budget per area ratchets down as consolidation lands.

## Re-run and monthly comparison

Use Python 3 standard library and Git; no Lean, Lake, new dependencies or full builds. The new calibration script/result use `README*` names because those are the only writable tool paths in this lane. Re-run in a disposable checkout: older producer scripts regenerate their frozen outputs and split shards in place. Set `T=docs/audits/direction-tools`, `CACHE` to an external directory, `OUT` to a scratch process directory, and `ARCHIVE` to the private coordination archive checkout when available. Do not run write-mode producers on a dirty working tree.

```sh
T=docs/audits/direction-tools
CACHE=/tmp/direction-reference-cache
OUT=/tmp/direction-process
ARCHIVE=/tmp/solidity-lean-coord
bash "$T/references/fetch.sh" "$CACHE"
python3 -B "$T/README-calibrate.py" "$CACHE" --check
python3 -B "$T/references/measure.py" "$CACHE"
python3 -B "$T/census/metrics.py"
python3 -B "$T/census/trend.py"
python3 -B "$T/census/check.py"
python3 -B "$T/reachability/calibrate.py" --reference "$CACHE/CompCert" --check
python3 -B "$T/reachability/reach.py"
python3 -B "$T/reachability/reach.py" --check
python3 -B "$T/reachability/test_reach.py"
python3 -I "$T/statements/scan.py" --check
python3 -I "$T/statements/provenance.py" --check
python3 -I "$T/statements/reuse.py" --check
python3 -I "$T/statements/calibrate.py" --check
python3 -I "$T/statements/similarity.py" --check
python3 -I "$T/statements/validate.py"
python3 -B "$T/process/history.py" --out "$OUT" --compcert "$CACHE/CompCert"
python3 -B "$T/process/reuse.py" --out "$OUT"
python3 -B "$T/process/closure.py" --archive-git "$ARCHIVE" --out "$OUT"
python3 -B "$T/process/verify.py" "$OUT"
python3 -B "$T/process/test_gap.py"
```

The two shard-regeneration commands are `census/metrics.py` and `reachability/reach.py`; the latter's check mode expects regenerated shards to exist. `census/check.py` also needs its regenerated shards. `process/closure.py` needs the pinned archive history, not a current build. Checks with `--check` validate committed frozen results; producers without it write outputs. For a monthly trend, run `census/metrics.py --rev <monthly-commit> --out <new-directory>` and `census/trend.py --rev <monthly-commit> --out <new-directory>`, retaining pins and categories. The verdict wrapper deliberately pins this launch base; a later audit must explicitly update its base and regenerate its small JSON before claiming a new measurement. Never silently relabel old timings or duplicate data as current.

## Limitations and user decisions

The mutation lane is absent under direction-tools at this base; no mutation score is asserted. Historical architecture timings and build-speed analysis are reused only as historical evidence; no matched reference check times, current build duration or transitive lemmas-per-theorem ratio is available. Differential and bench output directories are absent at the frozen input base. The process lane's matched overhead ratio remains inconclusive; source churn is not labor, and the missing archive/resource measurements do not block this direction recommendation. No systemd scope on the cloud VM (H232); no Lean elaboration was needed. The only area-level inconclusive verdict is Bridge, with its settling measurement stated above.

Only the user can choose the intended product endpoint: (a) a small intrinsic SolKey-compatible proof core, (b) a verified accepted-fragment compiler, or (c) production Solidity/EVM conformance. Each requires a different coverage denominator. A second choice is whether optional external bridges remain part of the main product's maintenance budget or get separately budgeted support. These choices do not authorize dropping existing premises, exclusions, proofs or tests.
