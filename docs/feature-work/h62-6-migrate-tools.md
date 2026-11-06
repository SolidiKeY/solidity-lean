# H62/H63 Tools migration overlay

Owner: `solidity-h62-6-20261106/migrate-tools`. Repository:
`/workspace/solidity-lean`. Assigned base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Branch:
`codex/solidity-h62-6-20261106/migrate-tools`.

This is an isolated migration overlay. Live producer ownership is retained.
No Tools originals, generated roots, module maps, trust pins or tracked
`lean-toolchain` have been edited. No pushes, merges, PRs or freeze announcements.

## Current checkpoint status

1. Census/backfill complete; clean old-toolchain directory measurement pending.
2. Official new archive provisioned and pinned; adaptation blocked by an external
   dependency. No original declarations have been adapted yet.
3. Full new directory build and matched clean comparison blocked. No timing
   regression percentage or `RUNTIME_GATE_PASS` is claimed.
4. Reviewable tooling/fixture checkpoint committed; final migration handoff pending.

## Reproduction and frozen boundary

Run from the repository root:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-tools/census.py --output /workspace/migrate-tools-evidence/census-base.json
PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-tools/test_tooling.py
python3 scripts/h62/item6/migrate-tools/serial-build.py --root /workspace/solidity-lean --toolchain /workspace/migrate-tools-evidence/toolchains/lean-4.24.0-linux --output /workspace/migrate-tools-evidence/old-clean-2
```

The scanner finds 30 assigned modules, 581 declaration candidates and 52 distinct
external direct imports. It masks nested comments, strings, character literals
and escaped newlines. These are source candidates, not an elaborated API census.
Whole-file SHA256 hashes conservatively freeze all bytes, including declarations,
proofs, cases, namespaces, syntax and budget options missed by lexical analysis.
All originals will be compared against the pinned Git base in the final manifest.
Source trust-token totals are zero for `sorry`, `axiom` and `native_decide`; this
is a lexical observation, not a transitive axiom audit.

The serial runner produces fresh isolated `.olean` artifacts for the complete
407-module dependency plan (including KeySort first). It does not restore caches
or use the old `.lake` directory. This is a clean import-closure experiment,
not the repository `./run-lean.sh` acceptance gate or native-C build timing.
It runs exactly one Lean process with `LEAN_NUM_THREADS=1`, `-j1` and
`--tstack=131072`; each process has a 12 GiB hard address-space bound. A 0.2 s
monitor enforces a sampled 12 GiB process-group RSS threshold and a conservative
4 GiB host/cgroup available-memory reserve. The VM cap is 16 GiB; no swap device
is present and observed cgroup swap use is zero. No `systemd-run` is used.
The cgroup reserve includes reclaimable file cache, so a resource stop is not a
performance regression. Timing includes guard overhead equally for both versions.

## Toolchain identity

Coordinator inputs under `/workspace/h62-coordinator-inputs/` passed all five
hashes in `sha256.json`.

| Toolchain | Release archive SHA256 | Actual versions |
|---|---|---|
| v4.24.0 | `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec` | Lean 4.24.0 / `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613 |
| official pinned v4.35.0 | `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` | Lean 4.35.0 / `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb |

Archives and unpacked toolchains remain off Git under
`/workspace/migrate-tools-evidence/toolchains/`. The new SHA256 equals the
coordinator's `toolchain-pin.json`. Tools are invoked by absolute path; the
tracked toolchain remains v4.24.0.

## Typed dependency request: DEP-SYNTAX-RAW-435

Source: checkpoint 2, owner migration lane for Syntax via migrate-root-gate.
Requested action: migrate only the owner-controlled String/Slice API uses in
`Solidity/Syntax/Raw.lean` at base c6f550e, preserving exact public types and
semantics; supply reviewed patch plus frozen-interface/build evidence. This lane
requests no ownership transfer and has made no edit to that file. No relay.sh
exists in this checkout; the coordinator retrieves this saved request.

Exact reproduction: use the serial runner above with toolchain changed to
`lean-4.35.0-linux` and a fresh output directory. The first clean new probe exits 1
at Syntax.Raw after KeySort, AST and SpecSyntax pass. Errors are at lines 597,
650, 665, 682 and 684: `String.drop` now yields `String.Slice`; `.toList`,
`.dropRight` on String and first-class `.endsWith` application differ. Full
messages: `/workspace/migrate-tools-evidence/new-clean-1/Solidity.Syntax.Raw.log`.
All 30 Tools modules transitively depend on this file. No Tools declaration has
been checked by the new directory probe. Partial prefix time 11.686 s and sampled
peak RSS 1,539,657,728 bytes are failed-probe measurements, not build timings.

## Isolated backfill and proof boundary

`ApiFixtures.lean` checks expression construction, instantiation, evaluation,
command diagnostics and rejection of an ill-typed application. The sole
`bounded_val` theorem is checked by `rfl`; unsafe evaluation is observable
metaprogram execution, not a theorem-proof shortcut.

`StringReference.lean` retains the old String operations found in
Tools/LatexTerm and Tools/LatexSolkey; `StringFixtures.lean` supplies isolated
new Slice materialization candidates. Eleven matched cases cover ASCII,
Unicode, empty values, malformed wrappers and alternative labels. Reference
passes on v4.24.0; candidates pass on v4.35.0. These are examples, not universal
equivalence proofs or a certification of original functions. Both versions pass
KeySort and the common API fixture. Final fixture logs/results are
`fixtures-old-2/` and `fixtures-new-3/` under the evidence directory.
Earlier exploratory fixture failures remain saved and are not passing gates.

Five Python controls pass: nested-comment/string/character masking, continued
string line accounting across all actual Tools files, same-line attributes,
current assigned census/missed commands, and interruption of a real fake-runtime
child followed by termination/reaping. SIGTERM handling is reviewed statically;
that regression specifically injects KeyboardInterrupt. No Lean server is used
by those tests.

## Independent read-only reviews

Finder and skeptic were separate agents, neither using Lean or a Lean server.
They found four missed attributed declarations (577 -> 581), quote-character
masking, escaped-newline line drift, and missing exception/SIGTERM cleanup with
an exit/signaling race. Findings were fixed and controls added. Both final
reviews found no further blocking issue in tooling/backfill. They explicitly
reject treating fixture success as Tools migration completion. Full checkpoint
review remains necessary after the owner dependency arrives and final gates run.

## Remaining obligations

Complete old clean measurement; obtain the owner migration dependency; coordinate
exact-file Tools edits before adapting originals; prove/check all original
statements without budget increases; run full affected acceptance and repository
final gate; perform matched clean old/new timing and RSS comparison under equal
settings; escalate any regression and STOP above 10%; finish declaration/API and
axiom audits; obtain independent milestone reviews; export final patch/bundle,
frozen-interface hashes, cross-directory report and valid CLOUDVM-RESULT.
No replacement goal or continuation is created by this lane.
