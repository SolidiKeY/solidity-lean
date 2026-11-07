# H28 G08 nonnumeric literal decoder completeness

Status: **done** (see "Claude VM completion"; the solc fixture rerun,
queue item 3, ran on 2026-11-06). The lane moved from a Codex VM to a Claude VM on 2026-11-05;
all 26 `Solidity/Frontend/LiteralGrammarH28/**` modules are registered in the
generated `Solidity.lean` root, so the former registration blocker
(Q-ROOT-01) and the cache-delivery question (Q-CACHE-01) are closed.

Exclusive writes: `Solidity/Frontend/LiteralGrammarH28/**`,
`tests/h28-sol/literal-grammar/**`, this file, and the lane's module-map
fragment `docs/module-map/frontend.d/literal-grammar.md`. Read-only inputs
(SHA256-pinned in `tests/h28-sol/literal-grammar/pins.json`):
`Checked/Lexer.lean`, `Checked/Token.lean`, `Checked/Tables.lean`,
`tests/upstream/grammar-0.8.38/SolidityLexer.g4`.

## Independent complete clause inventory

| Input/function | All clauses and branches | Current coverage |
|---|---|---|
| `escapeChar` | Quote single/double/backslash emit the original byte; n emits LF; r emits CR; t emits TAB; LF/CR emit empty; other bytes refuse. | kernel checked: escape_complete/escape_sound |
| `utf8` | cp < 0x80 emits one byte; otherwise cp < 0x800 emits two; otherwise three. Formula encodes all four-digit escapes including surrogates. No scalar or UTF8 validation may be added. | kernel checked: codepoint_iff and utf8_length |
| `strBody` | Empty; backslash-x plus two digits with true/false digit guard; backslash-u plus four digits with true/false digit guard; escaped CRLF; other backslash-c with successful/failed simple escape; raw byte with allowed-and-not-backslash true/false. Truncated x/u fall through the simple escape branch and refuse. Singleton backslash falls through the raw-byte branch and refuses. | kernel checked: body_iff and Body.toStrBody |
| `quotedBody` | Empty refuses; nonempty requires opening byte single/double quote and matching last byte, returns exact dropLast body; every failed guard refuses. Empty remainder, missing closer, unequal closer, invalid opener must be covered. | kernel checked: quotedBody_iff |
| `hexBody` | Empty accepts empty; pair followed by underscore requires both hex digits and nonempty suffix, recursively emits one byte; failed guard refuses; ordinary pair requires both hex digits, recursively emits one byte; failed guard refuses; singleton refuses. | kernel checked: hexBody_iff and encodeHex_roundtrip |
| `plainString` | quotedBody success dispatches printable(q) decoder; quotedBody failure refuses. Printable excludes quote, permits ASCII 32..126; strBody separately excludes raw backslash. | kernel checked: plainString_iff |
| `solTok` literal arms | Word and punctuation priority precede plain strings. Plain success emits str; plain failure dispatches hex prefix or unicode prefix. Hex requires quotedBody and hexBody. Unicode requires quotedBody, no irregularBreak and bidiBalanced before unicodeChar decoding. Other input falls through unchanged numeric arms. | kernel checked: solTok_literal_iff |
| `yulTok` literal arms | Bare hex refuses; word/punctuation priority; plain success emits str; hex prefix plus quotedBody/hexBody emits hexStr; otherwise unchanged numeric handling. Unicode is not a Yul literal arm. | kernel checked: Yul literal iff/impossibility |
| `classify` modes | Trivia priority, then sol; pragma semicolon/pragma-word handling; assembly punctuation priority then double-quoted raw length >2 plain string; Yul at arbitrary depth. | kernel checked: modeLiteral_iff |
| `untilQuote` | For literal delimiters 34/39: empty refuses; escaped CRLF copies three raw bytes; other backslash-c copies two; matching quote closes and leaves suffix; raw newline refuses; other raw bytes recurse. Singleton backslash belongs to raw-byte recursion then fails at end. | kernel checked: untilQuote_iff and ModeLiteral.split |
| Fragment concatenation | Lexer tokens contain individual fragment byte lists; concatenation laws must state exact byte sequence/order and refusal/classification boundaries. | kernel checked: modeSequence_iff and fragment append/flatten laws |

## Queue accounting

1. Independent Escape, Body, Quoted, HexBody, Plain, UnicodeLiteral, HexLiteral, Scan, Fragments, ModeLiteral and ModeSequence grammar/value relations are implemented independently of decoder outcomes. Body.toStrBody reuses existing strBody_sound. Numeric/EIP55 implementations remain immutable.
2. Arbitrary-length completeness/soundness covers simple, hex and Unicode escapes, escaped line ends, both quote modes and exact values. Scan/split theorems preserve every arbitrary suffix. Scanner iff is for literal delimiters 34/39; q=92 is an explicit negative boundary control.
3. Exact pair/underscore rules, independent byte/codepoint arithmetic, lengths, fragment concatenation values, universal classification iff/refusal consequences and all-byte constructive round trips are proved. All modes are characterized, including asm raw-source length/quote guards and unsupported pragma/Yul literal classes. Mixed-kind sequences are lexical; no parser-expression admission is claimed.
4. 255 kernel rows (28 hex, 53 body, 56 boundaries, 118 classification; 242 and 105 before the 2026-11-06 fixture rerun), inhabited positive and universal negative controls, 219 public theorem signatures/axiom pins (200 before the backfill) and 71 fixed compiler cases (58 before the rerun) in both pipelines are implemented.
5. Backfill (2026-11-05, `Lengths`, `Utf8Shape`): see below.

The old StrBody relation overlaps at escaped CRLF for an always-true predicate; the decoder emits empty but that relation can derive LF. Body models CRLF priority without excluding accepted inputs. Both the old overlap and new exact result remain visible kernel witnesses.

CodepointBytes preserves the original arithmetic, including surrogates and arbitrary Nat behavior. Invalid UTF8 is not silently rejected. Unicode canonical encodings use ASCII escapes with proved no-irregular-break and balanced-bidi guards. All-byte assembly roundtrip includes the empty value using escaped LF so the existing raw-length guard is met.

The global generated-word-table range proof covers every original matcher branch at the existing budget. Its proof-producing tactic applies safe lemmas and checked equality elimination, fails on unsupported shapes/cap exhaustion, and introduces no trust shortcut. ProofSafety reports exactly eight safe owning-module definitions; the range theorem has no axioms. Failed budget/recursion experiments remain in scratch logs; no budget was raised.

## External compiler boundary

soljson 0.8.38+commit.1835d247.Emscripten.clang SHA256: `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`. Fixtures request actual bytecode and AST in legacy and viaIR; exact values, Sol/Yul literal spans, error diagnostics, assembly flags, input/source/bytecode hashes are fixed. External observations are not kernel proofs or general conformance.

Initial strict comparison failed six rows (three cases times two pipelines), retained in evidence. Exact observation checking retains these differences: Unicode surrogate escape encodings are accepted by the byte model but rejected downstream by solc with SyntaxError 8452; plain surrogate escape compiles. solc accepts empty and single-quoted assembly flags, while the pinned model refuses raw length two and non-double quotes. Frozen producer/alignment files were not changed. JSON cannot transport arbitrary invalid UTF8 source bytes; byte-level kernel controls cover those cases.

## Claude VM completion (2026-11-05/06)

Branch `cloud/moved4-20261105/literal-grammar`, started from
`cloud/literal-grammar-move` (3b327d00, which restores `solc-fixtures.mjs`)
merged with master aec9adf1. Lean 4.24.0 / Lake from `lean-toolchain`; 4
cores, 15 GB, no swap.

### Queue item 1: fresh validation

- `./run-lean.sh` at 079ef4ac (25m36s): every target built except
  `Solidity.Examples.Tactics.OpenLoops`, which another lane owns. Lean was
  killed with exit 137 (out of memory) after 801 s while other jobs ran in
  parallel. The final head's run is recorded under "Final gates".
- In that build `FullPins` was built fresh. `audit.py --record` copied its
  `#print axioms` and `ProofSafety` reports to `evidence/axioms.log`, and
  `proof-source-identities.json` binds that log's SHA256 to all 26 source
  hashes. All 219 axiom sets and the 8 `DECL_SAFETY … safe` lines match
  `pins.json`. Every set is within {propext, Classical.choice, Quot.sound}.
- `register.sh --check` passes. `check-orphans.mjs` reports 5810 reachable,
  0 orphaned. `check-doc-paths.sh` reports one missing path, which is not
  from this lane: `docs/feature-work/after-roadmap-va1.md` cites a Mathlib
  file under `Bridge/.lake` that is not fetched here.

### Queue item 2: audit repair

`audit.py` used to verify an adoption chain of Codex-VM commits (0858098f,
9cbd923a, 405995c1, 59c3e31c). Those commits were never published, so the
audit could not run. It now reads only committed files, git, and an optional
fresh Lean log:

- **Axiom reports.** It takes the `FullPins` reports from a supplied log or
  from the committed `evidence/axioms.log`. A supplied log must show
  `FullPins` being built or replayed. The committed log must match its
  SHA256 in `proof-source-identities.json`. A supplied log is not otherwise
  bound to the sources; `--record` makes it the committed evidence.
- **Wrapped lists.** Axiom lists that Lean wraps onto continuation lines are
  rejoined before matching.
- **Scope.** It checks changes against the merge base with origin/master,
  or `--scope-base`, using `--no-renames`. It fails if neither base
  resolves.
- **Shared files.** `Solidity.lean` and `docs/module-map/frontend.md` may
  change only in lines that name this lane.
- **What scope no longer covers.** The Codex-era history from 6f3eedf was
  audited on the Codex VM and is not re-checked.
- **Removed.** The obsolete `adopted-master.json`, the Codex
  `runtime-bin/lake` wrapper and `runtime.toml`.

### Queue item 3: solc fixture rerun

First session (2026-11-05): blocked. `binaries.soliditylang.org` was denied
(proxy CONNECT 403) and the npm `solc@0.8.38` `soljson.js` has a different
SHA256 (0b15fcb2…), so it was not used.

Follow-up (2026-11-06): `soljson-v0.8.38+commit.1835d247.js` was fetched
from the GitHub mirror
`raw.githubusercontent.com/ethereum/solc-bin/gh-pages/bin/`. Its SHA256,
`6c74ffba…4312d390`, equals the pin in `solc-cases.json`; the runner checks
it again together with the reported version.

- `node tests/h28-sol/literal-grammar/solc-fixtures.mjs <soljson> <out> check`
  on the Codex-era 58 cases: PASS, and the output equals the committed
  `solc-observations.json` (all 116 observations, bytecode hashes
  included).
- New cases (13), each with a matching `FullControls.lean` row that the
  kernel checks (`fullControls_pass`). The model and solc agree on all 13:
  - raw control bytes: `plain-raw-TAB`, `plain-raw-NUL`, `plain-raw-DEL`
    (solc ParserError 8936 "Invalid character in string", model refuses:
    not `printable`); `unicode-raw-TAB`, `unicode-raw-NUL`,
    `unicode-raw-DEL` (both accept the raw byte as the value);
    `unicode-raw-CR` (both refuse; solc "Expected string end-quote");
    `yul-raw-TAB` (solc ParserError 1465, model refuses);
  - the other quote inside a literal: `plain-double-other-quote` (`"'"`),
    `plain-single-other-quote` (`'"'`), `unicode-double-other-quote`,
    `unicode-single-other-quote`, `yul-single-other-quote` (all accept,
    values `27`/`22`).
- `record` mode rewrote `solc-observations.json`: the 116 earlier entries
  are byte-identical (the diff only adds lines), 142 in total. A second
  `check` run then passes: "PASS 71 cases x legacy/viaIR".
- `audit.py` now derives the observation count from the case count
  (71 cases, 142 observations) and prints the summed kernel-row count
  from `pins.json`; `full_control_count` is 118.

A raw NUL/DEL fixture travels as a JSON string. The runner's
`sourceSha256` binds the exact bytes.

Follow-up reviews (read-only, no Lean server):

- Finder: the model rows, `.yul 7`, byte spellings, coverage JSON and
  `audit.py` are correct. It found three doc defects, all fixed in
  1ff1c163: the stale status line, a stale "Not fixed" entry for these
  fixtures, and a wrong merge date.
- Skeptic: all five claims confirmed: pinned SHA256 and version, the 116
  earlier observations unchanged, all 13 verdicts for solc and the model,
  "PASS 71 cases", and that solc reads the raw bytes (`unicode-raw-TAB` span
  `134:12:0`; plain cases fail with 8936 "Invalid character"). Caveats:
  - The exact-span assertion runs only for accepted cases. The five
    refused raw-byte cases are pinned by their frozen error locations in
    `check` mode.
  - The runner does not compare the model with solc. Agreement rests on
    the `FullControls` kernel rows and `audit.py`; the kernel check
    itself comes from the `run-lean.sh` build below.

### Queue item 4: backfill (suffix, byte-length and encoding properties)

`Lengths.lean` (13 theorems):

- **Scanner.**
  - `Scan.deterministic`: the split is unique for a literal delimiter.
  - `Scan.isSuffix`, `Scan.length_eq`.
  - `Scan.length_lt`: at least the closer is consumed, so the suffix is
    strictly shorter.
- **Plain and unicode literals.** `Plain.length_le` (out + 2 ≤ raw) and
  `UnicodeLiteral.length_le` (out + 9 ≤ raw). These are one-sided: an
  escaped line end decodes to nothing.
- **Hex literals.**
  - `HexLiteral.length_bounds`: 2·out + 5 ≤ raw ≤ 3·out + 5.
  - `HexBody.length_tight` and `HexLiteral.length_le_tight`: raw ≤ 3·out + 4
    for a nonempty value, reached by `hex"00_00"`.
- **Fragment sequences.** `Fragments.length_eq`,
  `Fragments.flatten_length_le`, and the plain/hex/unicode `FragmentValue`
  sums.

`Utf8Shape.lean` (6 theorems):

- `CodepointBytes.shape` and `uniEscape_shape`: every `\uHHHH` escape emits
  UTF-8 lead/continuation bit patterns, never an overlong form.
- `CodepointBytes.value`, `uniEscape_value` and `utf8_injective`: the code
  point is recovered exactly.
- Surrogates keep the shape. The model adds no scalar check, matching the
  documented deviation.
- Controls: a surrogate and a two-byte value (inhabited), and overlong
  C0 80 and E0 80 80 (negative).

All 19 theorems are pinned in `FullPins`/`pins.json`. The module-map
fragment `docs/module-map/frontend.d/literal-grammar.md` gives rows for the
17 lane modules master lacked.

### Queue item 5: reviews

Read-only finder and skeptic reviewed the backfill and the audit repair;
neither used the Lean server. Both found the new statements true and
non-vacuous, with no hidden premise. The `cp < 65536` premise is always met
by `\u` escapes (`hexQuad_lt65536`), and `IsQuote q` is necessary for
`Scan.deterministic`. Confirmed findings, all fixed:

- The hex upper bound was not tight. Added the tight theorems and corrected
  the docstring.
- The module docstring overclaimed "linear relation".
- `Lengths.lean` had an unused import, and the fragment theorems lacked
  docstrings.
- There was no three-byte overlong control or two-byte positive control.
- The audit pins had no committed Lean output. Fixed by the fresh log.
- A supplied log was accepted without any marker.
- Renames could bypass the scope check, and the check was skipped silently
  without origin/master.
- Shared files were allowed wholesale.
- `adopted-master.json` was stale.

Fixed later: **printable-boundary fixtures** (raw control bytes, the other
quote inside a literal) were added on 2026-11-06; see queue item 3.

Not fixed:

- **Model/compiler hex agreement.** Agreement on cases both accept is a
  property of the data, not asserted by the gate. This is by design.

### Final gates

- `./run-lean.sh` at d22b90d8 (later commits change only this doc
  from the final head). layers, `register.sh --check` and
  `fragments.sh --check` pass. `lake build` of every default target plus
  `SolkeyTestSuite` completes: all 5826 jobs, OpenLoops included (585 s),
  no `error:`. The script then exits 1 at its last step,
  `check-solkey.sh`. That step reads the default rules path
  `../solkey/...`, a sibling checkout at upstream b8d5f88, which is newer
  than the pinned snapshot (392 taclets, 167 mismatches). This comes from
  the environment, not the lane.
- `check-solkey.sh` with `SOLKEY_RULES` set to the pinned snapshot
  `tests/migration/solkey/.../solidityProgramRules.key` (commit 473da894):
  exit 0, "parsed 377 taclets, 131 read-bearing, table covers 131;
  annotations match".
- `python3 tests/h28-sol/literal-grammar/audit.py`: PASS. 4 frozen input
  hashes, 219 exact theorem axiom sets, 242 kernel control rows, 8 safe
  declarations (fresh report), exclusive scope since aec9adf1.
- Lean MCP diagnostics are clean (severity error) on `Lengths.lean`,
  `Utf8Shape.lean` and `FullPins.lean`.

### Follow-up gates (2026-11-06)

- Merged origin/master in 44e41be2. The Lake cache release
  returned 404, so the build was cold.
- `./run-lean.sh`: the first run reached job 6350/6430 with no `error:`
  before the 2-hour background limit stopped it. The rerun completed:
  layers, `register.sh --check` and `fragments.sh --check` pass, and
  "Build completed successfully (6463 jobs)", exit 0, 13m33s. The SolKey
  checker is no longer part of the script (master a897dac76).
  `FullControls` (`fullControls_pass`, 118 rows) built in the first run.
- `audit.py --record <first run log>`: `evidence/axioms.log` is
  byte-identical. Only the `FullControls.lean` hash in
  `proof-source-identities.json` changes. `audit.py` (committed log) and
  `audit.py <first run log>`: PASS, 219 exact theorem axiom sets, 255
  kernel control rows, 8 safe declarations, exclusive scope (21 paths).
- `solc-fixtures.mjs … check` against the pinned soljson: "PASS 71 cases
  x legacy/viaIR".

### Retained deviations

- Unicode surrogate escapes: the model accepts them, but solc rejects
  unicode-literal surrogates downstream (SyntaxError 8452).
- Empty or single-quoted assembly flags: solc accepts them, the model
  refuses them.

Neither theorem statements nor frozen inputs were weakened. No sorry, axiom
or `maxHeartbeats` change.

### Codex-era history

The Codex VM's adoption, cache and blocked-registration narrative, and its
receipts, live in `tests/h28-sol/literal-grammar/evidence/` and in git
history before this section. They are historical. The bulk logs, the cache
pack and `codex/h28-preserved-6492f34c` stayed on the Codex VM.

Master's `4492e6ed9` ("Audit external H44 evidence after published
integration") added `--evidence-dir`/`--published-integration` modes to the
Codex-era `audit.py` for evidence under the Codex VM's `/workspace/scratch`
and recorded a PASS there; `bulk-artifacts-h44.json` lists those off-git
artifacts. The 2026-11-06 merge kept this branch's rewritten `audit.py`,
which checks the committed `evidence/axioms.log` and scopes to the merge
base, so those two flags are gone; that historical PASS stays in git history.

### Codex conflict resolution (2026-11-07)

Merged published master2a43bf4fcdaf24750265afc8f8be5b420d1d22b0 into the preserved ea1876 branch. The portable audit, all26 modules/219 theorem pins/255 kernel rows/71 scanner cases, and the published runtime-profile deletion are retained. No older24-module audit or VM-only profile is restored. VM serial configuration and logs stay outside git. The old scope question is historical; central registration is present, and no validation waiver is inferred.

The completed immutable4492 build remains historical:6442-module original defaults/examples/native/TestSuite,exit0,3:10:03,RSS7864360KiB,0swaps. The subsequent full gate at ea1876 was stopped for this superseding merge request during run-lean; only its build-touched gate completed. It is not reported as a passing full gate. Both log sets are preserved at /workspace/scratch/h28-audit-5f145965 and /workspace/scratch/h28-current-e8247d92. Resolution evidence is /workspace/scratch/h28-resolve-2a43bf4f. Fresh resolved-head gates and reviews are recorded there; original proof versus finite compiler-observation boundaries remain unchanged.

Resolved-tree VM gates:26-module serial build PASS15.80s,RSS1400336KiB; fresh portable audit PASS219 exact axiom sets/255 kernel rows/eight safe definitions; all four kernel control files and ProofSafety PASS; permitted KeySort PASS. ActualLean4.24.0/Lake5.0.0-src+797c613. Fresh pinned compiler gate PASS71cases times legacy/viaIR,3.08s,RSS226964KiB,0swaps. Cache pack26modules/78artifacts/26mappings verified for coordinator pull; no VMshipping or import claim. Both read-only reviews found no conflict-resolution blocker. Global docpaths still fails on four references outside H28; no passing whole-project/full-runtime gate is claimed. The user explicitly authorized pushing the resolved assigned branch; default-branch push/merge is not performed.
