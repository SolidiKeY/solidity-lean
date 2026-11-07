# G35-INT-RAW-1105 — partial checkpoint

Repository /workspace/solidity-lean; existing branch codex/solidity-sol2-20261104/constant-depth; published input b86ae4568cef6d6226f4d170360bbb089debe3fb. Gate HEAD 7498f1de074830309966c3765111c7ec7b617b8c.

Execution and Controls are actual kernel-checked modules. decode_range unfolds the existing decoder for arbitrary IntTy (signed or unsigned); signed types use the existing signed wordInt interpretation. copy_run computes every raw word and derives the exact allocation-or-error outcome for arbitrary lengths and initial states. No success/representation premise, new decoder, producer edit or increased budget. Controls include signed roundtrips at -1/-128, positive127, dirty128/255, actual positive127 copy, dirty copy and late-dirty rollback. Negative roundtrip controls do not yet establish actual negative-byte array copying.

Execution build about1second; Controls1.2seconds; no owned module above60seconds. Both built separately with explicit -j1. Docker cap12884901888 bytes, swap0, one CPU, LEAN_NUM_THREADS1 after activation; writer lock and4GiB reserve guard. Axioms.lean MCP diagnostics succeeded with10 informational actual axiom reports, no partial/timeout/errors; exact guard pins still pending. No sorry/admit/axiom/unsafe or heartbeat increase.

Requested touched gate PASS. Checkpoint: touched/library/trust/layers/docpaths PASS; orphans/roots FAIL for unregistered RawInt modules; axiom inventory FAIL with0errors79unrecorded ConstantDepth pins. The coordinator has answered Q-PIN-1: refreshed ConstantDepth patch is coordinator-applied at scheduled integration; no worker exception. Current old packet remains intact; refreshed central patch against latest publication remains pending. RawInt roots/maps/pins also stay central. RawUint was read-only and unchanged.

Separate read-only finder and skeptic, neither using Lean/server or editing files, found no semantic defect in current proofs. Both explicitly classify this as partial: actual negative-byte/mixed-offset copies, guarded-entry/frame-binding, resolved eval_copy/horizons, allocation observations, padding/empty/near-width controls and exact axiom pins remain outstanding. Finder additionally requests general signed-extension accepted-word arithmetic. These are ready owned obligations, not missing upstream inputs or new premise requests. No completed-item claim.

ConstantDepth original mathematical proofs and prior seals remain unchanged. Its final central registration/full-gate obligation remains separately recorded. H41 unchanged: no ship-cache.sh; cache delivery coordinator-owned. This checkpoint creates no goal and does not mark either whole assignment complete.

## Next increment (still partial)

Fetched and verified publication 8bf8321873befa3f35ca31e97e5339a1baee93e6; the previously delivered two modules are byte-identical there. Existing owned history and original seals are preserved. This increment adds signed_decode_range, the intrinsic copyExpr, eval_copy for actual resolved local conversion at n+2, and guarded_run for entry-before-copy ordering. signed_decode_range exposes the 256-bit signed branch; it is not yet the independent width-specific accepted-range equivalence. guarded_run intentionally does not identify its data bytes with F.cd; frame binding remains an obligation.

Execution passes in about1second (bounded group2.60seconds), dependent Controls passes; no owned module above60seconds. Fresh MCP Axioms diagnostics:13 reports, success true, partial false, timed_out false, all information severity. Intermediate proof attempts hit the unchanged200000heartbeat budget and were corrected using explicit boolean guard shape and published STy.same_refl; no budget was raised. Failed attempt metrics remain recorded.

Separate read-only finder and skeptic reviews PASS for these statements, with no Lean/server or edits. Both confirm no decoded-value/success assumption or premise weakening; localRef is the actual input local binding. Both retain the partial boundary: finite-width arithmetic, selector/frame binding, raw-negative copying, observations and expanded controls/pins remain unfinished.

## Observation increment (partial)

Fetched published3ad22f66d8fc6431378c22e71823436c79dede7f and verified8bf83218 ancestry; preserved current branch and unintegrated RawInt changes. New copy_observations derives full rollback on error; success identifies fresh-address contents, next increment, every address other than next, locals and all nonheap state fields. No heap-validity premise is supplied, so it does not assert the allocation address was unused in arbitrary input states. Four new controls cover arbitrary-frame/off empty allocation, actual EOFzero-padding at offset123, and generic evaluator horizons0/1.

Both modules build serially in3.56seconds total; no owned module above60seconds. Fresh MCP inventory contains18 information-only actual axiom reports; no partial/timeout/error. Separate read-only finder and skeptic accepted the statements without Lean/server or edits. Skeptic identified an overbroad English phrase about old allocations; corrected to every address other than the allocation address, matching the theorem exactly. No theorem or premise changed.

The observation and empty/EOF controls cover those cases. The zero/one-horizon controls demonstrate fuel exhaustion only; they do not close semantic or execution-adequacy obligations. Width-specific accepted-range arithmetic, actual raw-negative/mixed-offset copying, frame binding/guard controls, partial-word padding were unfinished at this historical checkpoint; the published increment below supersedes this list and supplies the exact guarded axiom pins. Original ConstantDepth and prior RawInt seals stay intact.

The earlier checkpoint lists above are historical. Current published coverage is recorded below.

## Claude-VM increment (2026-11-05)

The following preserves the published Claude-VM report. Its references to "here"
and "this checkout" refer to that VM, not fresh validation on the original Codex VM.

The lane moved to a Claude VM (`cloud/moved4-20261105/constant-depth`). The Codex
bulk evidence (H44, `H44-manifest.json`) stays on the Codex VM and is not cited;
everything below was re-run here. The Codex wrappers `lake` and `bounded.py` were
removed.

New in `Execution.lean` (all for arbitrary `IntTy`, frames and lengths):

| Theorem | Statement |
|---|---|
| `accepted` (def), `range_iff_accepted` | the decoder's range test equals an independent width test: signed `w < 2^(b-1) ∨ 2^256-2^(b-1) ≤ w`, unsigned `w < 2^b` |
| `accepted_sign_bits` | for signed widths, acceptance iff the top `257-b` bits are all equal (`w / 2^(b-1)` is `0` or `2^(257-b)-1`) |
| `accepted_value` | an accepted word's value without `wordInt`: `w - 2^256` in the high band, else `w` |
| `decode_accepted`, `decode_dirty`, `decode_ok_iff` | decoding succeeds exactly on accepted words; dirty words revert with empty data |
| `values_zero`, `values_succ`, `values_ok_iff`, `values_dirty` | validation reads the head word then the rest; it succeeds iff every word is accepted |
| `dataValues`, `values_frame`, `guarded_frame_run` | with `F.cd = selector ++ data` (4-byte selector), the guarded entry+copy outcome in terms of the argument bytes: each of the three `cdTail` refusals and each dirty word preserves the state; success allocates the decoded words |

New controls in `Controls.lean` (each runs the real `Source.cdToMem`/`cdTail`;
word values are kernel-checked facts about the bytes, via `decide +kernel`):
near-width acceptance for `int8`, `int16`, `int248`, all of `int256`, `uint8`
255/256 and all of `uint256`, and `sign_matters` (200 is clean for `uint8`, dirty
for `int8`); `near_width_decode` (−128, −129, −2^255, 2^255−1 through the decoder);
raw negative bytes at the unaligned offset 3 (`negative_copy`: −1, −128, 127),
the suffix at 35, the misaligned window at 2 (reverts), the same bytes as `uint8`
(revert); an `int16` copy of −2^15 followed by a revert on 2^15; partial-word
padding (`0xff` pads to a dirty `int8` word and to the `int256` value
`0xff00…00 − 2^256`; `0x00` pads clean); and guarded entry under the frame
binding: admitted (`entry_frame_copy`), dirty second element, truncated
elements, short head, length ≥ 2^64, the unshifted offset 64 (dirty), and
selector independence. `eof_padding` now says that past-EOF zero reads are the
standalone helper's; at entry `cdTail` refuses such spans.

Pins: `tests/calldata-packets-1105/RawInt/Axioms.lean` has exact `#guard_msgs`
pins for all 55 public theorems (standard axioms only; nine controls use none);
the same block closes `Controls.lean`, so the library build checks it.

Reviews (read-only, no Lean server). Skeptic — ACCEPT-WITH-FINDINGS: `accepted`
is independent of `wordInt`/`lo`/`hi`, `guarded_frame_run` matches the RawUint
template, controls execute the real operations, nothing earlier was weakened.
Its findings, all fixed: pins were not built (now inline too); the boundary
docstring over-claimed for unsigned widths (unsigned controls added, header
narrowed); `eof_padding` needed the entry caveat. Finder — confirmed and fixed:
no short-head or large-length entry controls (added); no control showing the
selector shift matters (added `unshifted_copy`, `selector_independent`);
`decode_accepted` gave the value only through `wordInt` (added `accepted_value`);
`signed_decode_range`'s docstring over-claimed (rewritten); widths beyond `int8`
had no copy (added `int16_copy`). Its pin-exactness doubts (`values_zero`,
`int256_all`) are settled by Lean: the pins pass.

Still open: none of the listed RawInt obligations. The H44 bulk is unverifiable
from this checkout and is not relied on.

Gates for this increment: see `constant-depth.md`, section "Gates" (one build covers both areas).
