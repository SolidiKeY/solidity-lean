# G21 finite storage ABI success: kernel control resolved

New module Solidity.Lowering.V08.LiteralFailureStorageSuccessControls.
Proof commit364b2a8d319fa133e49f860faeba175f28fa4d2e. Published master6510c302
was fetched/inspected before work; no relevant upstream implementation changed.
Original frozen base2fe1f893 and helper branch/goal preserved. Coordinator
registers the module; Source definitions and Solidity.lean unchanged.

This resolves the exact previously deferred storage decode_true full-run/state
control, not merely its outcome projection. No recursion/heartbeat/fuel/node
or process/time bound was raised. No native_decide or host-test proof shortcut.

copied_observed uses decide +kernel on the actual Source bytesOfRV success
projection, proving all31zero bytes followed by1. The new abstract
run_from_observation lemma combines such an actual observation with an
independent exact state-invariant Hoare proof. copied_full instantiates it
with the existing stored_bytes theorem, deriving the actual complete copy
run with unchanged caller/state. The helper's observation premise is fully
discharged by copied_observed at the claimed endpoint; it is not an oracle.

word_read separately kernel-checks actual Source.wordAt. word_decoder proves
the actual abiDecodeData bool action is pure true for these bytes. decode_true
then rewrites the real evalE calldata-independent storage-local abi.decode
through the two proved executions. It returns true at originalfuel35 for
both Source pipeline parameter values, with the entire original locals/state
unchanged. This is not native compiler pipeline or emitted-code agreement.

Controls reject an all-zero replacement word and reversed byte order, and
derive actual retained callerbool and old heapobject0 contents[9,7] from the
same final-state equality. No prior byte vector/status/fixture changed.
Historical canonical host output remains host evidence; a new independent
kernel proof now supports this finite statement. TERRA-TODO is append-only
marked resolved, with exact theorem/commit; old seals/failures not rewritten.

Initial direct state-invariant application still caused deep reduction. The
abstract action/state helper solved that separate elaboration issue. Wrapper
and fixture aliases were exposed only for theorem rewriting; pure bool
word-read/decoder normalization was isolated from the large function-valued
state. Failed attempts and their real diagnostics are retained. Final MCP and
focused toolkit checks plus scoped actual axioms accompany the seal. Both
finder/skeptic source and exact artifact reviews are read-only without Lean.

This closes one finite kernel control. FullG21/G40/G41/G42 and BackfillsA/B
remain partial, including emitted runtime ABI/unknown-memory encoding,
source/native/target/world/frame/resource and final mandatory gates. P3 and
G42.03 remain RO. Published interfaces retain real premises; old9V12 staging
is preserved and not imported by this touched closure. Suite124/full1/cold124,
rawdocs1/frozencomparison1 and prior failures remain failures, not rerun.
Goal unchanged blocked; no reset/reactivation/completion or publication.
