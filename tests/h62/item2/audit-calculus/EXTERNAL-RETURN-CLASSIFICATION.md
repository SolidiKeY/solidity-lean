# External return byte decoder premises

This covers all eight frozen theorem candidates in `Solidity/Semantics/ExternalReturnBytes.lean`; exact source bytes match frozen and adopted master. Definitions and generated declarations are dependencies, not additional frozen theorem rows. Current semantic ownership is master/coordinator, no live semantic producer, per the Q-SEM-OWNER-05 coordinator lookup. The registry row H62-6-MIGRATE-SEMANTICS routes isolated migration to solidity-h62-6-20261106/migrate-root-gate with writeMode=isolated-migration-overlay-no-live-owner-transfer; current leases record no semantic lease. That separate H129 v4.35 responsibility does not transfer master ownership, switch the Lean4.24 toolchain, establish semantic acceptance or release any STOP.

`words count data` checks `count*32 ≤ data.length` before reading the required words with the existing ABI loader. This prevents its zero-padding behavior from accepting truncated required return words. `decode` feeds those actual words into the existing intrinsically typed binder decoder. Primitive conversion does not certify contextual nominal/source checks, and surplus bytes, including an incomplete trailing word, may be ignored.

| Theorem | Joint premises and exact conclusion |
| --- | --- |
| `complete_word` | An actual successful `words count data` read and `i<count` imply `i*32+32 ≤ data.length`. This is not exact total length; no demanded index exists at count zero. |
| `decode_ok` | Actual successful byte decoding yields the same word list from a successful required-word read and a successful typed decoder equation for the same environment and residual word list. A detached arbitrary-word witness is insufficient. |
| `empty_snoc` | Any nonempty snoc binder declaration fails with revert on the empty word list. This does not assert a successful read of any original byte input or failure of an empty declaration. |
| `decode_error` | Actual byte decoder failure with revert yields some word list on which the binder decoder also reverts. If required words were read, those words supply the witness. If the bytes are too short, the proof uses the empty list and the nonempty binder case; an empty binder declaration cannot enter that short-read branch. The conclusion contains no successful word-read equation. |
| `classify_error` | Actual error decoding to a reason determines the error tag immediately, without a panic-decoder refusal premise. |
| `classify_panic` | Actual error-decoder refusal and panic-decoder success on the same bytes jointly determine the panic tag; error-first precedence is retained. |
| `classify_other` | Both actual decoders refusing yields the other tag. This is classification, not universal physical invalidity or proof that no other error behavior exists. |
| `raw_data_exact` | The explicit bound `data.length < 2^256` gives raw catch decoding to exactly the original data, with no canonical re-encoding. |

Failure classification extracts a reason or code view; it does not replace the original bytes supplied to raw catches. These equations and conditional existential witnesses do not construct source executions, prove compiler/native adequacy, close callback integration or establish totality of an original source call.

At checkpoint V140 the exact eight ledger bindings are published at private commit 9d1f018b304ec0b8ed79c1265f0da06110297f05, directory evidence/solidity-h28-sol-20261104/automation-benchmark/external-return-inputs-v140. That historical packet contains1709 reviewed/3574 pending of5283; prior1701 rows, owner map, scope and provenance remain unchanged. At that checkpoint owners were3884 confirmed/1399 unresolved. Static classification gives no fresh joint-witness credit.

No source, statement, dependent definition, interface, budget, axiom, exclusion or toolchain changes. Zero fresh joint witnesses and no fresh Lean/kernel/replay/runtime/performance acceptance. All H28 pauses and STOPs remain, including actualCallerFields/extractionActuallyChanges/replay. Historical unavailable exact bytes remain UNVERIFIABLE.

At checkpoint V141, Q-SEM-OWNER-05 is acknowledged and only the three approved file-owner entries plus17 reviewed owner fields change. All1709 classifications and the5283-row frozen census remain unchanged;3574 role rows stay pending. Current owners:3901 confirmed/1382 unresolved. The exact owner-only input packet is private commit a6ebf45f5931f241db9fd3d381914bf0a932943d, directory evidence/solidity-h28-sol-20261104/automation-benchmark/semantics-owner-inputs-v141. Earlier packet owner counts describe their historical checkpoints.
