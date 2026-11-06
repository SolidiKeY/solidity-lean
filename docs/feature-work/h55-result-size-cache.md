# H55 result, size and cache: work in progress

The scripts and controls in `scripts/h55/result-size-cache/` and `tests/h55/result-size-cache/` are prototypes. No producer or consumer owner file has been edited. No checkpoint is complete or adopted.

## Size check

At base 4d3790eadb8a5212233bc7d5e345817476b2f590 the regular-blob census has 14,271 files, 249 over 100 KiB, 27 over 1 MiB and a 333,160-byte largest Lean source. The proposed 100 KiB data and 1 MiB source thresholds are provisional. The helper reads source approvals from the supplied base and binds them to SHA256; it cannot establish that the caller chose the coordinator-trusted base. The pinned base has no approved-source file. A coordinator-owned base/approval flow and production adapter are required. This prototype is not a safe production gate.

## Result schema and poller

The JSON Schema draft and validator reject duplicate keys, non-JSON constants, invalid marker pairs and schema errors. `jsonschema` is an external Python dependency in strict mode. The patch was produced against supplied poll.py SHA256 `32aa42866f73297bae955a086f93103eab9f8513beb6e92c993fa2743c916ac5`; isolated tests apply it to a copy and run the complete poller against a mocked API with a simulated backup. It is not deployed. A future deployment must verify the target digest, install the dependency and schema, and preserve `poll.py.bak-h55` before adoption. No real host backup exists yet.

The patch preserves the original parser for legacy batches and enables strict parsing only for explicitly configured `H55_STRICT_BATCHES`. In strict mode a completed turn requires exactly one `agentMessage` with `turnId` equal to the completed turn ID and `phase` equal to `final_answer`; missing or ambiguous association fails closed. An error clears a prior result from the strict batch digest and saved poll state in the tested simulated environment. If digest replacement fails, the poller logs the failure and continues, but the old digest remains readable; a fail-closed reader/adoption protocol needs coordinator review. The supplied snapshot does not establish that the real inspect API emits those metadata fields or includes the final message in the requested page. Strict mode must remain disabled until the coordinator verifies an authoritative or sanitized live fixture. The supplied snapshot also does not list this H55 batch in ACTIVE/WATCH: catalog selection and service configuration remain coordinator-owned.

ESCALATE: strict result validation and existing handoff producers use different formats. Coordinator options: (1) migrate affected producers and enable strict mode for their batch after verifying turn metadata, requiring coordinated rollout; (2) retain the existing parser for legacy batches and enable strict mode only for batches whose producers and API metadata have been verified. The isolated controls demonstrate the compatibility boundary; they do not establish production deployment or turn metadata truth.

## Cache

H62/H63 supersedes the v4.24 per-master cache item. No cache implementation or roundtrip was completed. The v4.35.0 migration and Lake remote cache are assigned to solidity-h62-6-20261106/migrate-root-gate, with cut-over controlled by the coordinator. Retain H41 cache-inbox; do not freeze master or publish a cache.

## Checks and reviews

`PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/h55/result-size-cache -p "test_*.py" -v` passed 21 tests. Independent finder and skeptic reviews used no Lean server. Size-review fixes include bounded reads, explicit hidden-index rejection, history inspection, data/source digest binding and deletion census; trusted base and operational approval remain open. Result-review fixes include strict SHA length, opt-in legacy compatibility, fail-closed synthetic turn association, stale digest invalidation, and missing-validator startup compatibility. Controls use the real legacy producer and a mocked API with a temporary backup. Live API turn association, service configuration, real-host backup, producer rollout, and a final review remain open. No Lean proof result or KeySort pass is claimed.

## H82 standing rules and waits

H82 supersedes the previous exact-file agreement protocol for statement-preserving edits; interface and semantic changes still require the applicable owner. The draft schema now requires typed, nonblank `waits` entries and forbids nonempty waits for `done`. Independent finder and skeptic reviews identified those validation gaps and they were fixed. A simulated digest-write refusal leaves an old digest readable even though the poller continues and records the error; a fail-closed consumer or independent invalidation protocol remains a coordinator dependency. The source approval/base trust, real inspect metadata, owner-controlled rollout and final proof gates also remain open.

## H82 successor: versioned report compatibility

The authenticated H82b assignment/scope and final stopped receipt were verified;
exact final head `6c93ebcd6f7125bd0c9913cf211565a50b4241b1` was merged before this
work. The optional integer `schema_version: 1` field now accepts the coordinator's
v1 report envelope while preserving legacy unversioned inputs. Unknown fields,
unsupported versions, booleans, strings, null and fractional versions remain
rejected. Versioned done reports retain all existing completion constraints.
JSON Schema treats numerical `1.0` as integer one; no lexical-number restriction
is claimed. Independent read-only finder and skeptic found no blocker and used
no Lean server. Final local controls ran 23 tests: 20 passed, 3 skipped because
the original host poll.py snapshot is unavailable on this VM. Evidence:
`/workspace/h62-statement-graph-evidence/h82/h55-schema-final-tests.log`.
This does not establish host deployment, real inspect metadata, fail-closed
consumer adoption, trusted-base integration or completion of either H55 item.
