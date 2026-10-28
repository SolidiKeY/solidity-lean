# Value-aware entry prerequisite audit (2026-10-28)

Starting checkpoint `38871aee752a24e37c2ac6196e9539ea3fd2c03a`, same saved VM,
branch `baseline/current-master-20261028`. This follow-up is blocked diagnostic
prerequisite evidence. It executes no Lean, compiler, EVM, or runtime probe.
`nativeValidationComplete` remains **false**. All preceding reports remain intact.

## Existing interfaces and why no probe ran

`Solidity.Lifetime.System.run` (`Solidity/Semantics/Lifetime.lean:97`) accepts
`TTx` explicitly. Its actual nonpayable guard precedes `World.enter` and the
body. `World.enter` credits payment once and creates a fresh frame; successful
runs produce a new persistent world. The failure path produces no changed world.
`System.call` takes closed typed programs; `System.payable` is a model-supplied
function. A faithful diagnostic must resolve imported ABI identity through
`Upstream.resolveEntry`, derive payability from the matching imported declaration
and row, and preserve successful deployment, transaction environment premises,
body execution, exact failure bytes, payment settlement and rollback.
`docs/lifetime.md` explicitly records that selecting the interface and matching
source metadata are model obligations. `System.run` alone does not establish
`World.accepts` or `allowCall`; it uses `Prog.run`, so only loop/recursion-free
controls could run without substituting for the existing fuel-bounded replay.

This API is **not currently callable through an identity-satisfied cache**.
Its 28-module current source closure is distinct from Testing's 257 modules.
The saved Lifetime setup has 24 references: 15 reference artifacts differ from
current local artifacts; seven current transitive modules are absent from that
saved setup, with four old imports outside the current source closure. Every
reference has both exact paths, timestamps, SHA256 values and byte comparisons
in `audit.json` and the final rerun `audit-final.json`. The 15 differing modules are:

- `Solidity.AST`
- `Solidity.Semantics`, `.Deploy`, `.Heap`, `.Run`, `.State`, `.Storage`
- `Solidity.SpecSyntax`
- `Solidity.Syntax`, `.Checked`, `.Elab`, `.Inlined`, `.Quote`, `.Scoped`, `.Splice`

These are stale descriptor observations, **not** proof that 15 modules need
recompiling. No Lifetime preflight or build was attempted after detecting this
identity failure. A Lake setup that selects the saved historical dependencies
would test an old closure, while importing the old olean against current modules
would not establish compatible current behavior. Neither is accepted evidence.

The other existing ordinary value-aware API is
`ContractWorld.World.enter/callFrame`. Its current source closure is also 28
modules, but its local root `.trace`, `.olean` and `.setup.json` are absent.
It additionally models funding, static calls and instance settlement; it is not
an already-available narrower substitute. `Contract.deployT` is cached but guards
constructors only. `State.withTx` accepts a value yet adds no payment guard.
`State.transactionEntry` resets ephemeral state but neither guards nor credits
payment. `Upstream.entryProg` elaborates the imported call and preserves the
transaction; ordinary nonpayability is not checked there. Upstream's payment
check is constructor-only, and `replay` exposes no value input. All 304 artifacts
from the verified 76-module native closure remain byte-identical to checkpoint
38871aee. A manually added `if !payable ...` would implement a new diagnostic
boundary rather than exercise an existing callable guard, so none was added.

## Concrete prerequisite and next discriminators

Obtain a current-identity Lifetime **root** artifact against its 27 current
dependencies, all already in the verified 76-module Upstream closure. Only the
Lifetime root adds to that reusable closure; the same is true of ContractWorld.
This is not evidence that a 28-module rebuild is necessary. This is a separate prerequisite owned by an authorized cache
refresh lane; this task has not requested or performed another build. It does
not require Testing, ProveChunked, a full build or universal feature proofs.
Then bind a diagnostic outside core to the actual imported ABI declarations
and invoke `Lifetime.System.run` with explicit `TTx` in both legacy and viaIR.
Keep the existing hard resource cap and timeout. Required pending controls are:

| Control | Required observation; currently unrun |
| --- | --- |
| Nonpayable, value zero | Successful body/storage change |
| Same nonpayable, value one | Empty-data rejection before body/payment commit |
| Payable, value one | Actual body sees caller/value; payment credited once |
| Payable body writes then fails | Exact body failure data; storage/payment rollback |
| Payable calls nonpayable helper internally | Internal call succeeds without repeated external guard |
| Internal-only ABI target | Canonical ABI resolver refuses it |
| Unchanged false-output control | Actual successful result disagrees with its independent false expectation |

No new fixture/variant association is asserted. Source refusals, documentary
proof-interface limits, and this missing runtime prerequisite remain separate.
Historical 40 typed-import modes, 38 replay results and 122 matching observations
are unchanged; they do not exercise nonzero-payment entry. No status, original
observation, expectation, pipeline, manifest or generated inventory was changed.
The cold exit124 at 90 minutes/546 of685 and peak8195923968 bytes, prior narrow
900-second timeout, and unrun warm measurement remain historical diagnostics.

## Reproduce and inspect

From the same clone, acquire the writer lock documented in
`docs/refactoring-progress.md` before saving new evidence; use a fresh output:

```sh
python3 scripts/solidity-baseline-value-entry-audit.py --out FRESH_OUTPUT.json
```

The script refuses an existing output path before collecting evidence, then
reads source/setup/trace/artifact bytes, compares the 304 native
snapshots, preserves tracked historical gap/attribution/probe/native evidence,
and runs positive synthetic descriptor plus missing-setup/import/hash negative
integrity controls. These controls are static, not runtime verdicts. Exit0 means
integrity checks pass and the blocked prerequisite is faithfully recorded;
it does not mean native validation passed. Raw source snapshots and feature
manifest rows for `stateMutability`/`msgValue` are retained with hashes.
The first executed driver is retained as `audit-driver-first.py`; the final
driver adds refusal of existing output paths and validates integrity before
writing. The final rerun and attempted overwrite control are separately logged.
See `commands.json`, `reviews.json`, and `handoff.json` for actual commands,
exits, logs, measurements and limitations. No new theorem or axiom check applies:
no Lean or semantic source was edited or checked in this follow-up. Earlier
standard-axiom prints remain preserved evidence for their original commands.
