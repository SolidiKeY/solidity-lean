# P8a checked syntax/settings checkpoint

This implements a checked parse-stage and raw-input validator. It is **not**
complete G15, source resolution, a SourceSpec instance, or compiler adequacy.
The frozen P8a signatures are unchanged.

## Typed interface and behavior

`Solidity/Lowering/P8/CheckedSyntax.lean`, namespace
`Solidity.Lowering.P8.CheckedSyntax`, exports `Parsed`, `Parses`, `UnitCert`,
`Cert`, `checkUnit`, `checkUnits`, `check`, `parseChecker`, `candidate`,
`validate`, `produce`, `settingsB` and `rawB`.

`Parsed` carries all source-unit trees, the input settings and main selection.
The existing G05 resolver receives syntax, not input; units-only syntax loses
settings. `units_only_resolver_obstruction` proves that an inhabited parse and
resolution of the existing units-only spec contradict `SettingsRespected`.
Its only premises are that actual parse, resolution and settings-respect claim;
the concrete control supplies a checked parse of `contract C {}` under both
admitted pipeline settings. Empty resolvers are not claimed contradictory.

The new certificates carry exact lexical pieces and grammar layouts. Checks
use the existing `Lexed` relation on original bytes, token yield, precedence,
unit names, and exact settings/main equality. The existing lexer/parser only
produce candidates; `validate` rechecks every output. No digest substitutes for
source bytes. Kernel controls use explicit byte/piece/tree certificates, not
opaque producer evaluation or native decision shortcuts.

`checkUnit_sound`, `checkUnits_sound` and `check_sound` establish the independent
existing source grammar relation. `validate_accepted`/`produce_accepted` prove
returned candidates pass the check. `settings_recorded`/`main_recorded` preserve
input tags. `settingsB_iff`/`rawB_iff` decide exactly existing `Settings.Ok` and
`Input.Ok`. Parsing remains separate from raw admission: callers must require
both `rawB = true` and a checked parse before claiming raw-input admission.

Both pipelines accept the actual contract certificate; wrong pipeline, main,
source bytes, missing certificate, duplicate unit, nonpipeline order and
historical compiler controls refuse. All audited headlines use only propext,
or no axioms. No parser completeness/uniqueness proof, full resolution chain,
root coverage, SourceSpec realization or EVM execution is supplied.

## Checkpoint handoff

Published integration base `63d3f9232416629146ab2f0a40d756dc9be43845`.
The original freeze `8f59a2c7791d8844682ce64c48118dae2a1105a8` is preserved;
its rebased commit is `e079a1a69aa07fa8b7c3955d9d8dcd7a28256db4`, with the
frozen interface byte-for-byte unchanged. Revision is this document's commit;
the machine-readable handoff supplies the full SHA.

Per-file check: `timeout 300 lake env lean --tstack=131072 Solidity/Lowering/P8/CheckedSyntax.lean`,
exit 0, 2.05 seconds. Touched closure: `timeout 300 lake build Solidity.Lowering.P8.CheckedSyntax`,
exit 0, 21 jobs, 22.35 seconds, peak aggregate RSS 813457408 bytes. Both use
LEAN_NUM_THREADS=1, explicit -j1, hard 12 GiB/no swap and authorized 4 GiB host
reserve. Failed elaboration/control attempts are preserved separately.

Independent read-only finder and skeptic, neither using Lean/server/builds,
found no confirmed defect and required the parse-versus-admission boundary.
No full/end-of-lane gates were run for this turn under H12. The prior full run
interrupted for H12 remains nonpassing. VM evidence is
`/workspace/p8a-implementation-20261102-evidence`.

Remaining current P8a obligations: full execution/observation-root extraction,
actual resolution/metadata/settings chain and frontend completeness, source
operational references/adequacy, failure hooks and hash/slot-preimage tracing.
V16 retains P8b G01 Lowering dom/agrees/cert. S02-IMMUT, SS-CP5-HASHED and SS-NEW
remain queued; no goal reset or completion and no worker push/merge.
