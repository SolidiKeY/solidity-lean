# P8a actual program-container extraction

This checkpoint extends the local typed observation visitor to every
expression-bearing container of the carried `Source.Program`. It does not
complete G15 or construct SourceSpec/Failures. The H12 frozen module is
byte-identical; new signatures are additive.

## Typed interface and claims

`Solidity.Frontend.Admission.ProgramObservations` exports:

- `bodyObservations`: body items and all modifier argument expressions;
- `declarationObservations`: carried declaration body and constant initializer;
- `contractObservations`: constructor body/modifier arguments, state-variable
  initializers and base-constructor argument expressions;
- `programObservations`: scans every `E.decls` entry and every `P.contracts`
  entry, preserving order and duplicates without recursively unfolding calls;
- `ProgramSite` and `program_observation_iff`: exact occurrence iff for these
  actual Program fields over their finite rosters;
- `programModifierTargets`/`modifier_target_iff` and
  `programBaseTargets`/`base_target_iff`: exact modifier declaration and written
  base-name identity scans, separate from observation/profile classification.

The six inclusion lemmas cover actual body/modifier argument/constant/
constructor/initializer/base argument lookups. `accepted_program_iff` transfers
local observation-site admission over the exact container relation.
`target_body_covered` requires both actual target membership in `E.decls` and
a successful `P.body` lookup; it does not assume that local call acceptance
implies a callee exists. Scanning all carried declarations covers recursive
cycles without a fuel bound once those premises hold.

`elaborated_constructor_in_declarations` uses the existing actual
`Elaborated.ctor_typed` theorem field to show each carried constructor body
also occurs in the environment declaration scan. No arbitrary constructor
origin is assumed.

## Controls and boundaries

The typed control Program has seven ordered observation occurrences across
body, modifier arguments, constant, constructor body/modifier arguments,
initializer and base arguments. Exact modifier/base target lists are retained.
The constructor occurrence explicitly witnesses the constructor side of the
relation. Body-only collection, omitted contract roster, and missing body
expectations are kernel-refuted. These are inhabited `Program` controls;
they do not claim the deliberately synthetic carrier is `Elaborated`, imported
Solidity, an executed source program or a SourceSpec witness.

Remaining: prove all executed dispatch/modifier/constant/construction targets
resolve into these rosters; cover types, all features and specification
observations; connect the extraction to the frozen independent root model;
finish settings/resolution/public compiler correspondence and operational
failure/hash semantics. No feature/exclusion/profile definition changes.
The existing local visitor is not claimed to be an independent operational
occurrence relation. No whole execution-root coverage follows from this
container theorem alone.

## Checks, provenance and handoff

Base: published `0862c0f533dde084b398ff808894f69ff7d35931` fetched before
starting. Its source/P8/Roadmap frontend interfaces are unchanged relative to
prior base `63d3f9232416629146ab2f0a40d756dc9be43845`; no replacement P8a work
was present. The original sealed `5373e7292e3fd65bd95afb90639ad57c20c8bdc0`
checkpoint remains under `refs/recovery/p8a/schema-5373e729`; its exports and
all prior evidence remain immutable. Private rebase retained published
runtime-frame imports and module-map additions. No default branch edits.

`timeout 300 lake build Solidity.Frontend.Admission.ProgramObservationControls`
passed 19 jobs, 2.056 seconds, peak aggregate RSS 379383808 bytes. The new
module and controls checked in 0.508/1.0 seconds respectively. All printed
headlines use only propext, Classical.choice and Quot.sound; no new axioms,
sorry, native decision shortcut, statement weakening or raised budget.
Failed elaboration/control attempts remain failed under distinct labels.

Lean 4.24.0/Lake 5.0.0-src+797c613, LEAN_NUM_THREADS=1, explicit -j1,
hard whole-build-group 12 GiB, no swap, authorized 4 GiB host reserve.
Per-file Lean MCP is unavailable; the touched module closure is the native
fallback. H12 defers full end-of-lane gates; this focused pass is not a full
build, combined TrustAudit, TestSuite, corpus or EVM adequacy pass. Historical
full interruption and documentation failures remain nonpassing.

Independent read-only finder and skeptic used no Lean/server/builds. Findings
fixed: isolate constructor-side control; preserve modifier/base target
identities. Source, commands, terminal receipts, measurements, reviews and
checksum-bound cumulative artifacts are recorded in the machine-readable
handoff for this document's commit. Evidence directory:
`/workspace/p8a-implementation-20261102-evidence`.

Producer remains P8a (G15 + S05-SPEC/S03-FAILURES), consumers V07/V08/V09/V16/
V17/VY5. V16 owns P8b/G01. S02-IMMUT, SS-CP5-HASHED, SS-NEW remain queued.
No persistent goal reset/completion, publication or controller integration is
claimed by this partial checkpoint.
