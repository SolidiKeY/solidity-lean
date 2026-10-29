# Roadmap G07: proof/trust regression gates and contract controls

G07 closes wave 0 of [the roadmap](../coverage-plan.md) ("Establish
proof/trust regression gates, axiom inventories and inhabited
source-to-machine controls; record existing failures separately. Check that
malformed source, altered bytecode and always-revert output cannot satisfy the
planned contracts."). It is the first checkpoint of lane V03.

Base: `ceb0d54` with the roadmap-w1 branches `g00-manifest-rev`,
`g02-measure`, `g03-ledger`, `g05-frontend`, `g06-evm-interface` and
`g01-contracts-rev` merged (the G01 revision's document has a filled
`Handoff`). Restated against the final G01 revision (`12088f5`, after three
integration holds; see §6).

## 1. Contract controls (`Solidity/Roadmap/Controls.lean`)

G01's contracts (`Solidity/Roadmap/Contracts.lean`) are statements over
parameters. A statement can fail two ways: it can be unsatisfiable (no
compiler could meet it), or too weak (a wrong compiler meets it). The module
checks both on one small instance, kernel-checked, with `#guard_msgs` axiom
pins.

**Inhabited control.** `toySource` reads source bytes as one of three
programs: `0 d…` succeeds with data `d`, `1 d…` reverts with `d`, `2` loops.
Every other text is malformed. Inputs carry both pipelines, the pragma's ABI
coder and a link map, which must be empty. An exhausted source transaction
(its resource failure) reverts with empty data. A success hashes its data
(`Toy.hashes`), with G06's Keccak-256 (`Evm.withKeccak`) and sane one-slot
regions (`Fixed.Sane`). `toyEvm` decodes the selected unit's runtime bytes
the same way, whatever the gas, and hashes nothing. The intrinsic layer is
the source language, with an identity pass and its certificate (`idCert`).
`compilerWith f` writes the text of `f p` for the admitted program `p`.
`publicCorrectness_of_faithful` proves the public contract for every `f` that
refines in both directions (`Faithful`). Proved:

| Theorem | Statement |
|---|---|
| `toy_publicCorrectness` | `PublicCorrectness toySource toyEvm toyCompiler id toyExport` (`f = id`) |
| `toy_publicCorrectness_loopReverts` | the same for the compiler that turns the loop into `revert []`: accepted by design, see below |
| `toySource_nonVacuous` | `SourceSpec.NonVacuous`: success with data `[1]` (hashing `[1]`), revert with `[7]`, divergence, at every artifact table, in the forward bounds and under the hash premise |
| `toySource_approved`, `toyEvm_approved`, `toyFixed_keccak` | `SourceSpec.Approved`, `EvmSpec.Approved` (the Osaka pin `Evm.pinned`, sane regions, every bound admissible, precompiles fixed, `this` from deployment, values affordable) and `Fixed.Keccak` |
| `toyAdmission` | a sound and complete `Admission toySource` (a definition) |

**What the toy exercises, and what it does not.** It exercises coverage
(admitted inputs compile, malformed ones do not), both pipelines and the
recorded ABI coder, the empty link map, the outcome and its data in both
directions of refinement, divergence against exhaustion, and the
`NonVacuous` witnesses. Several fields hold only trivially:

- `decode_reach` and `decode_commutes`: neither layer lists boundary worlds;
- `creates_table`, `PrecompilesFixed` and `ThisFromDeployment` (inside both
  `Approved` conjuncts): the toy emits no events and creates nothing;
- `envOnto`, `session`, `fixed`: identities, and neither semantics reads the
  environment (no requests, callbacks, balances or credits);
- gas and horizons: the EVM semantics ignores its bound, and every prefix is
  complete at horizon 0;
- the hash premise: the toy hashes at most one preimage and no slot
  preimage, so the premise always holds; `HashPremise.not_of_rootSlots`
  shows the case where it cannot.

These need real programs and the concrete pipeline (G49.03). The toy is not a
correspondence claim about Solidity.

**Negative controls**, on the same source and EVM, for every intrinsic layer,
state export and environment map `envAbs`:

| Theorem | Refuted | Through |
|---|---|---|
| `not_publicCorrectness_revertCompiler` | output that always reverts | `PublicCorrectness.not_alwaysRevert` (G01), forward direction |
| `not_publicCorrectness_hashRevertCompiler` | output that reverts whenever the source hashes (every toy success hashes) | `PublicCorrectness.not_alwaysRevert`, through the hashing success that `NonVacuous` demands |
| `not_publicCorrectness_alteredCompiler` | correct bytes with one byte appended (`0 1` succeeds with `[1, 0]`) | `PublicCorrectness.observes` (new), forward |
| `not_publicCorrectness_erasingCompiler` | revert data erased | `PublicCorrectness.observes`, forward |
| `not_publicCorrectness_loopToSucceed` | a loop compiled to a success the source never produces | `PublicCorrectness.observedBySource` (new), backward |
| `not_publicCorrectness_sloppyCompiler` | malformed text (the empty input) compiled | `PublicCorrectness.rejects` (new), coverage |
| `not_publicCorrectness_linkBlindCompiler` | a pre-assigned library address ignored | `PublicCorrectness.rejects`, coverage |
| `not_admission_sloppy` | a frontend accepting malformed text | `Admission.rejects` (new) |
| `not_nonVacuous_emptySource` | a source whose grammar accepts nothing | `SourceSpec.not_nonVacuous_of_no_parse` (new) |

The malformed inputs proved refused are the empty text, an unknown tag
(`badTag_not_admitted`), data after the loop tag (`trailing_not_admitted`)
and a non-empty link map (`linked_not_admitted`).

The six new generic lemmas hold of every source, EVM and compiler:

- `PublicCorrectness.observes` turns any completion of an admitted source
  meaning in the forward bounds (no resource failure, fewer than `hashBound`
  distinct preimages) and under the source's hash premise into an EVM
  completion with the same outcome and events, assuming nothing of the
  bytes' hashes.
- `PublicCorrectness.observedBySource` turns any EVM completion up to whose
  observations the source does not collide (`NoCollisionUpTo`) into a source
  completion at an admissible bound.
- `PublicCorrectness.rejects` refuses non-admitted input, and
  `Admission.rejects` does the same for a sound frontend.
- `SourceSpec.NonVacuous.admits` and `SourceSpec.not_nonVacuous_of_no_parse`
  show that a source admitting nothing fails `NonVacuous`.

A source definition that admits malformed text (say `Parses := True`) is not
refuted by any contract lemma: rejecting it is S00's obligation (the grammar
as a relation, G08–G11), not something the contracts can check.

**Accepted by design: divergence may become a revert.** The source may let
any frame fail as if out of gas (G01 Q2 and the decisions' follow-up rows),
and `Admissible` includes these exhausted bounds. So a loop may compile to
`revert []` (`toy_publicCorrectness_loopReverts`). This is what an EVM does
when a loop runs out of gas. A loop compiled to a *success* is refuted.

**Contract gaps found by G07.** These are properties of
`Solidity/Roadmap/Contracts.lean` that no control on these contracts can
rule out. They are recorded for the G01 owners and are not changed here:

1. **The hash-premise layout was unbounded (closed by the final G01
   revision).** `HashPremise.not_of_rootSlots` proves that with
   `regionLen ≥ 1` and `rootSlots ≥ 2^256`, no run with a slot preimage
   meets the premise, so `refines` would constrain nothing after it. The
   final revision adds `Fixed.Sane` to both `SourceSpec.Approved` and
   `EvmSpec.Approved`, which excludes this (`Fixed.Sane.rootSlots_lt`); the
   premise is now the source's, so a compiler cannot make it fail either.
2. **The resource-failure semantics is unconstrained.** "A failing frame
   reverts with empty data and its caller continues" is a comment, not a
   field: `Failures`/`NoFail` say which bounds fail, not what a failure
   observes. A source whose failing runs may end in any outcome makes the
   backward direction vacuous. This is an S03.04 obligation.
3. **The EVM's observation fields are unconstrained.** `EvmSpec.created`,
   `worlds`, `balances` and `resume` are free fields (`hashed` is now
   constrained by `hashes_source`): `worlds := []`
   makes `decode_reach`/`decode_commutes` vacuous, as in the toy. These are
   pinning obligations of G06/G49.
4. **The table is read only as bytes** (G01 non-circularity part 4) is not
   checked mechanically. The toy's `meaning` ignores the table.

## 2. Gates

All gates run without Lean, in about 15 s, through one runner, which exits
1 only on a failure outside the baseline:

```
node scripts/check-g07.mjs [--log RUN_LEAN_LOG]
```

| Gate | Script | Rule |
|---|---|---|
| Trust lint | `scripts/check-trust.sh` (existing) | no `sorry`, axiom, `native_decide`, …; inventory unchanged |
| Layers, orphans | `scripts/check-layers.mjs`, `scripts/check-orphans.mjs` (existing) | core below the elaborator; every module built |
| Non-circularity | `scripts/check-noncircular.mjs` (new; tests `scripts/check-noncircular.test.mjs`) | G01's four-part gate, §3 |
| Axiom inventory | `scripts/check-axiom-pins.mjs` (new; tests `scripts/check-axiom-pins.test.mjs`; inventory `scripts/g07-axiom-pins.json`) | §4 |
| Doc paths | `scripts/check-doc-paths.sh` (existing) | its summary line present; no missing reference beyond the baseline (lines compared as multisets, backticks dropped so the baseline cites no path itself) |
| G03 ledger | `scripts/roadmap-g03-ledger.py --check` (existing) | its summary line present; no error line beyond the baseline |
| Control pins | `scripts/g07-baseline.json` (`requiredPins`) | each control and contract lemma of §1 keeps an axiom pin, so deleting a control fails the gate |
| Build log | `--log` on a `./run-lean.sh` log | no Lean error line except a baselined module's out-of-memory kill (`137`/`Killed`); at least one completed build; a SolKey mismatch count present and at most the baseline (by count only) |

The transitive Lean axiom audit stays `TrustAudit.lean`. G07 appended one
`run_cmd` block for 22 contract and control theorems: the G01 lemmas
`PublicCorrectness.transfer` and `not_alwaysRevert`, the six new generic
lemmas, `HashPremise.not_of_rootSlots` and 13 control theorems.

The mechanical checks that a malformed-source, altered-bytecode or
always-revert compiler fails are the Lean refutations of §1, checked by the
kernel at every build. The scripts keep them present (`requiredPins`) and on
the standard axioms. G07 adds no script that mutates a compiler and expects
Lean to fail, and no control on the current fragment's compiler
(`Solidity.Evm.Correct`) or frontend: those move to G49.03. Run it as
[assurance.md](../assurance.md) describes, or open it in the Lean server.

## 3. Non-circularity, mechanically

G01's gate ([roadmap-g01-interfaces.md](roadmap-g01-interfaces.md#non-circularity-as-a-checkable-gate))
has four parts. `scripts/check-noncircular.mjs` scans every Lean file on disk,
tracked or not, under `Solidity/`, `Bridge/`, `tests/` and the root (930
modules at this revision). Imports are read from comment-blanked headers,
every module of an `import` line included, `public`/`meta` modifiers allowed.
It checks:

0. **The contracts.** `Solidity.Roadmap.Contracts` reaches only
   `Solidity.Keccak` and defines no function into `Artifact`.
1. **Import whitelist.** A module under `Solidity/Source/`, or any module
   that instantiates `SourceSpec`, reaches transitively only
   `Solidity.Source.*`, `Solidity.Roadmap.Contracts`, `Solidity.Keccak` and
   the named datatype modules of `DATATYPES`. No non-Solidity import is
   allowed, not even `Lean`. Instances are found qualified or not: `: SourceSpec where`/`:=`,
   a `{ … } : SourceSpec)` ascription, `SourceSpec.mk`. `DATATYPES` is empty:
   no source module reuses an intrinsic type. An entry names its
   correspondence theorem, which must be declared in its file.
2. **No meaning through the pipeline.** Source modules name none of
   `IntrinsicSpec`, `Lowering`, `Compilation`, `Execution`, `StateExport`,
   `EvmSpec`, `PublicCorrectness`, `SpecTransfer`, `Pass`, `Cert`, `ofWorld`,
   `typedRunPrefixes`, qualified or not. Comments are blanked; string
   literals count. The other half of the part, that the constants
   `Lowering.lower` unfolds to use no source constant beyond the whitelisted
   datatypes, needs a Lean-side constant audit once a real lowering exists.
   It is left to G16.
3. **The EVM end, as a whitelist.** A module that instantiates `EvmSpec`
   reaches only `Solidity.Roadmap.{Evm,Contracts}`, `Solidity.Keccak`,
   `Solidity.Secp256k1` and the pinned-EVM modules of `EVM_MODULES`. It must
   reach `Solidity.Roadmap.Evm` or an `EVM_MODULES` module. `EVM_MODULES` is
   empty: the current machine `Solidity.Evm.Machine` imports the intrinsic
   semantics (`Solidity.Semantics`), so it cannot be the pinned EVM as it
   stands. G06/G46 add the pinned EVM's modules.
4. **The artifact table is a variable.** Rules 0 and 1 keep every
   `Solidity.Evm.*` module out of the source closure and every compiler out
   of the contracts. That `meaning` reads the table only as
   `creationCode`/`runtimeCode` bytes is not checked (§1, gap 4).

Control modules (`CONTROLS`: `Solidity.Roadmap.Controls`) build toy instances
of both ends and may import `Solidity.Roadmap.Contracts` only.

At this checkpoint, rules 1–3 apply to no module beyond the control: S00's
modules are the first source modules (§ handoff of
[source-s00-s01.md](source-s00-s01.md)). The script's tests
(`scripts/check-noncircular.test.mjs`) exercise every rule on synthetic
modules, including the evasions the review found.

## 4. Axiom inventory

`scripts/check-axiom-pins.mjs` reads every `#guard_msgs`-pinned
`#print axioms` (options form included) outside comments in `Solidity/`,
`Bridge/`, `tests/` and the root modules. It takes the doc comment that ends
right before the pin, keyed by file and name, so a theorem pinned in two
files counts twice. At this revision there are 324 pins: 275 on the three
standard axioms, 27 on `propext` alone, 8 on `propext` and `Quot.sound`, and
14 on none. Lean checks each pin's text when it builds the file. The script
checks the text itself:

- a pin naming `sorryAx` or any other non-standard axiom is an error, since
  `#guard_msgs` would accept it;
- the printed name must end with the `#print axioms` target;
- a recorded pin must stay, and its axiom set must not grow;
- a new pin, or a smaller set, is reported until
  `node scripts/check-axiom-pins.mjs --write` records it.

## 5. Existing failures, recorded separately

`scripts/g07-baseline.json` records the failures present at the base. They
are owned elsewhere and are not fixed here:

| Check | Baseline | Owner |
|---|---|---|
| `scripts/check-doc-paths.sh` | 46 missing references (the base count) | the citing documents' owners |
| `scripts/roadmap-g03-ledger.py --check` | 38 errors after the merges. The second-round decisions and the G01 revision have no G03 rows yet (`typedRunPrefixes` moved to `TypedRun.lean`, the gas-cap decision renamed). Five rows say that G07's schedule after G02–G06 is unacknowledged. The module acknowledgements are stale. | G03's script (its acknowledgement tables); G07 does not edit it |
| `./run-lean.sh`, `lake build SolkeyTestSuite` | `TestSuite.Derived17` killed for memory (exit 137) on a cold build | Codex TestSuite lane |
| `scripts/check-solkey.sh` | 37 mismatches | Codex lane |

The gate fails only on a failure outside these lists.

## Remaining obligations

- The constant-level half of non-circularity part 2 (§3) waits for G16's
  lowering.
- Event-level controls, controls on real programs and the concrete pipeline
  (G49.03).
- Per-family rejection controls for the 30 exclusions (G03 decision D01).
  S00's syntax classifies the syntax-level exclusions; admission controls on
  source text follow with G08–G15.
- The four contract gaps of §1, for G01 (bounds on the hash-premise layout),
  S03.04 (exhaustion semantics) and G06/G49 (EVM observation fields).
- A script that mutates the compiler and expects Lean to fail, and controls
  on the current fragment's compiler and frontend (G49.03).

## Review

A read-only finder and a separate skeptic reviewed the first push
(`5bbf24e`), neither using the Lean server. Their findings and what was done:

**Fixed**

- The runner failed at its own commit: the baseline file's entries contained
  backticked paths, so the doc-path check counted the baseline as new missing
  references. Entries are now stored without backticks and compared as
  multisets. The doc no longer cites a module that did not exist yet.
- Qualified names (`Solidity.Roadmap.Lowering`, `: Roadmap.SourceSpec where`,
  `({ … } : SourceSpec)`) evaded the instance and later-layer patterns. They
  now match qualified names, and tests cover each form.
- `import A B`, `public import` and indented imports were misread, and
  imports inside block comments were counted. Imports are now parsed from
  the blanked header.
- Only `Solidity/` was scanned. Now `Bridge/`, `tests/` and the root are
  scanned too.
- The EVM end was a denylist. It is now a whitelist, with a positive
  requirement to reach the G06 interface.
- Part 0 (the contracts' closure and "defines no compiler") was claimed but
  not checked. It is checked now, unconditionally.
- The negative controls fixed `envAbs := id`. They now hold for every
  environment map.
- `not_admission_sloppy` quantified over a possibly empty type. The
  inhabitant `toyAdmission` is added.
- No control exercised the backward (soundness) direction. A compiler mapping
  the loop to `revert []` met the contract unnoticed. Added
  `not_publicCorrectness_loopToSucceed` (backward, refuted) and
  `toy_publicCorrectness_loopReverts`, which states the accepted case
  openly.
- Malformed inputs covered only the empty text. Added an unknown tag,
  trailing data, a pre-assigned library address, and the link-blind compiler
  control.
- Claims were overstated: "every field" (the trivially held fields are now
  listed), "malformed source definition" (narrowed to a source admitting
  nothing), the `EvmSpec.Approved` summary, and the count of new lemmas.
- Baselined gates ignored their exit codes, and `--log` failed open. Both now
  require the summary line, a completed build and a SolKey count. A known
  out-of-memory module is exempt only on its kill line.
- The pin reader could take a doc comment several declarations above a pin,
  counted pins inside comments, collapsed duplicate names and skipped the
  options form. All four are fixed and tested.

**Recorded, not fixed here:** the four contract gaps of §1 (found by the
skeptic; `HashPremise.not_of_rootSlots` makes gap 1 a lemma). Others:

- SolKey mismatches are compared by count only, since `check-solkey.sh`
  prints no stable per-mismatch key in the log.
- The G03 ledger's stale G07 schedule rows are baselined rather than
  acknowledged, since the acknowledgement tables are G03's.
- No mutation script and no control on the current fragment exist (§2).

## Handoff

- **Base:** `ceb0d54`, with six roadmap-w1 branches merged (`544b6d7`);
  G07 is commits `5bbf24e` and `119ee49`.
- **Done:**
  - controls: the inhabited control (`toy_publicCorrectness`), its
    accepted divergence-as-revert variant, and seven negative controls
    covering always-revert, altered bytes, erased data, a loop compiled to a
    success, malformed text, an ignored link map, and sloppy admission, with
    four malformed-input refusals;
  - lemmas: six generic contract lemmas and the hash-layout gap lemma;
  - gates: the non-circularity gate, the axiom-pin inventory, and the
    baselined regression runner with existing failures recorded separately;
  - TrustAudit: an appended block of 22 theorems.
- **New theorems:** `PublicCorrectness.observes`,
  `PublicCorrectness.observedBySource`, `PublicCorrectness.rejects`,
  `SourceSpec.NonVacuous.admits`, `SourceSpec.not_nonVacuous_of_no_parse`,
  `Admission.rejects`, `HashPremise.not_of_rootSlots`, and the controls of §1.
- **Checked:**
  - `lean_diagnostic_messages` on `Solidity/Roadmap/Controls.lean`: no
    messages; every `#guard_msgs` axiom pin holds (`[propext]`,
    `[propext, Quot.sound]` or none). No `sorry`, axiom, `native_decide`,
    `implemented_by` or `maxHeartbeats` change.
  - `node scripts/check-g07.mjs --log <build log>`: 0 new failures. It runs:
    - `check-trust` (0 findings), `check-layers` (160 core modules, 0 reach
      the elaborator) and `check-orphans` (0 orphaned);
    - `check-noncircular` (0 violations) and `check-axiom-pins` (0 errors);
    - the script tests (11 pass);
    - `check-doc-paths`: 46 missing, all baselined;
    - the G03 ledger: 38 errors, all baselined;
    - the build log: both builds completed, SolKey 37 mismatches (the
      baseline).
  - `./run-lean.sh` (warm, after `cccc108`): `lake build` "Build completed
    successfully (727 jobs)"; `lake build SolkeyTestSuite` "Build completed
    successfully (262 jobs)", `TestSuite.Derived17` included this time;
    `check-solkey.sh` "37 mismatch(es)", the baseline, so the script exits
    1 as at the base. 8 min 18 s. The cold build before it (40 min 46 s)
    failed only at the root `Solidity.lean`, which was edited mid-build.
  - `TrustAudit.lean` in the Lean server: "trust: 22 roadmap control
    theorems use only the standard axioms" (and the first block's 544
    headlines pass).
- **Remaining:** see [Remaining obligations](#remaining-obligations); the
  four contract gaps of §1 go to G01's owners.

## 6. Restatement against the final G01 revision

The G01 revision was held back three times at integration, first because
`refines` could not be met for long sessions and because unconstrained
region parameters let an always-reverting compiler through. The final
revision (`12088f5`, merged here with `git merge --no-ff`) changes:

- `Forward` is `NoFail ∧ distinctCount < hashBound`, and `Guard` is
  `HashPremise` on the source's preimages; `Collided` no longer needs
  `Forward`;
- `Fixed` wraps G06's `Evm.Fixed`, and the coder is per unit;
- `EvmSpec` has `pin`, its premise and forward restriction are trivial, and
  `RunCollisionFree` is gone.

Restated:

- **The toy.** It now hashes a success's data, so `NonVacuous`'s hashing
  success is exercised.
- **Generic lemmas.** `observes` takes the source's forward bound and
  premise, and `observedBySource` takes `NoCollisionUpTo`.
- **New control.** `not_publicCorrectness_hashRevertCompiler` refutes a
  compiler that reverts whenever the source hashes.
- **Gap 1.** It is now closed by `Fixed.Sane`, and the lemma is restated
  over slot preimages.

The non-circularity gate allows `Solidity.Hash.CollisionBound` and
`Solidity.Roadmap.Evm`, both statements-only modules that the contracts now
import (`CONTRACT_DEPS`).
