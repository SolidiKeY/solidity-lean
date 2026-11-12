# Parallelism: layers, files and theorems

How the package is cut so that Lake checks it in parallel and an edit
rebuilds little: the core apart from the elaborator (P1), large files split
by topic (P2), one soundness file per new rule (P3); the closer's clauses
stay one function (P4).

The tools: `node scripts/import-fanout.mjs` prints each module's rebuild
fan-out (how many modules import it transitively) and the longest import
chain, `--path A B` one import path from `A` to `B`;
`node scripts/check-layers.mjs` fails when a core module reaches the
elaborator or introduces an unapproved core-to-non-core import boundary.

Audits (2026-11-06): [architecture](audits/architecture.md) (layering, copies, Controls cost), [build-speed](audits/build-speed.md) (where check time and memory go) and [coordination](audits/coordination-process.md) (lane time, gates, merge latency).

## P1. The core apart from the elaborator

### The core

`CORE` in `scripts/check-layers.mjs` is the authority; by family:

- `KeySort`, `Eqns`, `AST`, `Scope`, `SpecSyntax`, `Hashes`, `Keccak`,
  `ERC7201`, `Secp256k1`, `TypeGraph`, `RevertBytes`, `Syntax`, `Signature`,
  `Update`;
- `Syntax.{Raw,Grammar,Contract,Scoped,Checked,Inlined,PushSource,Join}`;
- `Semantics` and `Semantics/**`, `Typing/**`, `Theory/**`;
- the rules: `Calculus.{Fml,Rules,RuleSyntax,RuleKit,KeyTaclets,Step,Arms,
  Blocks,Taclet,Proves,Logic,Preconditions,FiniteMembership,FilteredMembership,
  Hyp,Correct,FirstOrder,Transient,Lifetime,ContractWorld,PaymentWitness,
  PaymentConditions}` and `RuleSyntax`'s pieces;
- their soundness: `Calculus.{Sound*,StmtSound,ProvesSound,PremiseSound,
  UpdRuleScoped,UpdateRules,TermLib.Rules}`;
- what those import: `Calculus.{TermEval,TermEq,TermWk,LoopInvariantWk,Lower,LowerRun,Shift,
  WkOver,Lands,StateFacts,ReadWrite,DataIn,SeqRewrite,SyntaxSize,Graft,
  CallSummary,KIntTwoAnchors}`;
- static callback transport: `Calculus.StaticInvocation`; the typed Boolean
  loop, nominal-view inventory and selfdestruct binding checkpoints under
  `Yul/` are registered by exact names in `CORE`.
- intrinsic sharing/join foundations: `Calculus.{AnonLocalCapture,CallResultCapture,
  CallResultRestore,JoinSequence,JoinSequenceSize}`.
- the hash bound and hashed layout: `Hash.{CollisionBound,Adaptive}`,
  `Storage.{HashedLayout,HashedKeccak,HashedSeparation}`;
- the backend: `Backend.{Opcode,Jumpdest,Assembler,Control}`.

`Tools.SolCases` is an external-source printer and is explicitly included in
the forbidden frontend set checked from the core.

The list is meant to be closed under imports. The architecture audit
(`cloud/audit-20261106/architecture`, fa5acebd43214bbe642258d862f903bcf08d3f89)
found 95 direct core-to-non-core boundary edges. Those exact edges are pinned in
`scripts/core-import-baseline.json`, SHA256
`d202b21ddde800b40237b9c4a95482c17b8d5ea8d2c78c1b42e4bad7344ac80b`
(enforced by `scripts/core-import-closure.mjs`). Reproduce the audited
bytes with `python3 -B scripts/h62/item5/statement-graph/audit_core_baseline.py`.
They are existing debt, not proof that the core is already closed.

The authorized OT-W0-TOOLING follow-up re-pins current master
`fea090bf9fec1a372ad32952a5e72eb4d7015888` at **107** boundary edges.
`scripts/core-import-current-baseline.json` contains that full snapshot and the
12 additional edges, each attributed to its verified import-introduction commit;
its SHA256 is `880486dcbe8f1004449dc9f1d90f25a9964d0b2c5ea64dad3de3dd5cfc548b8d`.
Reproduce it with
`node scripts/h62/item5/statement-graph/reproduce_core_baseline.mjs`.
The original 95-edge snapshot remains immutable. The twelve are cleanup candidates,
listed in [the tooling handoff section](../scripts/h62/item5/statement-graph),
not a declaration that the package is closed under imports.

`scripts/check-layers.mjs` now checks the Solidity-package import closure as well
as the existing elaborator/parser restrictions. It follows paths through core
modules and rejects each new boundary to a non-core module, printing a witness
path. Paths through a pinned boundary are grandfathered; the downstream modules
are not promoted into CORE. This is a boundary-edge policy, not a baseline of
all transitive module pairs. Standard Lean library imports remain outside this
package-layer graph. The scanner handles comments, indented imports, and multiple
modules on one import line; unsupported quoted or multiline import syntax fails
closed. Existing elaborator/parser bans still apply even to an allowed edge.

The active subset is the union of `scripts/core-import-allowlist.json` (original
95) and `scripts/core-import-additions-allowlist.json` (authorized twelve). Each
component has independent permanent shrink-only history; an original edge cannot
be moved into the additions to restore it. Remove obsolete entries when fixing
debt. Both can only shrink: additions outside the audited set, duplicate
edges, re-adding a previously removed edge, and delete/recreate histories are
rejected. Validation checks committed change history and the working tree;
shallow histories, grafts and custom history overrides are refused. The immutable
95-edge and current 107-edge snapshots and their checksums must not be enlarged
to silence a later failure. No further allowance is authorized by this re-pin.

The merge pre-gate `bash scripts/coord-tools/gate.sh touched` runs the layer check
first and fails before invoking a build. Run it on the prospective merged tree
before committing/publishing the merge. Checkpoint/full modes use the same
preflight; per-file diagnostics remain unchanged.

The elaborator is `Syntax/{Elab,Quote,Splice}` and
`Calculus/{Print*,Surface*,TacticSyntax,Quote,NamedTerm}`. Source extraction for
the core's composed models stays above it (`Frontend/WorldImport`,
`Examples/Tactics/TransientStorage.lean`).

**A new module** that only states or proves (no `sol{}`, `dl!{}`, `#wp`,
`#guard_msgs` of a printer) belongs in the core if what it imports is: add
it to `CORE` when its name is not matched already (the checker names core
modules exactly).  Examples written in the surface syntax go above, in
`Examples/`; a core module's `sol[C]{…}` examples live in
`Examples/ScopedRuns.lean`.  The core's `dl{}`/`tm{}` macros sit below the
elaborator; `Prog.join` is in `Syntax/Join.lean` and the term taclets'
rules in `Calculus/TermLib/Rules.lean` (printers in `TermLib.lean`) for this
reason.

## P2. Large files split by topic

A file over ~1800 lines becomes a directory of pieces of at most ~1500
lines, cut at its own `section`s and topic headers, each piece importing the
one before; the file itself is the umbrella that imports them all, keeping
its docstring and naming its pieces.  A piece restates the file's
`namespace`s, `open`s and file-level `variable`s; a section cut in two is
closed and reopened with its `variable`s.  No declaration changes name.
Generated files (`Corpus/TestSuite`) are split in their generator, if at all.

The gain is the memory of a worker and the size of what an edit re-checks,
not fan-out (every importer reaches the last piece anyway).  A chain of
pieces costs about a second per piece more than the whole; measured on the
2026-10-24 splits, no piece and no downstream file got slower, and the
largest workers fell (`Calculus/Closer` 3.2 → 2.0 GB, `Calculus/MemRead`
2.9 → 2.1 GB).  `tests/trust-inventory.json` (`scripts/check-trust.sh`)
names pieces, so a split updates it.

A file split for **time**, not size, is cut differently: its definitions
stay in the file its importers already name, and its checks (`#eval` pins,
`decide +kernel` coverage) move to sibling pieces that each import it and
nothing imports, so they build in parallel and off the importers' path.
`Examples/Decision.lean` was split this way (2026-11-02; times in
`docs/automation.md`, M7-next).  A module whose time is one declaration
(`Examples/Tactics/OpenLoops.lean`'s `binomialRowsNine`) gains nothing from a
split.

**Pitfalls.**

- *A matcher is shared only within its module.* `Semantics/Storage`'s
  `match` twins (`SVal.find_at` …) state a `match` that is, by `rfl`, the
  matcher `SVal.findM` unfolds to: Lean reuses one auxiliary matcher for
  equal `match`es in a module, not across modules.  Cut between the
  definitions and their twins, the `simp only [findM]` steps leave
  `match … = match …` with two matchers.  The cut moved so that
  "Find and save" and the twins are one piece (`Storage/Ops`).
- *A narrowed import can drop a name the importer used transitively*:
  `Calculus/SurfaceNotation` used `synth` and `Calculus/SurfaceSpec`
  `elabStmtsP` through `NamedTerm`'s old `Syntax.Elab` import.  Each now
  imports the piece it uses.  A narrowing is safe only when the pieces it
  drops register no instance, macro or delaborator the importer's output
  reads; `RuleSyntax/Print` holds the delaborators, so no importer of
  `RuleSyntax` is narrowed.
- *The layer check names core modules exactly*: the pieces of `Syntax` and
  `RuleSyntax` are added to `CORE` (those of `Semantics/Storage` and
  `Theory/Typed/Obs` were matched already), 123 modules now.

## P3. Theorems: one lemma per rule

Statement-rule soundness is one lemma per `Stmt.step` arm
(`Calculus/SoundArms.lean` … `SoundLoops.lean`), dispatched by
`Calculus/SoundStep.lean` (`Stmt.stepSound_arms`) and
`Calculus/StmtSound.lean` (`Stmt.stepSound`, the blocks), each one
`cases s`.  A new rule proves its arm in `Calculus/Sound/<Arm>.lean`, one
file per new arm (`Calculus/Sound/README.md`; the template is in
`.claude/rules/soundness.md`), so that it elaborates alone.  Each
`TermTaclet.sound` case (`Calculus/TermLib/Rules.lean`) applies a named lemma
`TermTaclet.<rule>_sound` or is one term.

### Adding a rule: the six places

0. **Start** from `docs/rule-repair.md`: the gates before integration.
1. **The constructor**: `Taclet` in `Calculus/Rules.lean`, written in
   `dl{ … }` (`.claude/rules/rule-table.md`, step 1), its labels kept equal
   to `Taclet.branchLabels` (`Calculus/RuleKit.lean`).
2. **Its `Stmt.step` arm**: `Calculus/Arms.lean` or `Calculus/Blocks.lean`,
   dispatched by `Calculus/Step.lean`, with `Taclet.<rule>.toStep`
   (`Calculus/Taclet.lean`) and, where the arm is new, `Stmt.<c>.ruleExists`
   (`Calculus/RuleExists.lean`).
3. **Its soundness**: a new arm's file `Calculus/Sound/<Arm>.lean`; a taclet
   added to an existing statement extends that statement's `…Step_sound`
   where it is (`Calculus/SoundControl.lean` …).
4. **The assembly line**: an import and a case in `Stmt.stepSound_arms`
   (`Calculus/SoundStep.lean`), or in `Stmt.stepSound`
   (`Calculus/StmtSound.lean`) for a block.  The `cases s` is exhaustive:
   a statement whose arm has no lemma fails the build.
5. **The rule map row**: `docs/lean-key-rule-map.md`, the solkey taclets it
   transcribes and the file of its soundness.
6. **The printed tables**: `RuleShapes.tacletOrigins`
   (`Calculus/RuleShapes.lean`) and `PrintedRules.printedOrigins`
   (`Calculus/PrintedRules.lean`); `#check_constructor_table` fails on a
   missing row.  A taclet that reads storage or memory also gets its row in
   `SortCheck/Annotations.lean` (`solidity-lean rules check` compares it with SolKey's rules on demand; no gate runs it since H89).
   `taclets_partitioned`/`printed_rules_partitioned` and the claimed and
   unclaimed counts move with the rows.

A new statement form is a larger change than a rule: the syntax, the run,
the typing, the EVM, the quoters and printers (`Syntax/Quote.lean`,
`Calculus/Quote.lean`, `Calculus/PrintStmt.lean`) and `Stmt.isBlockArm`.

## P4. Closer clauses stay one function

`LFml.close` is one `Bool` on purpose, chosen for speed:

- the closer is the reflective half of `sol_prove` (`docs/testsuite-proofs.md`,
  M1 and M4, `3fc9bb4c`): one kernel evaluation runs the strategy and the
  closer per obligation, a leaf costing 50–60 ms and under 1k heartbeats in
  one `decide`, against ~600 ms and 18k heartbeats per leaf
  for a tactic proof of the clauses.  A KeY taclet is a clause of that function,
  not a proof step, so that it costs the kernel one evaluation, not a proof;
- the functions the kernel evaluates keep Gate G0's forms
  (`docs/intrinsic.md`, M0; `docs/kernel-port.md`): recursors and
  `casesOn`, with a `match` twin for compiled code, because a `match` on a
  context-indexed family costs the kernel a context comparison per cast
  (11–13× on symex).

Clauses as records folded over a list would change what the kernel unfolds
on every leaf (structure projections and the fold, on top of each clause),
the cost that design avoided, so the prototype was not written.  Changing
it is the closer owner's decision, gated on measuring
`Calculus/CloseTests.lean`, `Examples/Tactics/Decide.lean`, two
`TestSuite/Derived*` modules and the whole `SolkeyTestSuite`.

### Yul parser boundary

The core Yul preparation modules retain intrinsic certificates and checker laws.
Source parsing composition lives in Frontend/Yul; the layer gate also forbids
transitive paths from enumerated core modules to these adapters and to
Frontend.Checked.Check or Frontend.Checked.Parser. The existing lexer and pure
structural precedence predicate remain reusable prerequisites. Dedicated legacy
Yul parser modules are compatibility imports outside the core.

## P5. Build and integration throughput

Changes to how the package is built, registered and relayed to the lanes
(decision H21, 2026-11-03), each measured before and after.  Host times are
wall clock on 32 cores with Lake's artifact cache warm; "rebuilt" counts
Lake's `Built` lines.  A probe edit appends `theorem h21Probe… : True :=
trivial` to `Calculus/Close.lean` (it and its dependents: 414 modules, 205
of them examples, 49 TestSuite modules and its root), a different name each time so that nothing
comes from the cache.

### One Lake invocation

`run-lean.sh` builds the default targets (read from `lakefile.toml`'s
`defaultTargets`) and `SolkeyTestSuite` in one `lake build`, so the
TestSuite's chain (the memory-loop `Discover` modules, `Derived17`, `Report`)
runs beside the default build's tail instead of after it.  The targets are
the union of the two former calls; the exit is Lake's, under `set -e`, as
before (a failure in either set fails the script, and Lake now also reports
the other set's failures in the same run).  Lake's job limit and
`LEAN_NUM_THREADS` apply as before.  The work is the same, so a VM building
with one or few workers gains little; not measured there.

| Probe edit | Rebuilt | Lake wall |
|---|---|---|
| two calls (before) | 364 + 50 | 606.7 + 249.4 = 856.1 s |
| one call (after) | 414 (the same modules) | 697.6 s (−158.5 s, −18.5 %) |

The one-call run shared the host with another session's Lake build (two
other Lean/Lake processes at its start; the two-call run had none), so the
gain is if anything understated.

### Shared registries

The library roots are generated: `scripts/coord-tools/register.sh` writes
`Solidity.lean`, `SolidityExamples.lean` (since the next section),
`Solidity/Goals.lean` (every goal module, so each goal step adds its own file) and
`Bridge/SolidityBridge.lean` from the file tree, each importing every module
under its prefix, sorted, minus other libraries' subtrees (`Examples/`,
`Corpus/`, `TestSuite/`, `Solkey/TestSuite.lean`) and `Scratch/`.
The generated `Solidity.lean` imports exactly the closure the hand-kept one
reached (3487 modules at d7b05d68c; 3048 direct imports before).  `register.sh --check`
fails on a stale root; `run-lean.sh`, `gate.sh checkpoint|full` and CI
(`lean.yml`) run it.  `.gitattributes` merges the roots with `merge=union`,
so a rebase rarely stops on them.  A union keeps both sides of overlapping
hunks, so it can bring back a deleted module's import or leave the list
unsorted without any conflict reported; only `--check` catches that, so run
`register.sh` after every rebase or merge.  A lane runs `register.sh` after adding,
moving or deleting a module and commits the result; the integrator drops the
lanes' root hunks and regenerates.

`docs/module-map.md` is an index; the rows are in one file per area under
`docs/module-map/` (its former `##` sections, contents unchanged).
`scripts/coord-tools/module-map.py BASE` lists the modules added since BASE
without a row and proposes the fragment and a row (the integrator's former
`mmrows`/`mmplace`).

The other shared bookkeeping files are generated too, from a fragment
directory next to each: `docs/module-map.md` from `docs/module-map.d/`, each
`docs/module-map/<area>.md` from `docs/module-map/<area>.d/`,
`docs/README.md` from `docs/README.d/`, `TERRA-TODO.md` from `TERRA-TODO.d/`
and `scripts/g07-axiom-pins.json` from `scripts/g07-axiom-pins.d/`.
`scripts/coord-tools/fragments.sh` writes them; the combined files stay
committed (scripts and `git show REV:path` read them).  A Markdown file is a
marker line followed by its fragments concatenated in bytewise path order:
`00-base.md` holds the migrated text, a lane adds `<lane>.md` (lower-case
branch name), `~tail.md` sorts last, and a subdirectory such as
`docs/README.d/10-language/` is a slot inside the file (the language table).
The pin inventory has one fragment per Lean file,
`scripts/g07-axiom-pins.d/<path without .lean>.json`;
`check-axiom-pins.mjs --write` rewrites them with the combined file.  A lane
edits only its own fragments and runs `fragments.sh`, so two lanes never touch
the same lines.  `fragments.sh --check` (run by `gate.sh`, `run-lean.sh` and
CI) fails on a stale combined file; the write refuses lines in a combined file
that no fragment produces (a direct edit) unless `--force`.  The Markdown
combined files merge with `merge=union` (the pin inventory does not: a union
of JSON is not JSON); after any merge or rebase run `fragments.sh`.
`fragments.sh --resolve [--lane NAME]`, during a conflicted two-parent merge
or right after a merge commit, regenerates every combined file and the roots
and stages the result; it exits 1 while a path stays conflicted.  A side that
has fragments is taken from its fragments (its combined file may be stale);
only lines none of the merged fragments has are adopted, into
`<slot>/<lane>.md`.  A side that predates the fragments has its direct edits
adopted: a replaced block found once is edited in place in the fragment that
holds it, a deleted line found once is removed, inserted lines go to
`<slot>/<lane>.md` (so they land at the end of their slot), and pins merge by
key.  After a rebase or a fast-forward there is no merge to read; run
`fragments.sh` and move the lines it refuses into a fragment.  The pre-gate
service runs `--resolve` on merges whose only conflicts are in these files,
their fragments or the roots, and records them as `auto_resolved`.

Measured on the history since 2026-10-27 (non-merge commits): 214 touched
`Solidity.lean`, whose hunks are now regenerated instead of merged.  269
touched `docs/module-map.md`; of their 36,046 pairs, 3,613 (10.0 %; 738 of
the 6,912 concurrent pairs) edited the same section.  Edits in different
sections rarely conflicted before either, so the split mainly shortens the
file a lane reads and edits; it removes few module-map conflicts.  Rebuilds:
every added, moved or deleted module now edits the root and rebuilds it
(`Built Solidity`, 1.5–4.3 s); before, only those imported directly did.
Only `scripts/AxiomAudit.lean` imports the root.  A rebase can still stop on
a modify/delete conflict of a root; `register.sh` resolves it.

### Catalog data and the decision examples' definitions off the hot paths

`Language/Features.lean` (generated by `scripts/solidity-feature-audit.py`)
keeps what the frontend reads: the `Feature` type, `Feature.scope`,
`Feature.requirement`, the exclusions and the profile.  Each feature's
inspection record (`Feature.info`: status, upstream source lines, local
evidence), the status lists, `Feature.info_scope`/`info_requirement` and the
two consistency theorems (statements unchanged; the light module's filters
and `Unmodelled.reason` now read `Feature.scope`/`Feature.requirement`, equal
to the old reads by `Feature.info_scope`/`info_requirement`) are the
generated leaf `Language/FeatureInfo.lean`.  `--check` covers both.  A
requirement-text, scope or new-feature edit still rebuilds the frontend's
dependents (20 of the 34 past commits to the catalog); an upstream-line or
evidence edit (the other 14, about 40 %) no longer does.

`Examples/DecisionHashes.lean` keeps its formulas and imports `Names` from
the new light `Examples/Tactics/HashingNames.lean` instead of the hashing
examples; its checks (15 pins, 14 theorems, same names and statements) are
the leaf `Examples/DecisionHashesChecks.lean`, the time split of P2.
`Examples/DecisionFeatures.lean` now imports `Tools/Common.lean`, which it
had reached through `Tactics/Hashing`.

| Probe | Rebuilt before | Rebuilt after |
|---|---|---|
| a source line in `docs/solidity-features.json`, regenerated | 196 (199 dependents; 193 built, 3 killed by the host's OOM killer while another session built) | 2 (`FeatureInfo`, the root), 10.4 s |
| a theorem appended to `Examples/Tactics/Hashing.lean` | 15, 365.2 s (the `Decision*` chain after it) | 2 (`Hashing`, the root), 68.2 s |
| the `Calculus/Close.lean` probe: Lake wall | 416, 672.9 s (`DecisionGaps` last, at 667.9 s) | 417, 609.6 s (−63.3 s, −9.4 %; `OpenLoops` last, at 604.6 s) |

The `Close` and `Hashing` probes ran on a host with no other build (the
features probe before did not, so only its count is given).  `Decision`
finishes at 354 s instead of 537 s; the tail is now `OpenLoops`' single
declaration (P2).

### The examples as their own library

Most `Solidity/Examples/` modules are in the default library
`SolidityExamples` (generated root `SolidityExamples.lean`). Human decision
H109 reverses the earlier choice to put every worked chain in the default
build: `SoliditySlowExamples` is non-default and is built in CI and by
`run-lean.sh` / `gate.sh full`, not by checkpoints. It contains OpenLoops,
RevertData, and DecisionGaps with its eleven transitive example importers:

- `Solidity.Examples.DecisionGaps`
- `Solidity.Examples.DecisionAPF`
- `Solidity.Examples.DecisionBlocks`
- `Solidity.Examples.DecisionGapCore`
- `Solidity.Examples.DecisionGapHashes`
- `Solidity.Examples.DecisionGapKInt`
- `Solidity.Examples.DecisionLedger`
- `Solidity.Examples.DecisionOperators`
- `Solidity.Examples.DecisionRefutations`
- `Solidity.Examples.DecisionResidue`
- `Solidity.Examples.DecisionStorageArrays`
- `Solidity.Examples.DecisionThreeKindCoverage`

The other two slow entries are `Solidity.Examples.Tactics.OpenLoops` and
`Solidity.Examples.Tactics.RevertData`. Their statements and imports are
unchanged. The checkpoint touched-closure omits this slow set even on a core
change; full validation builds it explicitly. `scripts/AxiomAudit.lean`
imports both example roots so CI retains its axiom audit.

| Probe: a theorem appended to `Frontend/Source.lean`, `gate.sh checkpoint` | Built | Build gates |
|---|---|---|
| before: `build-touched` at `LEAN_NUM_THREADS=1`, then `run-lean.sh` | 170 + 2 | 1476 s + 4 s (its run-lean stopped at the known solkeycheck drift) |
| after: `build-touched`, then `lake build Solidity` | 66 + 1 | 188 s + 2 s |

The saving is the `build-touched` gate: 1476 → 188 s (−87 %).  The 104
modules no longer built at the checkpoint are 53 examples, 50 TestSuite
modules and `Corpus.Imported`.  A checkpoint that does not touch the core no
longer checks the examples, the TestSuite, the executables or the SolKey sort
check; those wait for `run-lean.sh` at the lane's end.  Examples have broken
after `Tools`/`Frontend` edits before (4a7632415), so a lane editing those
should set `GATE_EXAMPLES=1`.

### Master's artifacts relayed to the lanes

After a scheduled merge the coordinator runs
`scripts/coord-tools/ship-cache.sh CHECKOUT` on the integration checkout
whose gates just passed at `origin/master`.  Lake 4.24's artifact cache is
content-addressed (`artifacts/<hash>.olean|ilean|c|o`) and indexed by input
hash (`inputs/<package>.jsonl`); the integration build writes the host's
under `~/.elan/toolchains/leanprover--lean4---v4.24.0/lake/cache` (112 GB;
`~/.cache/lake` is another tool's), and a VM's is
`$XDG_CACHE_HOME/lake` = `/workspace/.setup/cache/lake` (no elan there).  The
script reads each module's trace (`depHash` = input hash, `outputs` =
artifact hashes) in the checkout, keeps those whose outputs are cached, and
for each active lane ships, zstd-packed and sha256-checked, exactly the
artifacts that VM lacks (the shared pack is the delta against the previous
shipment), then appends the input lines the VM lacks under Lake's own lock.
Nothing is overwritten: a pack is extracted into a staging directory,
checked file by file, and moved in with `mv -n`.  A VM short of disk for pack + contents + 2 GiB is
skipped and listed.  A VM with the Bridge's Mathlib checkout at the host's
pin but no Mathlib build gets the `lake exe cache` files it lacks.  Lanes need no extra
step: after `git fetch` and a merge of master, `lake build` fetches every
module whose sources and options match master (`Fetched` lines) instead of rebuilding it.

Measured 2026-11-03 at 2c79634c7: master's set is 10,676 artifacts, 5.11 GB
(oleans 4.2 GB; zstd packs them about 3.4×), 3,564 mappings.  A dry run over
the 27 active lanes (548 s, read-only) found 28 to 10,676 missing per VM
(0.19–5.11 GB): most VMs' caches were cleaned for disk.  The first real
shipment to one lane (`memory-copies`: 28 artifacts, a 53 MB pack, 1,029
mappings and 1,321 Mathlib cache files) took 105 s; a second run found
nothing missing.  Uploads run at about 1.2 MB/s per VM (`vmexec.py --put`,
4 MB parts), so a full first shipment (~1.5 GB packed) takes ~20 min per VM
and is skipped on VMs short of disk; later shipments carry only the merge's
delta.  The gain per lane, a rebuild of master's changes at the VMs' few
workers (0.5–3.2 h after a core change in the receipts), is not yet measured.
