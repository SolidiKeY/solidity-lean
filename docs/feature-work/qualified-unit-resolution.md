# Qualified multi-unit declaration resolution (SOL-QN / G12)

Status: moved to a Claude VM (moved4, 2026-11-06); see "Moved4 Claude-VM
checkpoint" at the end for the current state. The final target relation,
the independent C3 judgment with the `idUniverse` bound, target
completeness and supported-type adequacy are proved, each with the
boundaries stated there. The signature-aware resolver agrees with all 17
direct compiler queries. No G13/G15, cross-unit typing, Solidity-wide
correctness, source-to-EVM or RUNTIME_GATE_PASS claim is made.

## Checkout, inputs and protected interfaces

Repository `/workspace/solidity-lean`, branch
`codex/solidity-sol-20261103/qualified-units`, exact pinned base
`b6ba0696102a7a038afe2ed333c09dff397cc5b2`. The clean launch checkout was
at that base. The assigned branch was created there without resetting work.
The stale remote-tracking master was fetched; `git merge-base --is-ancestor`
verified the base in published master
`2c79634c753aa09d1181c45445799ebea3408b81` and in this branch.
`tests/sol-qualified-units/evidence/setup.json` records actual commands.

`tests/sol-qualified-units/scope.json` lists verified input paths and every
current explicit module/declaration/inductive constructor. Existing Source,
Static, Checked, Admission, SolcJson/Yul, Lowering, ExtCall and shared build
or registry files are not edited manually by the lane. Published dependency
merges are recorded below; H16/H19/H21/H22 freezes remain binding. There is
no SOL-OV/SOL-PC dependency, push, merge into the default branch or PR. The
later G25 packet is isolated and does not substitute for the original queue. `get_goal` is unavailable; the existing goal was
neither created again nor reset.

## Published dependency adoption (2026-11-03)

Published master `059eb83d4e1d494f42c532513ffbcd3e65adaf75` was fetched
and verified, then adopted in merge
`c8b5499ac7e96428bb4aa07176f964093f807c6c`. Its other parent is the saved
worker checkpoint `f624bdb60df4fc08ec985c87f3c4f1b58bc55c21`; no worker
file, original Source module or Static input changed in the merge.
The integration-qualified-units note imports only Relation, leaving 14
owned modules pending central registration. H24 is a P8 companion, not a
cross-unit canonical-signature interface or an answer to QN-SIG. Separate
finder and skeptic adoption reviews confirm the blocker remains.

All owned gates were refreshed serially against the adopted dependency.
Touched-work comparison now uses the verified published commit rather than
rebuilding the entire already-published increment from the original launch
base. The original assignment base and original worker patch remain intact.
Receipts also bind the actual adopted lakefile hash. Global gate commands
are unchanged. The first original-base rebuild attempt was stopped and its
exit-137 evidence preserved as adoption-interrupted-*. The corrected run
passes build-touched, then starts the adopted policy's full library build
of 2,390 targets. That uncached build was stopped, with its partial output
saved as adoption-library-incomplete.log; it is not a passing checkpoint.
Cache transfer was announced separately. The library and full run-lean
remain pending, independently of the two unresolved query failures.

Existing static trust, orphan, layer, root, documentation and axiom checks
were run separately in one bounded no-network container. Trust/layers/docs
and 6,252 recorded global axiom pins pass; roots/orphans fail on the 14
unregistered modules. These checks do not replace the unfinished library
or full gate. Commands/outcomes are in adoption-static.json.

## Published dependency adoption (2026-11-04)

Fresh published master `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5` was
remote-verified and merged as `7be46d788b21906606752bd61ba23c29001ba08f`,
with accepted producer da0551dd as the other parent. Every owned lane file,
Source/Static input, toolchain and Lake configuration is unchanged by this
merge. The bounded integration imports Controls and Lookup; together with
Relation, three modules are centrally registered and 12 remain pending.
No new module/composition or shared registry edit was made locally; the
original exclusive-write and producer-interface holds remain in force.

Finder and skeptic independently verified preservation and the unchanged
QN-SIG boundary. New OverrideValidation helpers still use single-Env STy
values; they do not supply cross-unit declaration-identity signatures. No
human QN-SIG option was selected by the integration message. The original
queue was therefore blocked at that historical checkpoint; H27 now authorizes its repair.

Source/hash inventory passes; the saved-evidence audit still refuses both
actual overload mismatches. Fresh root/orphan checks report the remaining
12 modules. No Lean source changed, so no new proof build was run. Prior
Lean/solc/KeySort receipts remain historical, not an exact-head validation
of this new dependency. The coordinator's reported full-gate/Bridge/audit
passes apply to its published increment, not the remaining owned queue.
Full local library/final validation remains pending; cache delivery is
separate. dependency-20261104.json records commands and review findings.

## Work queue

| Item | Status | Remaining |
|---|---|---|
| Inventory and independent relation | done (moved4) | `Target.Target` is the final relation, including inherited overloads; its overload hierarchy is the independent C3 `Linearization.Linear`. Executable leaves (`normalize`, `hides`, `overload`, `group`) are stated in its docstring. |
| Arbitrary finite qualified lookup | done (moved4) | `Linearization.order_iff` covers C3 existence and the `idUniverse` bound, with no premise. Precedence is `Linear.precedence` and acyclicity is `Linear.acyclic`. Adequacy against Source elaboration is `NormalizationAdequacy.types_adequate`. |
| Soundness/completeness and preservation | done (moved4) | `Target.target_iff` (premise-free), plus `Target.identity`, `Target.noClash` and `refused_no_target`. |
| Fixtures, acceptance and handoff | see moved4 checkpoint | The supported-type adequacy theorems are `types_sound`, `types_complete` and `types_adequate`. A cross-unit control discharges their premises. The gate outcomes are listed in the moved4 checkpoint. |

H27 authorizes the owned normalization repair. Required resolver integration
and full acceptance remain outstanding. The separately assigned G25 packet
is saved in its isolated worktree; it does not complete this original queue.
All proof obligations and existing failing controls remain in force.

## M3 modules and historical central-registration frontier

All paths below are under `Solidity/Frontend/QualifiedUnits/`. These are the
module inventory; Relation, Lookup and Controls are now centrally registered, while the other
12 need root/module-map registration at integration after H21;
this lane must not modify the shared registry itself.

| Module | Defines |
|---|---|
| `Relation.lean` | Already integrated upstream; independent raw member, namespace step and finite path relations over original identities |
| `Lookup.lean` | Already integrated upstream; raw finite lookup, with member/step/path soundness and completeness |
| `UnitPaths.lean` | Unique unit-namespace paths to contract/interface base identities; ambiguous prefixes cannot be rescued by later suffixes |
| `Inheritance.lean` | Identity-indexed base graph, private visibility before shadowing, finite inherited-name saturation and its equivalence |
| `Specification.lean` | Lexical head priority, compatible terminal symbols, unique proper prefixes, valid lexical scopes and the independent candidate acceptance relation |
| `Checked.lean` | Missing/ambiguous/local-shadow/invalid-scope outcomes; acceptance equivalence, original declaration identity existence and no-clash preservation |
| `References.lean` | All explicit paths and identifiers, including full expression-member chains and their prefixes |
| `Controls.lean` | Already integrated upstream; eight raw-lookup kernel controls, including cycle, diamond and duplicate-owner isolation |
| `CheckedControls.lean` | Seventeen checked lookup/refusal controls, including inherited-private fallback and scope validity |
| `ReferenceControls.lean` | Seven member-path, MapKey and import-alias observations |
| `ConstructorFixtures.lean` | All 112 existing Syn constructor specimens, with literal expected reference lists |
| `DifferentialControls.lean` | Eighteen kernel observations, including matching nongap compiler cases and three overload/base observations preserving the known gaps |
| `Layout.lean` | Universal frozen source-layout theorem and actual owner-body member correspondence |
| `ReferenceCoverage.lean` | Universal explicit-path coverage, subterm closure and nested full expression-path coverage |
| `SignatureGap.lean` | Two explicit counterexample observations preserving the inherited-overload defect |

The 112-row constructor inventory is pinned to frozen `Source/Syntax.lean`.
It lists every syntax child and explicit IdPath/MapKey field. Direct path
fields occur in inherit, function/modifier/fallback/receive/stateVar override
lists, usingPath/usingAlias, modInv, mapping keys and userType. Identifier
heads and expression member chains are separately covered. All four import
constructors are inventoried. The owned generator writes only this lane's
traversal/specimens. Their shared generation is structural coverage, not
external correctness.

`references` retains the full path of `N.M.T`, its prefixes and identifier
head. A non-path receiver such as `f().field` contributes its ordinary
subterms; runtime object-field typing remains G13. Struct fields and enum
values are not declaration graph nodes in frozen `Syn.collect`; this fact
is not permission for a new language exclusion. Final traversal/resolution
acceptance must retain the existing G12/G13 boundary.

## Candidate semantics and proved boundary

Raw relations use existing UnitSet, Sees, Sym and DeclId. Declaration
members retain original unit/position. The member interval uses the actual
owner syntax body; it does not join children by spelling alone. Four
same-spelled-owner controls preserve the counterexample that motivated
this correction. `source_layout` proves the layout of every original source
unit, and `Member.in_owner_body` identifies each returned member with its
actual position in that owner body. Neither theorem assumes source admission
or unique container spellings.

`paths_sub_references` preserves every frozen explicit path/identifier for
arbitrary intrinsic syntax. `references_eq` decomposes reference traversal
into its root contribution and actual children; `references_sub` lifts it
through the existing Syn.Sub relation. `expressionPath_in_references_of_sub`
therefore preserves complete member chains nested anywhere in source syntax.
The initial global induction reached the existing heartbeat budget; explicit
structural recursion and small append lemmas prove the same statement with
no budget increase or new premise.

Proper namespace prefixes require one identity. Duplicate occurrences of
that identity are harmless; two distinct identities are refused before a
later suffix can make their routes converge. Terminal overloadable
functions/events may form a coherent set. Local heads block reinterpretation
as imported namespaces, visible members precede globals, and private base
members are filtered before deciding whether a scope shadows a global.
Invalid foreign/nonexistent/non-container lexical scopes are refused.

Import traversal reuses frozen finite saturation. Qualified suffix recursion
consumes one component. Inherited graph saturation is bounded by original
source declaration positions plus the query root. Base references retain
all qualifiers and require unique prefixes and a contract/interface target.
C3/override validity, whole-program admission and expression access/typing
remain their existing owners' work; a successful standalone query is not
source admission. Frozen Sees cycle-snapshot and repeated-namespace-alias
differences from solc remain visible boundaries, not new exclusions.

`resolve_iff` is sound/complete against the explicit current Resolved
relation. `resolve_identity` proves every returned declaration identity
still names an original source declaration. `resolve_noClash` proves every
successful answer satisfies the existing no-clash predicate, without an
external admission premise. These do not repair the known inherited-overload
candidate loss described below and must not be presented as full H23
completeness.

## QN-SIG: H27 authorized owned normalization

Sources: H23's producer-interface/representation escalation requirement;
`Source/Overloads.lean` identifies inherited overload collection as G12;
`Source/Types.lean` gives STy/DeclName only scope/name, without unit identity;
`Decl.sameParams` uses one Env and its typed fnSig.

The current nearest-name graph loses B.f(uint) when D declares f(bool).
`SignatureGap.current_overload_gap` kernel-checks that current behavior;
`base_overload_exists` proves the lost identity exists. The two compiler
fixtures `inherited-overload-gap` and `qualified-parameter-overload-gap`
are accepted by pinned solc, and their call references select the base
function. The latter uses different units' same-spelled enum T types.
Both rows remain resolution_gap=true; resolver_acceptance_complete=false.
These are required-gate failures, not authorized exclusions.

The historical question is stored with stable ID/source tags/options in
scope.json. Human H27(2026-11-04) explicitly authorizes option2: implement
identity-preserving inherited-signature normalization within the owned paths,
prove identity preservation, keep the producer DeclId API unchanged and make
the module reusable. This is an explicit answer, not inferred permission.
The original options were:

1. Reopen the producer-interface freeze for a canonical signature API keyed
   by DeclId, then resume against that interface.
2. Authorize identity-preserving signature comparison within the four owned
   paths, including required parameter-type normalization; preserve frozen
   modules.
3. Clarify that inherited overload collection stays with its existing owner;
   retain an explicit uncompleted integration obligation.

No exclusion or new theorem premise is recommended or approved. Do not
silently flatten type names or depend on SOL-OV to hide this obligation.

## Gates, resources and trust

The table below records historical pre-2026-11-04 execution; none is a new
exact-head full validation claim. Current adoption-only checks are recorded
separately above. Commands run from the repository; full subprocess arguments, outputs and
exit codes are under `tests/sol-qualified-units/evidence/`.

| Command | Outcome |
|---|---|
| `python3 tests/sol-qualified-units/run-candidate-gates.py build` | pass: 15 modules, 23 jobs (`candidate-build.log`) |
| `python3 tests/sol-qualified-units/run-candidate-gates.py axioms` | pass: AXIOM_PINS_PASS 219 (`candidate-axioms.log`) |
| `python3 tests/sol-qualified-units/run-candidate-gates.py declarations` | pass: 1,582 individually pinned declarations, including 606 private declarations (`declaration-report.json`) |
| `python3 tests/sol-qualified-units/run-candidate-gates.py solc` | pass: all 15 compiler acceptance/refusal and selected-reference expectations (`solc-report.json`) |
| `python3 tests/sol-qualified-units/run-candidate-gates.py queries` | fail: 17 actual resolver queries; 13 cases agree, inherited-overload-gap and qualified-parameter-overload-gap omit the base declaration (`query-report.json`) |
| `python3 tests/sol-qualified-units/run-candidate-gates.py keysort` | pass: parsed 377 taclets, 131 read-bearing, table covers 131; annotations match (`candidate-keysort.log`) |
| `python3 tests/sol-qualified-units/run-candidate-gates.py repository` | incomplete: actual adopted coord-tools checkpoint; build-touched passes, uncached library build stopped with exit 137 (`repository-gates/gates.tsv`, `adoption-library-incomplete.log`) |
| `python3 scripts/check-sol-qualified-units.py --inventory-only` | pass: 15 modules, 413 explicit declarations, 112 constructor rows; full generated inventory and every theorem/fixture row audited (`inventory.log`) |
| `python3 scripts/check-sol-qualified-units.py` | exit 1: all seven gates executed serially, then audit independently recomputed the two actual differential mismatches (`adoption-acceptance.log`, `acceptance-gates.json`) |
| `python3 scripts/check-sol-qualified-units.py --audit-only` | exit 1 on actual differential mismatches, independently of gap/completion flags (`audit-only.log`) |
| optimized Python and gap-flag controls | pass: all three Python entrypoints refuse -O; both actual mismatches persist with every gap flag false; comparison survives JSON roundtrip (`audit-controls.json`) |
| adopted static gates | trust/layers/doc-paths/axiom-pins pass; roots/orphans fail on 14 modules (`adoption-static.json`) |
| `./run-lean.sh` | historical pre-adoption invocation stopped at stale roots; adopted checkpoint policy runs the library instead; full run-lean remains pending |
| `scripts/coord-tools/gate.sh full` and post-integration `./run-lean.sh` | pending after QN-SIG repair and authorized central registration; no full-build pass claimed |

Actual Lean is 4.24.0, commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake is
5.0.0-src+797c613. Runtime setup and toolchain archive checksum are in
setup.json. The exact solc version is
0.8.38+commit.1835d247.Emscripten.clang; SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.

The VM lacks systemd buses. The task runner uses verified Docker cgroups:
12 GiB hard memory, swap limit 0, LEAN_NUM_THREADS=1, explicit Lean -j1 via
a temporary owned alternate TOML. It byte-checks frozen lakefile.toml
unchanged and cleans up the owned container before removing temporary
configuration. A continuous guard uses min(host MemAvailable, finite
ancestor cgroup limit-current), preserving 4 GiB reserve. Actual minimum
headroom is recorded per gate, at least 12,416,843,776 bytes in the adopted serial attempts.

Build and per-mode evidence bind all 15 owned Lean sources and eight verified
inputs to exact hashes. Default acceptance runs build, axioms, declarations,
solc, actual queries, KeySort and repository checkpoint serially, recording
every subprocess outcome, including failures. Audits enforce current driver,
source, matrix, compiler graph and generated-query hashes and recompute the
actual query comparison. Setting resolution_gap=false cannot hide a mismatch.
All Python entrypoints reject optimization because it disables assertions.

All 219 explicit theorem pins are enforced live; all previous 199 sets are
unchanged. Reflection enumerates all 1,582 module-owned constants, including
1,231 theorems and 606 private constants; every entry is individually pinned.
No unsafe declaration, new axiom or nonstandard dependency occurs. The exact
five existing compiler-generated partial helpers remain byte-identical to
M2; no blanket partial allowance exists. Their baseline source hashes are
enforced. Only propext, Quot.sound and Classical.choice occur. There is no
sorry, native-decide shortcut or heartbeat increase.

The historical pre-adoption ambient repository axiom scan saw an ignored, untracked optional
Mathlib cache under Bridge/.lake and reports its test theorem foo as an
unrecorded pin. Original ambient output remains in repository-ambient/8.log.
The final core-source validation view overlays only that ignored cache with
an ephemeral empty tmpfs inside the container; no host cache, tracked source,
registry, gate or baseline pin file is changed. The unchanged global checker
then reports 6,122 pinned theorems, zero errors and zero unrecorded changes.
This source-only pass is distinct from the preserved ambient-cache failure.
Those historical run-lean/root/orphan failures are preserved. The adopted
axiom checker now excludes nested Lake caches (an upstream reviewed fix),
and the fresh static scan passes 6,252 pins without a cache overlay. Current
roots/orphans still fail on 14 modules; library/full run-lean remain pending.
Raw command TSV/controller outputs with trailing whitespace are preserved
byte-for-byte in sibling .gz files; log-normalization.json records the raw
hashes and whitespace-only normalization of the readable copies.

Compiler rows pin source hashes, settings, acceptance/refusal, error codes,
source spans and selected target unit/name/original graph position. The
matching intrinsic transcriptions elide comments/pragmas and unrelated
bodies. Direct query mode executes the actual candidate resolver and checks
17 queries against curated candidate sets and actual compiler-selected
references; it misses B.sol:1 and B.sol:2 respectively in the two gap cases.
Solc confirms selected references, not an enumeration of every overload
candidate. The query #eval result is executable testing; the separately
compiled observation theorems are kernel evidence. Neither is a verified
parser correspondence or evidence for all Solidity programs. Candidate
soundness/completeness against the explicit relation is not external
Solidity correctness and does not discharge QN-SIG.

## Required read-only reviews

Separate finder and skeptic agents reviewed each checkpoint area without
Lean invocations or Lean-server use. M1 found the spelling-based owner join
and indexed-induction error; both were fixed. Runner review found host-only
reserve accounting, interruption cleanup, nonrecursive inventory, stale
imports and unenforced axiom output. Fixes are cgroup-aware accounting,
owned-container cleanup, recursive inventory, source hashes and live pins.

M2 found inherited-private/global shadowing and ambiguous base-prefix bypass.
The new VisibleMember/UnitRoute relations and controls fix them. The skeptic
also found the inherited-overload candidate loss, retained as QN-SIG rather
than hidden as G13 selection. Fixture review found unpinned refusal reasons,
stale namespace inventory, missing kernel links and an analogous rather than
matching cross-unit inherited-type control. Exact code/span pins, actual
namespace parsing, complete links and matching DifferentialControls fix
those evidence defects. Final M2 re-reviews confirm all 15 compiler rows,
13 nongap links, exact target positions, 199 pins and KeySort output; they
retain QN-SIG, ownership layout and full final gates as unfinished.

M3 finder and skeptic independently checked Layout and the universal
reference proofs without Lean/server calls. The skeptic required lifting
full member paths through arbitrary nested subterms; references_sub and its
corollary now do so. Both verified complete module-owned reflection and the
five exact old compiler helpers. Final orchestration review required actual
query/repository gates and fixture freshness; these are now enforced. Finder
identified Python optimization disabling asserts; all entrypoints now refuse
it. An audit roundtrip exposed tuple/list normalization, repaired in the
comparison output. Both known query mismatches remain intentional failures,
not waived obligations. Final review details are saved in m3-reviews.json.

## Checkpoint handoff

The original patch retains worker snapshot f624bdb6 against the exact launch
base; adoption-followup.patch separately captures owned post-merge changes.
The next dependency-20261104-followup.patch records this adoption handoff.
Exact current head, published dependencies, all patch boundaries and original
base/branch are recorded after committing in evidence/checkpoint-handoff.json. Its sibling
SHA256SUMS binds committed source/evidence plus the generated original.patch
and handoff JSON. These files describe partial progress, not completed H23.
The original goal remains incomplete; H27 has resolved the authorization
boundary and work is active. No second goal or continuation is created. `get_goal` and
per-file Lean MCP diagnostics were unavailable; bounded serial shell checks
supply the recorded evidence. The exact committed head is supplied by the
post-commit handoff, while individual pre-commit gate records retain their
actual execution head and source hashes.

## H27 implementation checkpoint (active)

The additional G25-UCAST-1104 packet is saved separately at
/workspace/solidity-lean-ucast-1104, commit 3b8c05798b6213cb9264f204084fb7a891e1eb0e.
Its 372 cases/23 theorems/72 declarations pass scoped acceptance; full corpus
validation remains resource-stopped and five registrations are V09-owned.
No packet file is a dependency of this name-resolution work.

Potential lookup cost increase was warned before implementation. History
inspection found the finite-saturation resolver checkpoint a76a7490 and this
lane's M1/M2/M3 checkpoints; no speed-motivated refactor is undone. H27 will
keep original identities and finite graph bounds, with reusable typed
signature metadata rather than changing Source types or producer APIs.


H27 adds four reusable/controlled modules, with central registrations pending:

| Module | Proposed area row |
|---|---|
| TypePaths | Unique qualified type routes over original declaration identities; relation equivalence |
| SignatureNormalization | Intrinsic signature comparison keys, original owner occurrences, normalization identity and explicit comparison failure |
| SignatureHiding | Directional external parameter location comparison; all nested nominal identities preserved |
| NormalizationControls | 21 kernel controls, separate from compiler observations |

The 40 H27 theorem rows are enumerated in signature-normalization-matrix.json.
Every owned declaration, including private/compiler-generated declarations,
is reflected and pinned. The exact eight new generated implementation
helpers are individually reviewed; safe terminating public definitions and
all prior source/helper pins are retained. There are no unsafe declarations,
new axioms, budget overrides or nonstandard axiom dependencies.

`SignatureNormalization.preserves_identity` proves normalization identity:
its output owns exactly its input DeclId. Nominal leaves carry original
kind-checked declaration identities and satisfy the qualified TypePaths.Route.
Alias-equivalent parameter keys do not identify their distinct functions.
`sameParams` and `hides` return `none` on failed normalization, never a
successful distinct-signature answer. Hiding requires the consumer to supply
same-name candidates in the intended owner order. Its directional external
comparison preserves storage and nested callable distinctions. The ordered,
multiplicity-preserving `nominalIds` theorem covers nested nominal leaves.

The five pinned 0.8.38 compiler probes separately establish two accepted and
three rejected location scenarios, with exact error codes. Public/internal
memory-calldata comparison controls describe the normalization result;
the rejected overrides do not establish valid distinct Solidity overloads.
The stronger structural type-elaboration correspondence, inherited candidate
integration/order proofs, repaired direct differential and final gates remain
open. Existing Source.arrayLen folding is reused; this checkpoint supplies no
additional constant-expression evaluator or general type-checking adequacy.
No G13/G14/G15 or source-to-EVM completion is claimed.

The checkpoint repository library build was stopped by the unchanged H1
reserve guard (exit137); its raw log and gate receipt are retained under
h27-reserve-stop-*. Final library/run-lean/corpus validation remains pending.
Clean owned build-artifact cache pages were released with POSIX_FADV_DONTNEED
without removing or changing files, to permit bounded scoped checks. No
RUNTIME_GATE_PASS is claimed. The explicit --signature-foundation-only audit
checks scoped evidence; default acceptance retains every differential,
repository and unfinished-queue requirement.


### H27 committed handoff

This checkpoint supplies the reusable normalization/hiding foundation only;
the full four-item queue remains partial. Fresh serial commands/timings are
in evidence/h27-commands.json; all use the existing writer lock and 12 GiB
Docker memory/no-swap bound, LEAN_NUM_THREADS=1 and Lean -j1. Toolchain:
Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake
5.0.0-src+797c613. KeySort passes 377 taclets and 131/131 read annotations.
The scoped audit passes and its three in-memory corrupt-evidence controls
refuse false compiler acceptance, a missing theorem row and a failed gate.
Finder/skeptic findings and exact helper boundaries are in h27-reviews.json;
configuration/runtime cleanup ownership defects were fixed before sealing.

Actual resolver queries still fail inherited-overload-gap and
qualified-parameter-overload-gap. The repository checkpoint stopped during
library compilation with exit137/minimum available 4059549696 bytes; the
completed touched gate passed, but the interrupted library and later gates
have no passing receipt. Its total elapsed time was not captured; completed
module timings and the raw stop are preserved. Full library/run-lean/corpus
checks and central registration are pending. No acceptance or runtime-pass
claim is made. The next owned work is inherited candidate collection using
these keys, with an independent relation/proofs and repaired actual queries;
all earlier lexical-shadowing/ambiguity/identity obligations must remain.

Original base/branch, exact committed head, absolute patch/evidence paths,
review receipts, separate G25 packet status and checksum bundle are recorded
post-commit in evidence/checkpoint-handoff.json. The original persistent goal
remains incomplete. No get_goal or per-file Lean MCP tool is available in
this tool catalog; no replacement goal or competing continuation was made.


## H27 inherited collection checkpoint (2026-11-04)

Published origin/master b419c3cf4f642ae519b66bebc26cdf2f7cf93574 was
remote-verified and adopted by merge c6afeb3e1f02ccb84a165174128aadbf474e5b48.
The saved d13f33b0 implementation/artifacts were preserved. The five newly
accepted modules match their owned definitions; no frozen Source/Static,
Core ExtCall, producer DeclId API or shared registry was edited manually.
Eight owned modules are now centrally registered; 13 remain pending.

Potential lookup cost was warned before adding the walk. History inspection
included a76a7490 and this lane's finite-saturation/M1/M2/M3/H27 changes;
no speed-motivated optimization was undone. New registration proposals:

| Module | Proposed area row |
|---|---|
| SignatureMembers | Original-identity bounded C3 equations; explicit-failure inherited overload collection, independent walk judgment, unconditional membership equivalence and original identity/normalization preservation |
| SignatureMemberControls | 14 executed collection controls for overloads, same-owner duplicates, locations, original diamond override, missing/ambiguous bases, bad roots, unresolved first-owner types, cycles and absent names |

The implementation validates every written base with mapM, checks container
roots and normalizes every visible candidate before collection. Same-owner
functions are considered together before that owner enters the hiding set.
A failed comparison cannot count as a distinct signature or admit globals.
The general totality lemmas derive an actual walk for normalized groups;
collected_iff has no supplied desired-run premise. Every emitted identity
exists in the original UnitSet and has a successfully normalized signature.

Finder and skeptic independently identified dropped invalid bases and the
first-owner normalization bypass; all findings are fixed and have negative
controls. They reviewed the five new compiler-generated helpers exactly;
public definitions are terminating/safe and no source partial definition,
unsafe declaration, axiom or proof-budget increase was introduced. Previous
pins/source hashes remain intact. Details: evidence/collection-reviews.json.

Fresh serial gates pass 21 modules, 2067 reflected declarations, 285 theorem
pins and 66 H27 theorem rows. All 15 compiler fixtures and five signature
probes pass. KeySort passes 377 taclets and 131/131 annotations. The scoped
audit passes, including three negative evidence controls. Commands, actual
outputs and measured timings are in evidence/collection-commands.json.
Lean remains 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake
5.0.0-src+797c613; per-file Lean MCP/get_goal tools remain unavailable.

The fresh repository checkpoint stopped during library compilation after
24.25 seconds: exit137, minimum available 4212879360 bytes, unchanged H1
reserve guard. The completed touched gate passed; interrupted/later gates
have no passing receipt. Raw controller output is preserved in gzip files;
only readable-copy trailing whitespace is normalized. Full library,
run-lean/corpus and central-registration validation remain pending. No
RUNTIME_GATE_PASS is claimed.

This is a partial original-queue checkpoint. The independent WalkMember
judgment does not invoke executable walk; Collected still uses executable
order and ready, so the theorem does not independently establish C3/bound
adequacy or structural normalization/overall Solidity correctness. Checked
integration is still open, and must preserve nearer non-overloadable lexical
shadowing and refuse collection failure without global fallback. The actual
legacy resolver still fails inherited-overload-gap and
qualified-parameter-overload-gap; these are retained, not waived or relabeled
as G13. G13/G14/G15/source-to-EVM completion is not claimed. No new scope
question, replacement goal or competing continuation was created.

The committed collection patch/bundle and final VM receipt identify exact
snapshot/packaging heads, base/branch, all remaining queue obligations and
absolute artifact paths. Earlier committed H27 and separate G25 packet
artifacts remain preserved; this checkpoint does not complete either queue.


## Signature-aware Checked integration checkpoint (2026-11-04)

Published origin/master 89373e34cdfd6bb5db7054b1c204d01edffc5fa7 was
remote-verified and adopted as merge 10d99dcd1bb72a203ce1719d6d8ce76fb712fb4a.
The saved bce9ddb1 implementation/artifacts remain preserved. The two
accepted References modules match their owned definitions. Shared AST reader
APIs were inspected: they are executable surface-reader boundaries, not a
replacement for this intrinsic Source declaration resolver. No Source,
Static, protected frontend/lowering, Core ExtCall or producer DeclId API was
edited. Ten owned modules are centrally registered; 13 remain proposed.

Potential checking cost was warned before integration; prior finite graph
and a76a7490/M1/M2/M3/H27 history was inspected, with no speed-motivated change
undone. New consumer API:
`Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve`.
The existing resolver, its proofs and all legacy counterexample observations
remain unchanged. The new consumer reuses existing Failure, ValidScope,
coherence/no-clash contracts and checked terminal validation. It supplies
independent Member/NamespaceStep/Head/Admits judgments and unconditional
resolve_iff, successful-answer no-clash and original-identity proofs.

Only a nonempty nearest overload family triggers signature collection.
Non-overloadable nearest declarations retain their old lexical priority.
Global fallback requires absence of the original nearest-name set, so failed
normalization or ordering refuses the admissible route instead of exposing
globals. Such refusal uses the existing missing-route error; this does not
mean the underlying declaration node is absent. An intermediate visible
non-overloadable declaration is an explicit barrier, not a filtered-away
route to older functions. Private filtering occurs before this check.

Finder identified the deeper D.f/B.variable/A.f barrier. SafeOwners now
checks original visible members; paired lexical/qualified kernel controls
refuse it. Pinned solc rejects the conflicting hierarchy with two 9097 errors
and accepts the positive public-getter override, whose original variable
identity is preserved by the new resolver. These observations do not prove
that every SafeOwners refusal is invalid Solidity; general adequacy remains
open, rather than becoming a silently approved exclusion or premise.

The 17 original direct queries now execute the new public resolver and agree
with unchanged expected candidate sets and actual compiler-selected targets.
The two historical *-gap case IDs remain stable; their gap flags are false
only after actual agreement and new paired kernel observations. All 15 main
compiler rows have complete query/kernel links. Existing legacy gap theorems
still describe the old API and are not weakened or removed.

Fresh scoped evidence passes 23 modules, 2193 reflected declarations, 329
explicit theorem pins and 110 H27 theorem rows. The two new modules provide
17 general theorems and 27 kernel controls. All 112 Source constructor rows,
15 main compiler fixtures, seven supplementary probes and 17 direct queries
are checked. The scoped audit now also requires actual query agreement and
all compiler/kernel links. Six in-memory corruption controls reject missing
base candidates, missing links, false getter rejection and other bad receipts.
Exact commands/timings: evidence/resolution-commands.json. Read-only reviews
and the single exact new generated helper pin: evidence/resolution-reviews.json.
No source partial definition, unsafe declaration, axiom or proof-budget
increase was introduced; all previous pins/source hashes remain unchanged.

KeySort passes 377 taclets and 131/131 annotations. Lean is 4.24.0
(797c613eb9b6d4ec95db23e3e00af9ac6657f24b); Lake is 5.0.0-src+797c613.
The fresh repository checkpoint touched gate passes, but library compilation
was stopped by the unchanged H1 reserve guard after 238.37 seconds,
exit137/minimum available 4192772096 bytes. Interrupted/later gates have no
passing receipt. Full library/run-lean/corpus validation and 13 central
registrations remain pending; no RUNTIME_GATE_PASS is claimed.

This is still a partial original queue. Independent C3/bound and structural
normalization adequacy remain open, including complete supported-type
coverage and the existing Source.arrayLen folding boundary. The theorem
against the declared relation is not external Solidity correctness or a
verified parser correspondence. Cross-unit expression typing/access/overload
selection remain with their future owner. No statement/premise/exclusion or
legacy observation was weakened. The original persistent goal remains
incomplete; get_goal/per-file Lean MCP tools are unavailable, and no new goal,
reset or competing continuation was created. Earlier H27/G25 artifacts remain
preserved. Registration proposals and final VM receipts identify all exact
snapshot/packaging heads and absolute patch/bundle/checksum paths.


## Owned G0 repair checkpoint (2026-11-05)

Published 8495f1deb0a95dd6b9301822d8649ab76b217681 was fetched, independently
ancestry-verified and merged as 11da8811639de8fa16f5befe446ed476a3439581.
All committed/uncommitted artifacts were preserved. DifferentialControls and
SignatureGap were the two newly imported owned modules; publication is not
whole-lane completion. Twelve modules are now centrally registered and 11
remain proposed. No cache freshness was inferred from the delivery notice.
The prescribed /tmp writer-lock directory was absent after environment
startup and was restored before writes/checks; no other writer/Lean job ran.

The explicit G0 review found indexed Syn matches in owned kernel-evaluated
helpers. Prior integration is no waiver. History was inspected and potential
checking cost warned before repair. Eleven helpers now use category-general
Syn.casesOn/Syn.rec motives, with all 112 constructors enumerated exactly once.
Public memberCount/basePaths/bodyDecls/expressionPath/references/rootReferences,
types/parts/isExternal interfaces remain unchanged. No protected Source
callee or producer API was edited. This is an owned repair, not a claim of
transitive or repository-wide G0 compliance through frozen Source functions.

Structural casesOn-only reference recursion hit the original 200000-heartbeat
isDefEq budget. That raw failure is retained. The documented faster form now
uses kernel Syn.rec and structural casesOn executable twins; both equality
link theorems are proved with explicit generalized recursor motives. All
existing consumers and constructor controls pass without heartbeat or
recursion-budget increases. Existing proof reductions were updated, while
all 329 prior explicit theorem headers are verified unchanged. The preliminary
"no twin" strategy receipt is archived; the corrected receipt identifies both
twins. G0 constructor/link/header checks are enforced by the lane checker.

The exact trust transition was reviewed independently: 2193 to 1506 constants
(708 removed, 21 added), with 125 surviving changes only dropping dependencies.
The active list remains 19 individually pinned compiler-generated helpers;
two old reference helpers are replaced by the two axiom-free runtime twins.
Historical declaration/axiom/helper inventories and source hashes remain
archived. No unsafe declaration, axiom, nonstandard dependency, weakened
statement or general helper allowance was introduced. Details are recorded
in evidence/g0-reviews.json and g0-kernel-helpers.json.

Fresh scoped gates pass 23 modules, 1506 declarations, 331 explicit theorem pins,
all 112 Source constructor rows, 110 H27 rows, 15 main compiler fixtures, seven
supplementary probes and 17 actual resolver queries. KeySort passes 377 taclets
and 131/131 annotations. Nine read-only corrupted-evidence controls now include
wrong eliminators, missing twin links and changed theorem headers. Exact
commands/timings/raw failures are retained in evidence/g0-commands.json and
its controller logs. Lean remains 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b),
Lake 5.0.0-src+797c613; get_goal/per-file Lean MCP tools remain unavailable.

The fresh repository touched gate passes, but library compilation was stopped
by the unchanged H1 reserve guard after 1264.19 seconds, exit137/minimum
available 4201066496 bytes. The run was serial with explicit -j1,
LEAN_NUM_THREADS=1 and Docker 12 GiB/no-swap bounds; no other job was interrupted.
No interrupted/later gate is counted as passed. Full library/run-lean/corpus,
central registration, independent C3/bound and normalization/type-coverage
adequacy remain unfinished. No RUNTIME_GATE_PASS or whole-queue completion
is claimed. The existing persistent goal is not reset or marked complete.


## Independent C3 merge checkpoint (2026-11-05)

Published f77cf60d3cea8f7f1db8db29cc027532b0cd3fce was fetched with a bounded
fetch and ancestry-verified against origin/master and previous8495f1de, then
merged as53cd6f9c618f99947cf6d6a924363d3be8399d87. Saved e82d8a9d work and
all untracked receipts remain preserved. Incoming changes did not touch owned
modules or frozen Source/Static inputs. No cache freshness is inferred.

MergeSpecification.lean adds an independent fuel-free First/Merge judgment
on original DeclIds: a first eligible row head occurs in no row tail; every
preceding row is independently blocked. It never calls mergeOwners. The proved
merge_iff characterizes the actual existing mergeOwners in both directions,
including the final empty step: output.length < fuel. General proofs preserve
all input identities, exclude invented identities, coalesce duplicates on
successful merges, establish output uniqueness and transport successful runs
to larger fuel. No existing definition or theorem statement is changed.

Nine kernel controls cover nontrivial diamond identity, its relational witness,
duplicate routes, a blocked first head, contradictory precedence and independent
absence of any Merge judgment, exact insufficient fuel, zero fuel and empty
rows. This proves neither valid hierarchy existence nor hierarchy precedence
or the idUniverse-specific bound. Normalization adequacy and full supported-type
coverage also remain unfinished. Producer Source/Static APIs remain read-only.

Separate read-only finder and skeptic reviews used neither Lean nor server and
found no concrete defect. Exact reflection adds69 declarations, removes/changes
none of the previous1506; the resulting1575 have no new unsafe/partial/axiom or
nonstandard dependencies. Generated producer-namespaced merge equations belong
to the new module and are explicitly inventoried, without producer-source edits.
The new22 explicit theorems bring pins to353. A first axiom check caught ordering
of reflected dependency sets versus live lists; the raw failure is retained and
only new pin ordering was corrected, with identical sets. The next run passes.

Fresh scoped gates pass24 modules,1575 declarations,353 theorem pins,132 H27
rows, all112 constructor fixtures,15 main solc0.8.38 fixtures,7 supplementary
probes and17 actual resolver queries. KeySort passes377 taclets and131/131
annotations. All9 audit corruption controls pass. Actual Lean4.24.0 and
Lake5.0.0-src+797c613 remain unchanged. Commands/timings, additive trust delta,
reviews and12 pending central registration proposals are in evidence/merge-*.json.
No shared roots/module-map files were edited by the lane.

The previous full checkpoint failure remains raw and unresolved: after1264.19s,
the H1 reserve guard stopped the serial12GiB/no-swap job at4201066496 available
bytes (exit137). This merge checkpoint does not reclassify that run as success
or claim current-head full validation. Full library/run-lean/corpus and final
acceptance remain pending. Frozen Source transitive G0 remains outside the
owned repair; no RUNTIME_GATE_PASS or full-lane completion is claimed.
The existing persistent goal remains incomplete; get_goal/per-file Lean MCP
are unavailable, and no goal was created/reset. Separate G25 work is preserved.


## Moved4 Claude-VM checkpoint (2026-11-06)

The lane moved from the Codex VM to a Claude VM. Branch
`cloud/moved4-20261105/qualified-units` merges the move branch
`cloud/qualified-units-move` (f94495e3) and current origin/master. The lane
base is aec9adf1ad8666a7e591e42a537069a93dc858cb.

None of the following were reachable from this VM, and none are cited as
evidence here:
- the Codex evidence directory;
- the H44 bulk bundle (`bulk-evidence-H44.json` indexes it);
- the Codex Docker runner.

All validation below was re-run on this VM.

### New modules

| Module | Content |
|---|---|
| `Linearization.lean` | Fuel-free C3 judgment `Linear`, built from `Routes`/`Bases` and `MergeSpecification.Merge` (see note 1). `order_iff`: `SignatureMembers.order` is sound and complete for `Linear` with no premise, so the `idUniverse` depth bound and the `bound * bound + 2` merge budget never refuse a valid hierarchy. Also `Linear.unique`, `Linear.bounded` (duplicate-free linearizations; cycles have no derivation), `Linear.members`, `Merge.sublist` (C3 monotonicity), `Linear.precedence` (base linearizations and the reversed local base list are sublists) and `Linear.acyclic`. |
| `Target.lean` | The final relation `Target` (see note 2). `target_iff`: `SignatureResolution.resolve` is sound and complete for it, with no premise. Also `identity`, `noClash` and `refused_no_target`. |
| `NormalizationAdequacy.lean` | `erase` keeps only the Source `DeclName`. `types_sound` holds for every constructor. `types_complete` and `types_adequate` hold on every supported signature category (see note 3). `fields_refused` covers struct members and variable declarations. |
| `TargetControls.lean` | Kernel controls: the diamond linearization and its local precedence; no linearization for a self-cycle or a missing base; both inherited-overload targets; a multi-hop target. Refusals: missing, ambiguous, local shadow, failed signature, visible barrier. Adequacy: a function type, refused struct members, and `adequacy_instance` (see note 4). |

Notes:
1. `Linear` never mentions `linearize`, `mergeOwners`, `bases` or `order`. It shares only `basePaths` with the executable code.
2. `Target` copies `SignatureResolution.Resolved`, with the hierarchy replaced by `Linear` and readiness replaced by `Normalized`. Its docstring names the trusted executable leaves: `normalize`, `hides`, `overload` and `group`.
3. The premises `LeafSound`/`LeafComplete` range only over `references s`, the paths written in the signature syntax.
4. `adequacy_instance` discharges those premises for a program where unit A imports B, and both B and an unimported C declare enum `T`.

### Proof boundaries

These follow from the finder and skeptic reviews.
- `target_iff` is completeness against an implementation-shaped relation. Only its hierarchy part is independent. It is not independent Solidity semantics.
- `Target`'s plain branch and global barrier use `InheritedMember`. That is reachability along the syntactic base graph, and it does not require a valid linearization. Only the overload branch requires `Linear`.
- C3 precedence is proved as monotonicity. Agreement with solc's exact order rests on the deterministic first-head rule and on pinned fixtures. There is no compiler differential of `Linear`.
- Normalization adequacy is relative to Source `Syn.tys`. Where Source `userTy` cannot follow a written path, the localized premises fail for that syntax, and the theorem says nothing about it. This covers unit aliases, paths with more than one qualifier, and homonyms visible in its flat environment.
- Adequacy is stated for `types`, the parameter elaborator that `normalize` uses. It is not stated for `ownerScope`/`parts`. `Source.arrayLen` folding is reused.
- No G13/G14/G15, source-to-EVM or RUNTIME_GATE_PASS claim is made.

### Queue items 5-8 of the move handoff

- check-trust passes with 0 findings. The two `References.lean` `@[implemented_by]` sites are inventoried, in `tests/trust-inventory.json` near lines 1388 and 1393.
- Registration: all 28 lane modules are in the generated `Solidity.lean` root (`register.sh --check` passes). Each has a module-map row; this checkpoint adds rows for 4 new and 6 previously missing modules to `docs/module-map/frontend.d/qualified-units.md`. The 12 pending central registration proposals are closed.
- `scripts/coord-tools/fragments.sh` also regenerated master's stale combined `docs/module-map/v08-adapters.md`, which failed `fragments.sh --check` on master.
- `check-doc-paths.sh` fails on master before this lane. `docs/feature-work/after-roadmap-va1.md` cites a Bridge Mathlib cache path. This lane does not own or change that file.

### Claude-VM gate driver

`tests/sol-qualified-units/claude-gates.py` replaces the Docker runner here. On this VM the shell refuses `lean` and `lake build`; Lean evidence comes from language-server elaboration of generated probe files in the VM-local `claude-evidence/` directory.

Under H44 that directory stays off git; the lane's `.gitignore` excludes it. The committed `tests/sol-qualified-units/claude-evidence-manifest.json` names all 36 files with their bytes and sha256, and records the receipt outcomes, the lane source digests, the runner digest and the two pin-file digests.
- `check-sol-qualified-units.py --claude-vm` with the directory present requires every file to match the manifest, then runs the full content audit.
- Without the directory it prints `EVIDENCE_OFF_GIT` and checks the manifest against the current sources, runner and pins, then applies the recorded receipt outcomes.
- `--write-claude-manifest` re-records the manifest.
- `probe M` writes the probe, deletes any old output and records source digests.
- The queries and declarations probes write their own `.out` files through `IO.FS.writeFile`.
- `record M F` requires the saved language-server diagnostics `F` to contain no errors. It also requires the sources to be unchanged since `probe`, and the output to be newer than its input.
- The axioms log is re-derived from the saved diagnostics by the checker (`--claude-vm`).
- Build and repository receipts come from `scripts/coord-tools/gate.sh full`'s own PASS/FAIL lines and per-gate logs.
- KeySort runs the built `solkeycheck` against the vendored solkey taclets.
- The pins grew without changing any old entry:
  - 1857 reflected declarations; all 1575 previous entries are unchanged.
  - 414 axiom pins; all 353 previous ones are unchanged.
  - New theorems use only `propext`, `Quot.sound` and `Classical.choice`, or no axiom at all.
  - The three compiler-generated `_unsafe_rec` helpers of `erase`, `eraseList` and `Supported` are listed in `partial-helpers.json`.

The compiler differentials ran on npm `solc@0.8.38` `soljson.js`.
- SHA-256 `0b15fcb2…`; tarball integrity `sha512-DsDLa7uA…`.
- binaries.soliditylang.org is refused by this VM's proxy, so the pinned `6c74ffba…` artifact was unavailable.
- Both report `0.8.38+commit.1835d247.Emscripten.clang`, but they are not byte-identical.
- The accepted set is pinned in the checker's code, and each report records the artifact that actually ran.

Limitations of this driver, from the tooling reviews:
- The diagnostics JSON carries no language-server session binding.
- Sources are hashed at probe time and at record time, not inside the elaboration.
- `minimum_available_bytes` is null: there is no monitored run. A point-in-time `MemAvailable` is recorded separately.
- `private theorem`s are outside the axiom probe, as on the Codex runner. Their transitive use is covered by the public theorems.

### Gates at this checkpoint

`scripts/coord-tools/gate.sh full` ran at c5c3a308 with elan on `PATH`. The sources are unchanged from that head except `scope.json`. The receipts (`gate-build.json`, `gate-repository.json`, `gate-keysort.json`, `gate-sh-summary.log`) are VM-local and listed in `tests/sol-qualified-units/claude-evidence-manifest.json`.

| Gate | Result | Cause |
|---|---|---|
| build-touched | PASS | |
| run-lean | FAIL | `lake build` passes (6122 jobs, no `error`). The failure comes from `check-solkey.sh` (note 1). |
| trust | PASS | 0 findings |
| orphans, layers, roots, fragments | PASS | |
| doc-paths | FAIL | Fails on master: `docs/feature-work/after-roadmap-va1.md` cites a Bridge Mathlib path. |
| axiom-pins | FAIL | 0 errors and 3919 unrecorded new pins in the repository-wide inventory (note 2). |
| testsuite, corpus | FAIL | They compare the same sibling checkout's `TestSuite.sol` (`519abdd5…`) with the imported AST (`12de663e…`). |
| automatic-strict | PASS | |
| KeySort (`claude-gates.py keysort`) | PASS | `solkeycheck --key` matches the vendored `tests/migration/solkey` taclets. |

Notes:
1. `check-solkey.sh` reads the sibling `../solkey` checkout. On this VM that checkout is upstream HEAD `b8d5f883`, not the pinned revision, and it reports 167 annotation mismatches.
2. None of the 3919 unrecorded pins is a `QualifiedUnits` theorem. The lane's own pins are in `tests/sol-qualified-units/axiom-pins.json` and pass.

The lane gates pass: solc, signature probes, resolution probes, queries, declarations and axioms. `check-sol-qualified-units.py --claude-vm` stops at `required gate failures: build, repository`.

A full build run started before the last source edits, and it reported errors in `TargetControls.lean`. They came from compiling against a stale `NormalizationAdequacy` olean. The rerun above rebuilt both modules cleanly, and the language server reports no errors in either file.

These receipts are recorded as failures and are not waived. Queue items 1-4 and the proofs are done. `scope.json` keeps `fixtures-acceptance-handoff` partial and `acceptance_complete` false until `run-lean` and the repository gates pass. That needs either the pinned solkey sibling or a fixed master.

## Moved4 follow-up: fixture acceptance (2026-11-06)

This section supersedes the gate table of the previous checkpoint. All
evidence below was produced on this VM at d9146bb1 (sources unchanged since).

### Pinned compiler

- `soljson-v0.8.38+commit.1835d247.js` came from GitHub's solc-bin mirror
  (`raw.githubusercontent.com/ethereum/solc-bin/gh-pages/bin/`). Its SHA-256 is
  `6c74ffba…d390`, the pinned value.
- `compiler-artifacts.json` and the checker's hard-coded set now accept only
  that artifact. The npm `soljson.js` (`0b15fcb2…`) used by the previous
  session is no longer accepted.
- With it: 15/15 `compiler-matrix.json` rows pass, and the signature and
  resolution probes pass. All three reports record `6c74ffba…`.
- The direct differential (17 queries against the Lean resolver) passes. It
  includes the multi-hop reference (`N.M.T`), the ambiguous refusal (`N.T`) and
  the missing-symbol refusal (`N.M.Missing`, solc error 7920).
- The agreement on the ambiguous case is accept/reject, not the reason. solc
  rejects `ambiguous-namespace` with error 2333 at the second `import * as N`,
  a duplicate declaration of the alias. The Lean resolver refuses the reference
  `N.T` as `ambiguous`. `ambiguous-base` works the same way.

### H44 bulk manifest

`verify_bulk_h44` in the checker checks `bulk-evidence-H44.json` for
internal consistency and prints `BULK_H44_MANIFEST_PASS`. It checks:
- the file's sha256 (`4affb5e3…`, as committed by the Codex lane at f94495e3);
- the 269 entries are unique, and each lies under `bulk_directory` with a
  `tests/sol-qualified-units/evidence/` original;
- every digest is well formed;
- the byte sizes add up to `total_bytes` (73851319);
- nothing under `evidence/` is tracked by git.

This is a structural check only. The files stay on the Codex VM, and no file's
content is verified here. A one-off search found that no tracked file matches
any of the 269 digests, and that git history has no `evidence/` path. Neither
result is recorded in an evidence file.

### Gate changes

- **KeySort removed.** Master a897dac76 (H89) dropped the SolKey checker from
  every gate. `claude-gates.py` no longer has a `keysort` command, and the
  checker no longer requires that receipt.
- **Repository receipt.** `gatelog` lists in `MASTER_ONLY` the gate.sh
  failures that do not come from this branch. The repository receipt passes
  only when every other gate passes. It keeps the full status table and the
  `master_only_failures` and `lane_failures` fields.
- Each exemption has a guard:
  - axiom-pins must report 0 errors and must not name `QualifiedUnits`. No lane
    theorem is in that inventory, so the name check cannot fail; the lane's own
    414 pins are the axiom evidence.
  - doc-paths: every `missing:` line must cite from a file that this branch
    does not change against origin/master.
  - testsuite and corpus: every log line must be the sibling `TestSuite.sol`
    revision check.
- All 12 gate.sh gates must be present in the run.
- The checker re-checks the receipt. It pins the four exempt names, requires
  every other gate to be PASS, and requires `lane_failures` to be empty.
- **Build receipt.** It now requires every one of the 28 lane modules to be
  covered:
  - 23 are built, replayed or fetched by run-lean;
  - the 5 changed modules are compiled by build-touched, then found up to date
    by run-lean.
- **Module map.** The master merge had duplicated a module-map row (a union
  merge in `v08-adapters.md`). `fragments.sh --resolve` repaired it.

### Gates at this checkpoint

`scripts/coord-tools/gate.sh full` ran at d9146bb1, with the Lake cache seeded
from master's `lake-cache` release (pack master b7c3cc51). After it, only
the driver, the checker, the lane doc, `scope.json` and the manifest changed;
the lane sources and inputs did not. The receipts were re-recorded from that
run's logs.

| Gate | Result | Note |
|---|---|---|
| build-touched, run-lean | PASS | `lake build` of the default targets plus SolkeyTestSuite: 6465 jobs, 0 `error` lines |
| trust, orphans, layers, roots, fragments, automatic-strict | PASS | |
| doc-paths | FAIL (master) | 5 missing references in h62 docs, scripts and tests; none in this lane |
| axiom-pins | FAIL (master) | 0 errors; 4478 unrecorded repository-wide pins, none in `QualifiedUnits` |
| testsuite, corpus | FAIL (environment) | The VM's sibling `../solkey` `TestSuite.sol` (`993bad1c…`) is not the imported pin (`12de663e…`). It is not caused by this branch, but neither gate got past that check here. |

Lane receipts, via `claude-gates.py`, all pass:
- solc, signature-probes and resolution-probes;
- axioms: 414 pins match `axiom-pins.json`;
- declarations: 1857 reflected declarations match `declaration-pins.json`;
- queries (`DIRECT_DIFFERENTIAL PASS`);
- build;
- repository (`LANE_FAILURES []`).

The Lean probes were elaborated by the language server and showed no errors.

`check-sol-qualified-units.py --claude-vm` passes in both modes:
- with the local evidence directory, the full content audit;
- without it, `EVIDENCE_OFF_GIT`, which checks the manifest against the
  current sources.

`scope.json` now marks `fixtures-acceptance-handoff` done and sets
`acceptance_complete` to true. The proof boundaries of the previous checkpoint
are unchanged.

### Remaining limitations

- The four exempt gate failures above remain. doc-paths and axiom-pins fail on
  master's files. testsuite and corpus depend on this VM's sibling checkout.
  No master baseline run was made.
- The generated `Solidity.lean` root and `docs/module-map/frontend.md` carry
  this lane's registrations. Under H21 they are produced by `register.sh` and
  `fragments.sh`, not hand-edited.
- The legacy Codex runner `run-candidate-gates.py` still has a `keysort` mode.
  Nothing calls it.
- The H44 bulk files cannot be content-verified from a Claude VM.
- `test-signature-audit.py` and the default (non-`--claude-vm`) acceptance mode
  read the Codex-only `tests/sol-qualified-units/evidence/` directory. They
  cannot run here.
- The Claude-driver limitations listed in the previous checkpoint still apply.

### Reviews (follow-up)

The finder and skeptic reviews were read-only and used no Lean server. The
following findings were confirmed and fixed:
- The checker did not re-check the exemption.
- Nothing guarded the testsuite and corpus exemptions, and the doc blamed
  master for them.
- The build receipt named no lane module.
- The H44 manifest digest was not pinned.
- The required gate set was incomplete.
- `h27_status` was stale.
- The doc overstated the ambiguous-case agreement and the H44 check.

Two findings were accepted as documented limitations, not fixed:
- The acceptance flag is set by hand. The receipts are checked independently
  of it.
- The axiom-pins guard cannot fail for a lane name.
