# SOL-C3: exact C3, graph identities and finite public fuel

The merge and graph proof layers are implemented and kernel checked on base
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`. Branch:
`codex/solidity-sol2-20261104/c3-exactness`; repository:
`/workspace/solidity-lean`. Compiler fixtures pass; full final gates remain open;
this document does not declare the frozen assignment complete.

## Producer and independent specification

`Solidity/Source/Resolve.lean:46–79` defines the producer reached from the four
assigned inputs. `Env.bases` selects the first file-level contract/interface
with the requested name, then takes terminal base-path names. `Env.merge` first
checks fuel: zero fails even for empty input. Positive fuel removes empty lists,
returns `[]` only at empty active residuals, scans heads left to right for one
absent from every tail, globally removes that chosen identity and recurses with
one less fuel. Termination consumes a positive observation as well.

`Env.linearizeF (n+1)` visits `(E.bases c).reverse` with recursive depth `n`, then
merges those complete base linearizations followed by the reversed direct-base
list. Each merge gets `N*N+2`, with `N=E.decls.length`; public depth is `N+1`.
`Env.chain` falls back to `[c]` on failure. `Env.ctorOrder` reverses that chain;
sequence consequences therefore retain a successful public-result premise.

`Trace.lean` defines independent generic success, obstruction and finite stuck
relations. It supports actual Nat declaration positions as well as producer name
strings. No relation calls `Env.merge`. `first_iff` exposes the rejected prefix;
`first_none_iff` and `obstruction_iff` extract an actual blocking tail for every
head. The relation chooses the first legal head and removes it globally.

For arbitrary finite inputs, `merge_iff` is success iff an independent trace
exists and output length is strictly below fuel. Direct `Trace.unique` does not
use producer functionality. Total occurrence count strictly decreases, giving
`fuelBound = ls.flatten.length+1`. At that bound, success is exactly `Trace` and
failure exactly `Stuck`. At arbitrary fuel, `merge_none_iff` separates genuine
obstruction from a trace whose required budget exceeds the supplied fuel.
Membership, duplicate freedom and every original list's ordering derive from
`Trace` at arbitrary identity types and lengths.

## Existing admission and exact public graph fuel

`Admission.lean` defines `rank` as the position of the first declaration chosen
by the exact existing `Env.bases` predicate. A miss has sentinel rank `N`, which
is not asserted to be a graph node. `base_rank_lt` derives strict edge descent
from existing `basesOK = true`: every base is an earlier file-level contract or
interface, with interfaces inheriting only interfaces. No new admission rule is
assumed. Rank is injective on selected in-bounds names, including environments
with duplicate declaration occurrences. This is not a bijection over all such
occurrences. Existing no-clash requirements are preserved and not needed for
this stronger statement about producer selection.

`Linearization.lean` defines independent `ExactLin`, with indexed child
derivations in reversed direct-base order and an independent exact merge trace.
Its direct uniqueness follows from child uniqueness and `Trace.unique`.
`linearizeF_exact_sound` supplies it for every successful recursive run.

Completeness does not assume `WellFormed.linearizes`. Under `basesOK`, inherited
merge-tail ranks are strictly below the root rank, hence every tail name occurs
in the declaration-name list. Tail duplicate freedom bounds length by `N`, even
when repeated input occurrences exceed `N*N`. Since `N < N*N+2`, the existing
merge budget suffices. Strict rank descent bounds recursive depth. Thus:

- `ExactLin.complete`: any exact derivation fits depth strictly above its rank;
- `linearize_exact_iff`: the existing public entrypoint succeeds exactly for the
  independent exact derivation, under existing base admission;
- `linearizeF_unique`: all successful recursive fuel choices agree by exact C3.

The existing public fuel is proved sufficient under the requested invariants.
No insufficient-public-fuel counterexample or API change is needed or claimed.

## Constructive graph failures and constructor-name sequences

`GraphBlocked` records a finite path to a genuinely stuck merge with exact
child derivations. `graph_trace_or_blocked` covers arbitrary admitted graphs;
`linearize_none_iff_blocked` identifies public failure exactly with this finite
certificate. Its all-fuel refusal theorem needs no admission premise once a
certificate is supplied.

`CyclePath` is a nonempty inheritance path. Exact derivations strictly shorten
along such paths, so a checked cycle excludes every exact derivation and every
finite-fuel producer success, even outside admission. Under `basesOK`, strict
rank descent independently excludes cycles. Concrete self/mutual-cycle units
and an admitted acyclic ordering-inconsistent unit inhabit these controls;
obstruction propagates to an actual derived contract as well.

`ExactLin.mem_iff` characterizes reachable names. Direct-base order and complete
base linearizations remain ordered sublists of the tail. Reversal yields
`ctor_direct_order` and `ctor_monotone`; `ctor_nodup` establishes at-most-once
names in the successful public constructor sequence. These are properties of
`Env.ctorOrder`, not proofs that constructor bodies execute or complete.

## Actual declaration-position identity correspondence

`Renaming.lean` proves arbitrary support-local identity transport for candidate
admissibility, deterministic first selection, global residual removal, success
traces and stuck certificates. Its injectivity/support premises are discharged
by existing selection and admission in the graph application.

`Identity.lean` supplies an independent Nat-indexed `IdentityLin` relation over
selected declaration positions. `ExactLin.identities`, `IdentityLin.decode` and
`IdentityLin.roundtrip` prove both directions. Positional output uniqueness comes
from independent deterministic C3; every output position belongs to `Syn.graph`.

The final source-unit interface does not leave root selection as a new caller
premise. `collect_root_scope` proves the actual intrinsic collection fact;
`unit_contract_selected` derives selection from existing `contractNames`
membership. `unit_identity_iff` uses only existing base admission and that root
enumeration. `resolved_identity_iff` also discharges environment equality through
the original `Resolves'` relation. It never uses assumed public success.

Raw undeclared roots still publicly return `[c]`, exactly as the original API
does. Their sentinel is not a declaration position; controls explicitly refuse
an `IdentityLin` claim there and exhibit sentinel collisions. A duplicate-name
control shows first-match selection and exclusion of an unselected occurrence;
the same source unit fails existing no-clash admission. No universal
name-to-all-declaration-occurrences bijection is asserted.

## Controls, trust and acceptance

`Controls.lean` has arbitrary-length rejected-prefix selection, generic
cycle/duplicate/delayed-obstruction families, inhabited Nat/String traces,
zero/one-fuel boundaries, later-legal-head refusal, diamonds and shared ancestors.
`GraphControls.lean` adds actual intrinsic contract and interface diamonds,
repeated shared and redundant ancestors, mixed contract/interface inheritance,
illegal interface admission, ordering failure and propagation, self/mutual
cycles, positional order refusal, reachability, constructor subsequences,
resolution equality and duplicate/sentinel boundaries.

`Audit.lean` prints every explicit declaration signature and pins all actual
per-constant axiom sets with `#guard_msgs`: 236 declarations/constructors and
12 inductive constructor families. Only the existing standard logical axioms
`propext`, `Classical.choice`, `Quot.sound` occur; exact subsets are recorded per
constant. Independent trace uniqueness requires none. No new axiom, proof
placeholder, unsafe code, semantic assumption or heartbeat override is added.

`tests/sol-c3-exactness/manifest.json` enumerates modules, declarations,
constructors, inhabited case witnesses, used intrinsic syntax constructors,
arbitrary proof families and exact producer pins. Fixed witness mappings plus kernel-checked closed witness types, syntax values
and public API types prevent substituting unrelated existing names or weakening
required interfaces. The acceptance checker rejects
stale source/log receipts, missing/extra declarations/modules/constructors,
unsupported declaration syntax, erased pins, unapproved axioms and omitted case
families. Twenty-one general mutation controls and nine fixture-packet mutations exercise
these refusals. The full schema additionally requires exact successful source,
run-lean, KeySort and corpus receipts, final independent reviews, all checkpoints
done and no open obligations; it currently refuses the unresolved gates.
The independent kernel proofs do not assume compiler-test results.

## Runtime, gates and review history

The original clean checkout was at the exact published base on `work`; the
remote was fetched, ancestry verified and the assigned branch created without
resetting work. The first substantive merge checkpoint is commit
`a73eca5dbdce4078e6b4da793cd0499d1c6ae771`, with a verified immutable bundle/patch
under the lane's ignored `.artifacts` directory.

Lean is 4.24.0 (commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Lake
5.0.0-src+797c613. The later explicit H26 runtime-recovery authorization approves
Docker enforcement without systemd, separately from the original H26 lane
approval. The owned Docker container enforces 12 GiB, zero swap and one CPU.
Every heavyweight Lean process uses LEAN_NUM_THREADS=1 and explicit -j1. The
writer lock and parent-memory monitor preserve the H1 4 GiB reserve; interrupted
checks stop the owned container before releasing the lock. An actual cancellation
control verifies this cleanup.

Failed attempts and later passing checks are recorded in `evidence/`; see
`fixture-reviews.md` for setup-attempt corrections and interrupted diagnostics.
A fresh permitted KeySort rebuild/check against current pinned source passed
(377 taclets, 131 read-bearing annotations) in 27.16 s. Every executable/library
in the owned worker configuration now has explicit -j1 as well.
The graph-controls target passed with its import closure in 7.10 s; graph audit
discovery in 5.83 s and guarded audit in 5.08 s. These are warm/cache-aware timings,
not clean full-build claims. Build logs give maximum process/child RSS; MCP `/usr/bin/time`
figures measure its client, while receipts separately report cumulative aggregate
cgroup peak and minimum observed parent headroom. Per-file diagnostics are clean
for current graph modules. Permitted KeySort output, layer checks and exact source
pins are saved; the full final driver and fixture/trust gates remain required.

Separate read-only finder and skeptic reviews use neither Lean nor its server.
Initial merge findings (producer-based uniqueness, missing necessity, mistaken
identity wording) were fixed. Packet findings (stale receipts, incomplete
inventories, removable pins, missing delayed obstruction, scope and cancellation
bypasses) were fixed and rejection-tested. Graph reviews required actual
source-unit root evidence, interface coverage and sequence-only wording; all were
implemented and both reviewers found no remaining graph-source blocker. Graph
packet reviews also passed after fixed/typed witness and API guards, active-command
checks and 21 rejection controls addressed all confirmed findings. Both graph reviewers excluded compiler fixtures and final assignment gates from
that verdict. Separate fixture reviews subsequently accepted the aligned sources,
exact diagnostics, kernel type links, hashed evidence and negative controls.

Shared roots/module-map rows remain coordinator-owned; registration.md lists all
new modules. Existing Source, Static, core, H16/H19/H25/H22/H21 owner areas and
producer APIs are unchanged. No override-graph validation, modifier resolution,
SOL-OV dependency, push, merge, PR, new goal or reset is performed.

## Remaining original obligations

Nine exact solc 0.8.38 fixtures now pass (five positive and four negative).
The compiler digest is
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The fixture ledger pins every source, compiler identity mapping, exact negative
diagnostic and thirteen active kernel-typed observation links. Mixed/interface,
diamond, shared-diamond and redundant ancestor shapes match intrinsic controls.
The compiler rejects cyclic sources at declaration-order admission and the
ordering-inconsistent unit at Z; W propagation is separately kernel-proved.
Reverse AST name sequences are static comparisons, not execution tests. Six
compiler-comparator controls and thirty packet mutations pass.

Trust, layers, doc paths, TestSuite parity and automatic classification pass.
The actual final driver fails its registration preflight: all nine new root
imports are reserved to the coordinator. Orphans fails for those same modules;
the shared axiom inventory reports 236 new standard-only pins, with zero axiom
errors. `registration.md` and `axiom-registration.json` provide exact integration
requests. No failed gate is counted as a pass. Current-source KeySort passes
377/131. The initial full corpus run passed in 3224.40 s; the latest current-input replay passed in 35.15 s under the required envelope. The first full
default-target attempt stopped after 2040.31 s when its H1 reserve guard fired
in unmodified Source/Horizon; this is a failed/stopped gate, not a reported Lean
theorem error. Isolated Horizon recovery subsequently passed in 655.44 s.
Further default attempts stopped on H1 in unchanged baseline modules; isolated
DecisionHashesChecks (310.24 s) and OpenLoops (586.05 s) passed under identical
limits. The full default-target command then passed in 1342.03 s (3672 jobs),
with minimum reserve 6746066944 bytes. Every stopped attempt remains in evidence.
Integrated driver/gates, full-assignment readiness reviews and final seal remain open. The persistent goal stays
incomplete and owns continuation.


## Constructive order-obstruction backfill

OrderObstruction.lean adds an independent CommonOrder predicate: a duplicate-free
common supersequence of every input list. It permits extra identities, making
its impossibility result stronger. Terminal obstructions exclude every such
order by induction on the proposed order; stuck prefixes preserve impossibility
under global filtering. Thus Stuck is equivalent to absence of any common order.
Existence of a trace is equivalent to existence of a common order, while the
canonical output remains determined by first legal head selection. A compatible
reversed tie order is inhabited and separately proved noncanonical.

The bounded producer succeeds exactly when some common order exists. At every
fuel, failure is exactly order incompatibility or insufficient budget for the
unique trace. Actual String and declaration-position Nat obstruction matrices
have no common order. These are arbitrary-family kernel proofs, not only finite
example decisions. All fourteen additions have exact axiom and signature/type
pins; the predicate itself also has a generic definitional equality guard.

The final packet has nine modules and 236 explicit constants/constructors,
twelve constructor families, nineteen typed API guards, twenty-one typed
witnesses, four intrinsic syntax-value guards plus the generic CommonOrder
value guard, thirteen external-source observation links, and thirty rejected
packet mutations. Separate source finder and skeptic reviews accept this
backfill without waiving the remaining global validation gates.

Per-file diagnostics now pass all nine modules. Actual server and worker command
arguments are recorded with parsed -j1 and stack131072; an incoming MCP option
separator is stripped before adding those flags. The earlier closed CommonOrder
witness needed explicit definition unfolding for decidability; its statement
was unchanged. Four axiom-message comments needed exact line wrapping; the
actual axiom sets were unchanged. Failed attempts remain in evidence.

The owned cache-release helper uses O_RDONLY and POSIX_FADV_DONTNEED on completed
owned build/cache regular files, with both writer and Lake-client locks. It
retains all bytes/artifacts/mappings and changes no resource limit, swap setting,
reserve or proof budget. If used before an isolated recovery check, its before/
after memory record and post-advice timing are reported. It does not drop global
caches or touch source/toolchain files.

Both backfill packet reviews pass after independent lightweight source/receipt
hash comparisons (34 inputs each). This is checkpoint approval, with all failed
or pending global gates still explicit. Q-C3-REG-1 is retired: the original
coordinator-owned registration route was already authorized; no disposable
validation-copy or shared-file editing authorization was inferred.


## Published partial delivery and baseline recovery

Fetched origin/master and verified published b419c3cf4f642ae519b66bebc26cdf2f7cf93574
without moving the owned branch. All six producer pins remain byte-identical.
Published Trace matches the owned proof; published Controls matches reviewed
dc6b974c and still needs the three additive backfill controls. Seven other new
modules remain for coordinator integration. `integration-manifest.json` records
the exact remaining scoped patch and hash. The external master gate receipt
is coordinator evidence for partial publication, not this lane's final gate.

Owned cache preparation used only read-only POSIX_FADV_DONTNEED under both locks.
The recovered checks retained Lean 4.24.0, Lake 5.0.0-src+797c613, one CPU,
LEAN_NUM_THREADS=1, explicit Lean -j1, 12 GiB/no swap and the 4 GiB reserve.
`evidence/default-targets-recovery.json` enumerates commands, exits, timings,
RSS/peak boundaries and unchanged baseline hashes. Successful warm replay
receipts supplement this recovery history without relabeling stopped attempts.

The proofs, fixtures, controls and constructive obstruction backfill are complete.
Coordinator-owned shared registration and the integrated original driver remain
open. The saved packet is a blocked integration handoff, not full readiness.


## Latest publication: 89373e34cdfd6bb5db7054b1c204d01edffc5fa7

Fetched and ancestry-verified in this same owned checkout without moving the
assigned branch. Admission and Linearization are now published byte-identically,
as is Trace; published Controls still lacks the reviewed backfill. All six
producer pins remain identical. Five new modules remain: Audit, GraphControls,
Identity, OrderObstruction and Renaming, plus the Controls delta and owned
tests/checker/docs. The earlier b419/seven-module accounting is historical.

The new publication receipt/comparison checker binds exact Git objects, source
pins and remaining scoped patch; it does not claim correctness from file
presence. No source/proof/toolchain/budget changed, so earlier kernel, fixture
and runtime gates remain evidence for identical owned inputs. The coordinator's
reported exact-master gates are external partial-delivery evidence. Remaining
shared registration, integrated original driver/gates and readiness reviews
remain open. No new scope decision is requested.


## H35 VM validation and cache delivery

Fresh owned-module build, guarded axiom inventory, both kernel-control modules,
pinned compiler fixtures, acceptance controls and KeySort pass on this VM.
The owned build is a warm replay; Audit/Controls/GraphControls were separately
re-elaborated through per-file MCP. No theorem/source/proof budget changed.
H35-HANDOFF.md and evidence/h35-gates.json record commands, exits and resources.

The installed coordinator-mode ship-cache.sh exits2; this VM lacks coordinator
catalog/transport configuration. A verified72artifact/24module cache packet is
prepared, explicitly not shipped. Q-H35-CACHE-1 asks for a supported worker
shipping configuration or coordinator retrieval/import receipt. Both reviewers
approve the prepared blocked handoff after fifteen cache-verifier controls;
H35 completion, shared registration and integrated final gates remain open.


## H41 amendment and received-cache receipt (2026-11-05)

H41 supersedes the earlier worker-shipping requirement: retain verified packs
on this VM, record path/SHA, never run ship-cache.sh on a VM, and mark delivery
coordinator-pending. The coordinator reports pulling the H35 archive and
verifying SHA256 95342ae5f29dc9999bbfbeea80df80ba7d079aa8e16d447d0afed1a30a8cee32.
Receipt: /home/guilherme/.local/state/cloudvm-coord/receipts/c3-exactness-cache-received-20261105T020449Z.json
This remote receipt is user-supplied coordinator evidence, not a file read on
this VM. Local archive bytes independently match. No import success was reported.

Current delivery status is coordinator-pending. Q-H35-CACHE-1 is resolved by
H41; no shipping configuration/permission is requested. The original immutable
H35 packet remains untouched. Its historical prepared_not_shipped label is
not rewritten into an unsupported worker shipment/import claim.

Fresh origin/master observation is 1d14f57a3a048bb1c1969c4c2c958d010ab84cb5,
which still has the same four C3 modules. All six producer pins and those
published files match the previous reported publication. Five modules plus
the Controls backfill still need coordinator integration; original shared
registration and integrated driver/gates/readiness obligations remain open.
Proof/source/toolchain/budgets are unchanged, so existing VM gate receipts
remain bound to identical inputs. See evidence/h41-cache-delivery.json and
evidence/h41-master-observation.json. No ship-cache.sh invocation, new goal,
goal reset, merge, push or shared-root edit occurred in this H41 turn.


## Authorized adoption of 8495f1de (2026-11-05)

Published 8495f1deb0a95dd6b9301822d8649ab76b217681 is now a parent of the
preserved owned branch. All24 proof-closure source hashes remain unchanged.
The sole add/add conflict was Controls; its exact reviewed owned bytes remain.
Eight C3 modules are published; only Audit and the Controls backfill remain
for coordinator integration/registration, plus owned tooling/evidence/docs.
Earlier four/five-module inventories are historical. No manual unowned/shared
root edits occurred. The source/write-scope checker now requires this exact
authorized upstream ancestor and rejects every unowned delta relative to it;
all six producer pins still use the original6f3 base. Four negative scope
controls guard the operational adoption rule, with no theorem/exclusion change.
H41 delivery remains coordinator-pending; no ship-cache invocation or assumed
cache freshness. Actual new VM gates and cache/source identity follow separately.


## Follow-on adopted master f77cf60d (2026-11-05)

Adopted f77cf60d3cea8f7f1db8db29cc027532b0cd3fce into the same preserved
owned branch, with no conflicts. It includes8495; the C3 publication set is
unchanged. All24proof-closure sources, original sixproducer pins and owned
Controls bytes remain unchanged. The ownership checker now pins this exact
authorized upstream ancestor and still rejects every unowned delta/untracked
write. Original BASE/theorem/axiom/fixture guards are unchanged. Audit and
Controls backfill/shared registration plus integrated readiness remain open.
No protected Source/Core ExtCall edit, proof weakening, budget change, goal
reset, default-branch merge, push, PR or ship-cache invocation occurred. H41
delivery stays coordinator-pending. Scoped cache identity is established only by actual object checks; no
master-wide freshness is inferred from H21 shipping notices.


## Published 9584 integration and actual runtime blocker (2026-11-05)

All nine C3 modules, including Audit/Controls, are now identical to adopted
9584f9e7df09f638d9e0cb8930501d1660aa4b2f; registration and all eight source
gates pass. Prior missing-registration statements are historical. All original
producer pins and 24 Lean closure hashes remain unchanged. Independent finder/
skeptic original-queue audits find mathematical/fixture scope complete. Actual
VM owned build, fresh axiom/control MCP, pinned fixtures, 34 rejection controls,
KeySort and full corpus pass. Full run-lean.sh and isolated unchanged published
OpenLoops instead hit the unchanged H1 reserve; no full runtime/readiness pass.
See tests/sol-c3-exactness/INTEGRATED-HANDOFF.md and evidence/integrated-gates.json
for commands, exits, timings, proof boundaries, retained failures and exact
cache request. H41 remains coordinator-pending; no worker shipping/import or
master-wide cache freshness is claimed. Full driver/final acceptance remain open.


## b86 adoption and artifact-scanner repair (2026-11-05)

Verified/adopted b86ae4568cef6d6226f4d170360bbb089debe3fb preserves all C3
proof bytes and existing work. Actual owned/axiom/control/fixture/acceptance/
KeySort/corpus checks pass. All eight source gates pass after intact relocation
of the prior sealed packet outside source scanner roots: its copied Audit
caused236duplicatepins, not a published registry loss. Prior packet now at
/workspace/c3-exactness-artifacts/integrated-943fa28ff1a878d33988226f14bd6b9f98bdd5a8
with unchanged checksum manifest85a25442...ae83e4b; exact evidence and path
supersession in tests/sol-c3-exactness/evidence/b86-artifact-relocation.json.
No shared scanner/registry change. Historical OpenLoops/full-driver H1 stops
remain unwaived;277project source imports unchanged, no new cache verified,
full runtime and readiness remain blocked. See tests/sol-c3-exactness/B86-HANDOFF.md.


## Requested e684 rebase (2026-11-05)

Rebased onto e6849d3bdf516099d20c33d3581d523449764018 before this checkpoint
commit. Integrated C3 proofs were not replayed. Olda005 head/ref/bundle and334
pruned evidence files remain exactly preserved externally; pruning retained.
Owned exact-upstream guard and artifact ignore carried forward, no Lean edits.
Fresh owned kernel/axiom/control/fixture/KeySort/corpus gates pass. Shared source
inventory fails on479 rows in four tracked published files outside C3; seven
other source gates pass. Exact ledger and scope boundaries are in
tests/sol-c3-exactness/E684-HANDOFF.md and evidence/e684-inventory-gap.json.
Historical full-driver H1 failures also remain unwaived; full acceptance fails
explicitly. H41 delivery stays coordinator-pending, no shipping or freshness
claim. No premise/budget/registry change, default merge, push, PR or goal reset.


## H82 authenticated successor intake and current validation

Final stopped C3 head21043c5220a7c0390810ec7088c83a6bd9c8ff8c was verified and
merged by9192f209cd12c30a5183bc2c779a631102dc8061 before member work. Full frozen
prompt/queue/scope hashes match the receipt; delivered H82b archive, manifest,
SUMS and exact verified-final-stop member entry were checked. Metadata/frozen
assignment/stopped acknowledgement wait is resolved. External runtime/seal and
cache bytes are not included and remain unretrieved. No retired goal was woken.

All nine Lean sources and six original producer pins remain unchanged. Updated
scope baseline is the authenticated integration, not permission to edit another
area. Portable bounded timing preserves failure/signal statuses. Fresh receipt
selection is digest-bound outside Git; original tracked evidence is untouched.
An additional current-file guard prevents cached build logs alone certifying
kernel checks. It accepts exact direct elaboration or the preferred MCP Audit
diagnostic, requiring current hashes/toolchain/bounds and explicit zero errors.
Actual MCP diagnostic PASS; fresh compiler9 fixtures PASS; current fixture
checkpoint236 declarations/12families with4scope+21general+9fixture negative
controls PASS; five portable-evidence unit tests PASS; owned236pins already
registered. Canonical KeySort377/131/table131 PASS. Lean4.24.0, Lake5.0.0.

Retained CLI direct-import failures show missing physical C3 .olean files even
though cached/fetched targets exit0. MCP's supported import setup succeeds;
this does not establish CLI cache recovery or full runtime. No unchanged
OpenLoops timing STOP was repeated. Full checkpoint still refuses unfinished
full gates/reviews; global zero-error inventory has4405unrecorded changes
(last actual check), and full cache-only readiness exits3. No RUNTIME_GATE_PASS.
External solc observations, kernel proofs, constructor-name order and actual
constructor execution remain distinct. Source, theorem, budget, axiom and
exclusion bytes are unchanged. See tests/sol-c3-exactness/SUCCESSOR-HANDOFF.md
for absolute paths, measured limits/times, exact resolved/unresolved waits.


## Gate-owner hold and gate-preserving re-cut

The successor e684-to-9192 pin change, mandatory direct audit and MCP acceptance
alternative were not owner-approved and are withdrawn. Original e684 pin,
TOOLING set and every original gate function/condition are restored. Optional
successor receipts are used only as complete hash-bound pairs; absent files
fall back to original tracked evidence. No MCP result substitutes for the
required lake run. Earlier successor PASS reports under the withdrawn edits
are historical, not approved acceptance.

Six regression tests PASS, including full-module AST equality to member21043
apart from the permitted evidence-location adapter. A detached clean-checkout
check with all successor artifacts absent reaches tracked evidence without a
missing-file exception. It still refuses original scope/snapshot drift; that
is retained as failure, not waived. No pin, theorem or budget was changed to
force parity. See tests/sol-c3-exactness/GATE-RECUT-HANDOFF.md. Gate-owner route,
shared inventory, full runtime/cache/final acceptance and original external
retirement evidence remain waits. No known timing STOP was rerun.


## Evidence-authority review: substitution removed

The optional successor adapter described above is withdrawn: its index declared
both paths and hashes. The checker is now byte-identical to authenticated21043,
including its e684 pin and all original checks, and reads original tracked
audit/fixture evidence only. SUCCESSOR-EVIDENCE.json is ignored historical data.
No MCP diagnostic substitutes for the required lake run. Four regression tests
PASS, including exact-file equality and a poisoned index having no effect.
A clean checkout without successor artifacts runs without missing-file errors;
it retains original source/scope/snapshot refusals, now including upstream
Source/WellFormed.lean pin drift. No pin or gate was changed to force success.
Current acceptance remains open. See tests/sol-c3-exactness/EVIDENCE-AUTHORITY-HANDOFF.md.
