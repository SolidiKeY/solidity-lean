# Original old compiler inventory: completion handoff

Lane: solidity-h62-6-20261106/migrate-yul.
Branch: codex/solidity-h62-6-20261106/migrate-yul.
Original base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
Original VM checkout: /workspace/migrate-yul.
Preserved baseline and cache view: /workspace/migrate-yul-baseline.

The clean branch was fetched and fast-forwarded onto coordinator-approved
7683091e7c35d265b3b76fdf2a93d0197ce9f556 before this increment; ebec6cb45 is an
ancestor. The frozen collector checkpoint is
4c17633935c53a960b6f045561e6bb4f7b64ad6c. The authenticated export records the
final committed head. No reset, discard, push, default-branch merge, new goal or
goal completion occurred. Handoff destination:
solidity-h62-6-20261106/migrate-root-gate, through the coordinator.

## Completed component

The old compiler-observation collection and bounded read-back checks pass all
1,774 original ordered, unique modules: 1,356 supervised one-module queries and
418 explicitly derived empty headers. Every one of the 32,734 original extra
compiler names has a recorded IR parameter/result signature; none lack an IR
lookup. Empty headers never claim a Lean query. Exact original census, summary
identities, name order, job/probe/source/output bindings, compressed bytes and
actual old toolchain versions are verified. No name was dropped or waived.
The separate completed old kernel dataset contains 55,647 declaration records
and 52,406 public records across the same 1,774 modules.

The bounded checker exited 0 in 6.045821229 seconds, with 245,600,256 bytes of
sampled peak RSS and 16,302,698,496 bytes minimum estimated availability. All
1,356 collection probes exited 0 without resource stops or swap. Their wall
times sum to 2,775.679068528 seconds; this is neither end-to-end collection wall
time nor migration-build time. Maximum sampled probe RSS was 2,083,274,752 bytes;
minimum estimated availability was 15,066,079,232 bytes. The same v3 guards,
12 GiB sampled RSS limit, 4 GiB reserve, explicit -j1 and one Lean thread were
used under the inherited 16 GiB VM cap. No systemd-run was used.

Both read-only reviewers approve the full corpus and bindings. Neither ran Lean
or wrote files. Their prelaunch finding about a contradictory zero count was
fixed before collection: counts derive from verified headers, and summaries
bind to the matching completed kernel-inventory rows. Negative controls cover
that case. All 66 Python tests pass in 24.879 seconds.

Bulk evidence remains off Git under:
/workspace/migrate-yul-artifacts/resume-7683091e7/.
Key files are full-old-compiler/manifest.json,
complete-old-compiler-inventory.json,
full-old-compiler-verification/probe-result.json, resource-summary.json,
visibility-query-provenance.json, cross-directory-dependencies.json and
python-tests-final.log. Deterministic inspectors, validators and supervisors
are committed under this lane's scripts/tests paths. Historical source-bound
inspectors remain byte-identical.

## Proof and observation boundaries

Old IR signature integrity does not establish public visibility, attribute or
instance-priority equivalence, new-toolchain compatibility, semantics or
performance acceptance. Terminal IR types retain compiler Repr text; the
validator does not typecheck IR. In both official toolchains, isDeclPublic
returns true immediately for an inspector header that is not a module. The
source paths, hashes and quotations are retained as evidence, rather than used
to authorize a public/private exclusion. Old kernel type/proof snapshots and
the actual old clean build are separate evidence.

These inventory commits change no production Lean statement, definition body,
proof budget, axiom set, interface signature or exclusion. No sorry,
native_decide or new proof axiom was added. Implemented shims and touched frozen
statements are both empty lists.

Official v4.35 archive SHA256:
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
Actual old Lean: 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake: 5.0.0-src+797c613.
Actual new Lean: 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
Lake: 5.0.0-src+eb6cafb.
Old KeySort passes with 377 taclets, 131 read-bearing and 131 table-covered.
The new KeySort Parser String API gate failed. No RUNTIME_GATE_PASS is claimed.

## Complete original queue remains

1. Census, API compatibility and old baseline: partial overall. The original
   clean v4.24 build passed 2,143 targets in 7,291.842443605 seconds, with
   8,441,331,712 bytes sampled peak RSS. Old kernel/compiler corpora are now
   complete. Public visibility, attributes and full new compatibility remain.
2. Official v4.35 migration: partial. The B05 ReservedNames kernel proof repair
   is already integrated and its signatures/axioms audited. The full new
   assigned dependency closure is not built. Public generated API preservation
   still needs coordinated shims.
3. Full new build and clean common-source before/after wall/RSS: unfinished.
   Current source has 1,811 Yul modules, 2,234 closure targets and 2,237 sources
   including KeySort-only inputs. There are 83 changed original sources.
   Historical c6 timings cannot serve as a current-tree comparison.
4. Authenticated patch, bundle, interface hashes and cross-directory report:
   partial handoff available; accepted root gates remain open. The original
   scope has 137 unchanged static boundary edges to 58 providers. Providers
   outside the project census retain null source hashes. The 37 new Yul files
   remain read-only observations. Seven of all 144 current boundary edges have
   importers outside the original scope. Static reports are not elaborated
   API proofs.

## Waits and independent backfill

- Root gate: eight Allocation kernel API differences remain unwaived, with no
  implemented shims. Two old-only extraConstNames entries,
  Solidity.Yul.Compilation.Frame.ctorIdx._boxed and
  Solidity.Yul.Compilation.Slots.ctorIdx._boxed, remain unclassified. Absence
  from the new enumeration does not prove failed direct IR lookup. Exact old
  signatures and the limited new observations remain in the evidence.
- Root gate/performance: the existing v4.35 Allocation inspection regression,
  +42.8164% wall and +119.6682% RSS, remains STOP. No unchanged new IR retry or
  expansion occurred. Old-only backfill does not waive this result. This is
  not the clean migration-build comparison.
- SortCheck: the new String.trim/dropRight Parser failure has unchanged source.
  A compatible overlay remains pending.
- Syntax, Hash, Backend and Frontend: previously reported Syntax.Raw,
  Hash.CollisionBound, Backend.Scalar.Slice and Frontend.Checked.Token failures
  have unchanged sources. Compatible producer overlays remain pending.
  Source.Ctor's producer proof update and other changed dependencies need
  renewed validation. H82 proof-only standing permission is not an exact-file
  approval blocker; ownership and frozen interfaces remain respected.

Independent backfill remains: public visibility and attribute/instance-priority
evidence; comprehensive generated public API compatibility; explicitly assigned
case/witness controls and deterministic acceptance measurements; common-source
benchmark preparation while dependencies wait. Do not weaken a statement or
approve an exclusion/premise to finish. No blanket generated-name waiver or
project-consumer rewrite substitutes for compatibility.

## Original assignment and scope retrieval

Sibling original-rendered-prompt.md contains the complete original rendered
assignment transcription. prompt-provenance.json distinguishes it from the
unavailable launcher bytes. original-work-and-backfill-queue.md preserves the
full original four checkpoints and backfill. exact-scope-manifest.json preserves
the authenticated 1,777 write-scope entries. These files are committed and
carried in the cumulative patch and complete-history bundle. Their original
SHA256SUMS remain intact. The final scope-files.json supplies absolute VM paths
and hashes, so retrieval does not depend on coordinator-local paths.

The existing original goal remains unfinished. get_goal was not exposed; its
absence is explicitly nonblocking. No goal was created, reset or completed.
Historical H82 retirement files are provenance, superseded by explicit Nov7
continuations. Fresh-thread handoff after reviewed items goes to the coordinator
under this same goal. Do not create a replacement goal, VM or competing
continuation. Preserve the original VM, branch and evidence. No H71 push
authorization was delivered, and nothing was pushed. The final export separates
inherited coordinator changes from this lane's increment and authenticates the
patch, bundle, evidence, full scope and checksum manifest.
