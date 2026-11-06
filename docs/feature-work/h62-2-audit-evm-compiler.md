# H62 item 2: frozen EVM compiler hypothesis audit

Status: **blocked on SCOPE1; full assignment unfinished**. This checkpoint
contains reviewed additive backfill, not completion of the four-checkpoint queue.

## Frozen checkout and scope

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-2-20261106/audit-evm-compiler`.
Owned worktree: `/workspace/audit-evm-compiler`; the older clean
`/workspace/solidity-lean` checkout was preserved. Fetch established that the
base is an ancestor of published `origin/master`. No push, merge, PR, deployment,
central registration or original-interface edit was performed.

Writes are confined to this document and the assigned tests/scripts prefixes.
All 160 mapped original files and the module map match their frozen Git blobs.
The core/import graph, intrinsic representations and proof budgets are unchanged.

## Queue and coverage

1. Inventory: partial. The deterministic source census records every one of
   1,830 theorem declarations in the 160 mapped files, including private and
   no-premise declarations. Exactly 499 have extracted kernel types from 14
   built modules; 1,331 declarations / 146 modules await inspection. Full
   producer-owner reconciliation remains pending. Snapshot write-owner
   candidates occur on 570 rows; migration overlays occur on all rows and
   never establish producer ownership. The snapshot has no confirmed producer
   assignment for these records. One duplicate public source name,
   `Solidity.Evm.Memory.StateRepr.stack`, occurs in MemoryCapture and
   MemoryStructDefaultSource; this is an unresolved identity candidate,
   not a claimed build failure.
2. Joint witnesses: blocked. Five original compiler headlines each have a
   simultaneous witness for every premise, on the same admitted nonempty
   setAge program/state/machine. Five Layout separation lemmas provably have
   no simultaneous witness. The other 1,820 source declarations remain
   pending classification/witness review; this includes declarations whose
   interface status or need for a witness is undecided. No premise was added
   to an original theorem. The five impossibility controls retain the literal
   requirement and blocker. See the owner ticket in the assigned tests folder.
3. Success/totality: partial. The public compileProg implementation admits and
   executes setAge, changes storage slot 13 from zero to ten, and ends with
   zero pending jumps. Reject-all, always-revert, empty-code and trailing-jump
   candidates fail that observation. Overflow produces exact reversion. A
   generic theorem transfers an assumed source success for supported non-paying
   programs to target success; its source-success premise is also witnessed
   jointly with every other premise on setAge. Source totality for every supported program,
   all public contracts and observable gas/fork behavior remain unfinished.
4. Fidelity/verification: partial. Source signatures and full Expr kernel
   types have SHA256 evidence; all original-to-proof links are unique and
   frozen-signature checked. Lean separately checks the linked proofs, and
   finder/skeptic separately compare the packages to original hypotheses.
   The reconciler itself does not certify those proof links. No full-task
   validation or full affected-library gate has been claimed.

## Premise meaning

For the five headlines, there is no globally quantified Producer structure.
Fragment admission, Sim for the actual input pair, capacity/push bounds,
no-pay flags, successful execution and initial balance consistency are per-input
conditions. HeadlineAudit proves them together, using one coherent tuple of
contract, contexts, program, flags, source state and target machine.

LayoutAudit also exhibits individually inhabited mapping regions while proving
that their forbidden overlap cannot be inhabited. This distinguishes individual
inhabitation from a simultaneous witness. These intentional separation lemmas
are useful correctness facts; their impossibility blocks the literal audit
requirement, rather than establishing a compiler defect. Global versus per-input
classification for every other declaration remains pending. The census field
is_prop_binder only records whether a domain is Prop; Type-valued certificates
still require audit.

## Toolchain, resources and validation

Actual Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Actual Lake: `5.0.0-src+797c613`. The frozen audit is not a migration lane;
TC1 asks whether the coordinator intends a second v4.35.0 audit validation.
The supplied official v4.35.0 pin and all coordinator input hashes were checked.
No alternate v4.35.0 build or v4.24.0 migration cache was introduced.

KeySort passed before proof work. Lean MCP tools were not exposed, so per-file
checks used bounded lake env lean with explicit -j1, 131072 stack, one heavy job
and the writer lock. The runtime guards host/cgroup headroom, a four-GiB reserve,
no host swap, a per-process address-space limit and sampled aggregate RSS. It
kills only its own process group on timeout/resource violation. Acceptance
controls verify timeout descendant cleanup and refusal of missing -j1.
Initial metrics named maxrss describe the largest waited child; final records
use explicit sampled-group and largest-child names. No systemd-run was used.

Frozen dependency build: 62 jobs, exit 0, 282.08 s. Initial external-cache fetches
reported success while omitting three oleans; these artifacts were rebuilt with
cache reuse disabled. The broad multi-environment metadata inspector first hit
its default heartbeat budget and later crashed. One fresh process per mapped
module fixed extraction; proof budgets were never raised. Raw failure evidence
is retained alongside successful replacement runs.

All three audit proof files pass. Their 23 new theorem declarations use only
propext, Classical.choice and Quot.sound as applicable; zero authored sorry,
new axioms, native_decide or raised heartbeat options occur. Compiler-source
statements and all original files remain unchanged. Exact commands, exits,
axiom output and resource records live in the external evidence directory.

Matched Layout checking around additive validation, same tree/cache/resources:
median 2.84262 s before and 2.82415 s after, delta -0.65%, within the 10% rule.
This measures unchanged Layout checking; it is not a whole-build performance
result. Full run-lean.sh, the optional Bridge modules and the remaining module
and statement census are pending. The global documentation-path check fails
on an unchanged after-roadmap-va1 attribution into the absent optional Mathlib
checkout (MathlibTest/SplitIfs). The owned references resolve; no out-of-scope
placeholder or documentation edit was introduced.

## Independent reviews

Read-only finder and skeptic used no Lean server and made no fixes themselves.
Confirmed extraction findings (attributes, equation bodies, mutual blocks,
context-history wording and frozen-blob verification) were fixed. Runtime
process-tree/headroom findings were fixed. The success predicate was strengthened
from arbitrary pending jumps to zero pending jumps, with an explicit negative
regression. Both reviewers checked all five joint packages against frozen
Correct signatures and accepted the reviewed subset. They retain the limits
above, including unresolved owners and the distinction between reconciler
metadata and separate kernel evidence. Detailed receipts are external.

## Reproduction and handoff

The assigned scripts contain deterministic census, reconciliation, external
configuration, per-module isolation, bounded execution and timing tooling.
Bulk inventories, logs, kernel expressions and build artifacts stay off Git.
coverage.json contains ten reviewed links, not bulk census output.
Registration suggestions are supplied only as an additive fragment under tests.

External directory: `/workspace/audit-evm-compiler-evidence`.
The final handoff there records full committed head, original goal/context,
commands, pending obligations, patch/bundle paths and SHA256 manifest. Resume
this same original goal/VM/branch after the coordinator resolves SCOPE1; do not
create a replacement goal or take another lane's files. The goal is blocked,
not complete. No empty marker commit is needed.
