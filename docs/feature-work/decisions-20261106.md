# Coordination decisions, 2026-11-06 (H53–H64)

A durable copy of the user's decisions recorded on 2026-11-06 in the
coordinator's state file (`~/.local/state/cloudvm-coord/decisions-20261102.md`,
which stays authoritative and holds the full wording). Lanes run on Codex VMs
unless noted.

## Scope and the final theorem

- **H53.** Scope stays full: the whole language, an optimizing compiler (O)
  and solc translation validation (T); see
  [full-scope.md](full-scope.md).
- **H55.** A Codex Sol lane writes the G49/G50 public source-to-bytecode
  theorem against the frozen interfaces, every unproved piece a named typed
  premise, and reports the count of open premises with owners. It takes
  G49.01–.03 and G50.01–.02 from V16 and starts from V16's staging commit
  `e59348224` (the premise JSON stays off git). V16 keeps P8b, G18.02/.03 and
  G51.
- **H64 (1).** That lane first defines one pass template: a `PassCorrect`
  structure (one behaviour type, one transitive refinement relation), its
  transitivity lemma, the public theorem as a fold over the passes, and one
  "source does not fail" premise proved once at the source end. Each lane's
  pass theorem gets one adapter into it.

## Refactors (H57, H58)

From a read-only audit of the week's code (19 items, kept in the
coordinator's `registry/refactor-audit-20261106.md`). Mechanical work goes to
Terra, interface unification to Sol lanes. Approved with short pauses of only
the affected lanes, one at a time: merging the P8/P8b `Producer`, retiring
P10 Interface V1, merging the P1 V3 admission agreements, and putting the
outcome and word types on G01's `Roadmap.Outcome`/`Roadmap.Word` (scheduled
last).

## Infrastructure (H56, H58, H64 (2))

- Merge gate builds run on a Codex VM; the auto-continue cap is lifted (H53).
- Now: a pre-gate size check, a JSON schema for lane results, a shared build
  cache. The gate also checks `#print axioms` of public theorems against an
  allowlist and rejects `sorry`, new `native_decide` outside the allowlist,
  and options that skip kernel checking.
- Measure first: splitting Controls/Checks into their own library, per-lane
  ledger fragments, area-batched merges.
- Held until the G49 lane reports: relays via git refs and the generated
  axiom audit.

## Fleet programs (H62, H63)

1. About ten Terra VMs clean continuously (duplication, generic lemmas,
   compression, slow modules).
2. Reviewer VMs prove every interface's hypotheses satisfiable and add
   totality theorems, so a compiler that rejects everything cannot satisfy
   the public statements.
3. Differential testing (G52) against the Osaka execution-spec-tests
   fixtures, solc 0.8.38 in both pipelines and a reference EVM.
4. Per-case controls become generic lemmas or data tables.
5. A statement dependency graph generated from the Lean code, with exclusive
   claiming, replaces the prose registry over time.
6. The fleet moves from Lean v4.24.0 to v4.27 or later (module system; Lake's
   remote cache replaces the per-master cache plan). The cut-over waits for
   the coordinator's go.
7. A full kernel replay runs only at milestones (G54/G55).
