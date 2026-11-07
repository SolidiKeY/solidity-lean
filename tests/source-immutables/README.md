# S02-IMMUT diagnostic input

Desired admission is frozen in expected.json: a direct constructor may assign
its immutable; an ordinary function or a constant write remains refused.
The pinned compiler accepts/refuses these five fixtures in both pipelines and
both optimizer profiles. This probe checks compiler admission only, not runtime
immutable values or Source/compiler correspondence.

The unchanged Source still rejects the direct immutable constructor in both
pipelines. Its desired acceptance gate is FAIL (two mismatches), not an approved
exclusion or a passing support test. Mutable constructor and immutable initializer
positive controls execute successfully in the Source diagnostic. Those positive
#eval results are execution evidence, not kernel-proof substitutes. Kernel facts
prove the current constructor/method write rejections and erased phase identity.

ImmutableBaseline.lean.txt is the frozen diagnostic at source head
55083d60976573443c821afde569b6cd442eee5e. It is deliberately not a registered
Lean module asserting permanent rejection. The exact tested .lean copy and MCP
output are retained under /workspace/vy5-composition/h12-independent-20261102/.
Both readers pin the exact expected.json SHA before parsing it; changed
verdicts and empty/duplicate fixture catalogs cannot turn a failure green.
All reported source/helper/fixture hashes are explicit. probe.mjs takes the
pinned compiler and committed loader as arguments; it checks the helper hash
BEFORE importing it and checks fixture hashes before compilation. check-source.mjs
refuses missing, reordered, incomplete or stale Source evidence. guards.test.mjs
checks these failure paths and preserves the genuine failed support result.

Implementation is blocked on a runtime-writer decision, not missing whole-lane
publication. Source.Ctx/Frame.ctx contains no constructor identity; identical
constructor/method bodies receive the same context. LVal.state and RLVal.state
both require Decl.mutable=true, which is false for immutable variables.
A mutable-declaration view or global guard relaxation would bypass that invariant.
runInits/elabInit cannot substitute for ordered constructor assignments involving
locals/control flow. A safe constructor-specific phase/ownership capability and
resolved write operation requires the reserved evaluator/horizon cases to be
coordinated. No Source implementation or premise was changed here.

The precise owner/action question and reviewed evidence are sealed under
/workspace/vy5-composition/h12-independent-20261102/final/. H12's wave5–6
premise-only composition work remains paused. The already reviewed funds producer
is commit1f563ee7951a563ed37acb4a5fdacfda2e52ba11; it is absent from fetched
master eba99fe7c2e00926d0c830e56af34e0699d804c4. Its global affordability
ledger/body-history obligation remains distinct and open. No new full build,
TestSuite/docs/strict/trust/cumulative end-of-lane gates are claimed for this
blocked diagnostic item; only per-file and affected probe checks were run.
