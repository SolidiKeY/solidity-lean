# H64 merge meaning checks

`node scripts/check-meaning.mjs --build` is the mandatory `meaning` step of
`scripts/coord-tools/gate.sh touched`, `checkpoint`, and `full`. The standalone
`gate.sh meaning` mode runs just that step. In full, checkpoint and meaning modes,
preparation requests exactly the production olean targets that the live audit
imports. Lake's `--rehash build` rebuilds stale artifacts only, including separate
Corpus targets that `run-lean.sh` does not cover. No executable/native-code targets
are requested. This supplements H58's data-size check.

Touched mode passes `--build --touched`: only changed production modules, their
transitive dependents and required production dependencies are prepared. The graph
crosses core/Bridge packages and package roots. The live audit still checks every
production module; unrelated stale targets fail closed rather than being rebuilt
by a touched run. Build errors fail the meaning step before live inspection.
External prerequisites (including Bridge's core path dependency) must already be
fresh: a no-build preflight prevents compiling them with their original threading
options. Core production dependencies selected by the touched graph are prepared
first through the core's serial configuration.

The source policy reuses `blankLean` and `findings` from
`scripts/check-trust.mjs`. It rejects proof holes and new native proof/recovery
or implementation-override sites, and detects kernel-skip options in commands,
quoted macros and attributes. Existing implementation/recovery/option sites are
counted per path against the trusted merge base (`GATE_BASE`, default
`origin/master`); changing or adding a site requires review. Disabling
`Elab.async` is permitted. Production proof holes are never exempted.

The live audit calls Lean's `collectAxioms`, the API behind `#print axioms`.
It imports every production module under Solidity, SolidityBridge and
SolidityVelvet, including the separate Corpus and TestSuite libraries. It checks
every theorem, frozen production definitions and new pin targets. Frozen pin
files outside those libraries are re-elaborated; their live targets and local
declarations are audited. A project axiom fails even when unused.
Only `propext`, `Classical.choice` and `Quot.sound` are generally allowed.
`Lean.ofReduceBool` is allowed only for exact theorem names already pinned with
it in the trusted merge-base G07 inventory. This baseline has no such exceptions.
The candidate cannot widen this list by editing its inventory.

Lake's `--rehash --no-build` prerequisite checks source/dependency freshness,
including Bridge proofs. It may restore local artifacts but never compiles stale
targets. With `--build`, it repeats after preparation; direct invocation without
that flag remains an audit-only check. Anything still stale fails closed. These build freshness
hashes do not implement a frozen-statement hash policy.

Reuse boundaries:

- `check-trust.sh` remains the core implementation/recovery inventory gate.
- `check-axiom-pins.mjs` remains the textual G07 consistency gate; its collector
  also supplies current frozen targets to the live audit.
- `TrustAudit.lean` remains the selected public-bridge audit.
- `scripts/AxiomAudit.lean` remains CI's stronger safe-constant audit of the
  default libraries, with its unsafe implementation exceptions. H64 calls
  Lean's API rather than copying that dependency walker.

`--source-only` is diagnostic and never constitutes a meaning-gate pass.
Live checks run with `LEAN_NUM_THREADS=1` and `-j1`. Gate-driven builds add
`-j1` through a temporary Lake configuration's weak arguments, removed afterward.
The full build wrapper accepts that configuration through `LEAN_GATE_CONFIG`.

`node --test scripts/check-meaning.test.mjs` tests planted source escapes,
valid Lean fixtures with new axioms/native proofs/generated holes, clean proofs,
a stale-cache rejection, real stale-target preparation, unrelated stale-target
isolation, dependency preflight failure and cross-package touched selection.
It does not certify a full master pass.

Read-only finder and skeptic reviews prompted fixes for escaped options, mutable
axiom policy, stale Bridge artifacts, omitted test pins, new definition pins,
local generated axioms, full/checkpoint ordering and explicit threading.
At baseline c73b8b33f, full-master validation was blocked by missing artifacts
and a read-only toolchain artifact cache. A passing full-master timing remains
unavailable from this run.

H64b finder and skeptic review found and prompted fixes for import-header forms,
root traversal and Bridge dependency threading. The six test groups pass. Current
master's source scan passed over 7,325 files in 5.269 s at `36ccddf38`.
A local preparation probe compiled Corpus.Imported with `-j1` but failed saving
its artifact to the read-only toolchain cache. The coordinator's earlier local
full-gate log at `a348ff024` (merged with master `bfbabcaee`) records **18 s**
for meaning, stopping at seven stale Corpus modules before the live audit.
Neither duration is a passing source + build + live-audit measurement; that
measurement still requires a coordinator rerun with a writable cache.
