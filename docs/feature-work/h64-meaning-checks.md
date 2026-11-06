# H64 merge meaning checks

`node scripts/check-meaning.mjs` is the mandatory `meaning` step of
`scripts/coord-tools/gate.sh touched`, `checkpoint`, and `full`. The standalone
`gate.sh meaning` mode runs just that step. Build the production modules first;
missing or stale artifacts fail the step. This supplements H58's data-size check.

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
targets. Rebuild missing/stale targets before retrying. These build freshness
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
and a stale-cache rejection. It does not certify a full master pass.

Read-only finder and skeptic reviews prompted fixes for escaped options, mutable
axiom policy, stale Bridge artifacts, omitted test pins, new definition pins,
local generated axioms, full/checkpoint ordering and explicit threading.
At baseline c73b8b33f, full-master validation was blocked by missing artifacts
and a read-only toolchain artifact cache. A passing full-master timing remains
unavailable from this run.
