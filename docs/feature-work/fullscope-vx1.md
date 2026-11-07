# VX1 contracts and environment fields

## Scope and interfaces

VX1 covers the full-language G01 relation contracts and X02 environment fields.
The approved target has no language exclusions. Production adequacy, concrete
admission and environment-field integration remain separate proof obligations.

The intrinsic contract modules are:

- `Solidity/Language/EnvironmentFields/Contracts.lean`: artifact-indexed inputs,
  ordered observations, byte memory, physical fields and two-sided run-indexed
  certificates in `Solidity.Roadmap.FullScope`.
- `Solidity/Language/EnvironmentFields/Frozen.lean`: the versioned `V1` consumer
  interface. Preserve its statements and dependent definitions; interface changes
  require a separate version and compatibility adapter.
- `Solidity/Language/EnvironmentFields/Consequences.lean`: conditional backward
  completion and exact-observation consequences of that certificate.
- `Solidity/Language/EnvironmentFields/ContractControls.lean` and
  `Solidity/Language/EnvironmentFields/FrozenControls.lean`: inhabited interface
  models and falsifying controls, not production Source/EVM certificates.

The following are approved full-scope obligations, not claims that every
generic V1 field establishes them operationally.

D1 binds artifact, oracle and resources per run in both refinement directions.
D2 requires exact pinned gas behavior and creation-size failures. D3 requires
solc-compatible physical storage/transient layout and byte-memory refinement.
D4 admits unsafe assembly with proved writeback and opaque optimization.
D5 retains only approved crypto/chain premises. D6 preserves observations under
its specified gas-value quotient; cost improvement is a separate obligation.

## Production linkage boundaries

The generic V1 bundle does not itself identify production source or target
operational semantics. Concrete adapters must establish independent source
legality, original Forward/Guard meanings, unconditional coverage, oracle/query
provenance and actual operational resource alignment. Gas charging, physical
layout agreement, reachable-state representability and unsafe writeback are
proof obligations, not additional assumed public premises.

The positive FrozenControls model uses Unit environments and artifact/oracle
inputs; it is not `Source.sourceLang` or `sessionAt`. The intentional control in
`tests/fullscope-20261104/vx1/EmptyDomainControls.lean` shows that admitted,
compiled inputs and live generic D2/D3/D4 witnesses do not imply an eligible
execution when Allowed domains are empty. Preserve this control; concrete
producer linkage must establish actual eligible environments and runs.

### H70 all-30 staged manifest and generator inventory

H37/H70 withdraws all thirty former language exclusions as open whole-language
work. The staged proposal keeps missing production support explicit and retains
structured unsupported diagnostics. It does not make an unimplemented feature
present or admit source constructs merely because their target scope changed.

The checker-read fixtures and generator adapter are in
`tests/fullscope-20261104/vx1/manifest-rescope/`. Keep the active catalog and
admission diagnostics consistent when integrating the adapter. The baseline
catalog has not yet been replaced by the staged proposal. This heading is the
normative target-scope anchor consumed by the adapter checker.

## Environment fields and remaining work

X02 must carry universally quantified chain inputs through source semantics,
admission, lowering and compiler execution, with exact fork availability.
Existing fork/environment producers retain their implementation roles; do not
duplicate the G31 backend environment proofs. The checker-read field/fork census
and premise-accounting fixtures remain under `tests/fullscope-20261104/vx1/`.
They do not establish end-to-end producer adequacy.

Source linkage belongs to H125 vy1-words; aggregate lifecycle remains V10.
G01 EVM/resource linkage routes to v17-validation-release and executable-bytecode.
VX1 owns OpenLoops proof-module content and memory/time splitting. Native-browser
owns slow-library registration, generated roots, module-map rows and its runner/
planner. Slow classification cannot waive the applicable proof budget or hide
an unfinished obligation from full validation.

## Evidence policy

Receipts, logs, timings, handoffs, source-review packets, checksums and historical
validation records live in the private coordination repository under
`evidence/solidity-fullscope-20261104/vx1-contracts-environment/`. They are not
public code-branch artifacts. Checker-read semantic fixtures and source code
remain here. Private archive delivery is not proof, integration or performance
acceptance; pending producer, cache, catalog and OpenLoops obligations stay open.
