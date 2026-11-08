# Working in this repository

A dependency-free Lean 4 model of [SolKey](https://github.com/SolidiKeY/solkey).

## Start with the code

Use `rg` and local imports to locate definitions, proofs and tests. Read only
the [guidance](docs/README.md) relevant to the task. Documentation should keep
commands, non-obvious constraints, external assumptions and unresolved decisions;
implementation descriptions and completed-work histories belong in code and Git.
New guidance must be linked from an existing reachable document.

## Constraints

- Keep the core dependency-free; optional integrations belong in `Bridge/`.
- Keep statements, formulas, terms, states and values intrinsic. Read
  [Gate G0](docs/intrinsic.md) before changing their representation.
- Match SolKey rule names, shapes, schema variables, side conditions and branches;
  use `dl{ … }` / `tm{ … }` with matching printers. Preserve the
  [rule correspondence](docs/lean-key-rule-map.md) and
  [semantic deviations](docs/solc-alignment.md).
- Keep imports local and acyclic; the core must not reach elaborators, printers
  or tactic front ends. Register modules with `scripts/coord-tools/register.sh`,
  add their area fragment under `docs/module-map/<area>.d/`, and run
  `scripts/coord-tools/fragments.sh`. Do not edit generated roots or indexes.
- Read relevant [audits and prior-art studies](docs/document-index.md#guides-audits-and-performance)
  before freezing an interface.
- Check the [direction audit](docs/audits/direction.md) and [size reduction](docs/audits/size-reduction.md)
  (it links every area study) before adding a large new area.
- Warn before a refactor that may slow checking; inspect Git history for a
  speed-motivated change it would undo. Do not raise `maxHeartbeats` to save a proof.
  Finish with `simp only [...]`, explicit signatures and typed `have`s.

## Before editing

Follow the [writer lock and resource bounds](docs/contributing.md#worktrees-and-memory)
before writes or Lean checks. Preserve other writers' work; parallel lanes use
separate worktrees. Read the matching conventions (`Solidity/` omitted):

| Area | Guidance |
|---|---|
| Calculus rules and `SortCheck/` | [rule table](.claude/rules/rule-table.md) |
| `Examples/`, `Theory/`, updates and notation | [derivations](.claude/rules/derivations.md) |
| Calculus soundness and `Counterexamples/` | [soundness](.claude/rules/soundness.md) |
| `Typing/`, `Semantics/` | [typing](.claude/rules/typing.md) |
| Rules and closer repairs | [rule repair](docs/rule-repair.md) |
| Tactics | [development](docs/contributing.md#tactics) |

## Verification

Use per-file diagnostics through the [lean-verify skill](.agents/skills/lean-verify/SKILL.md).
Import changes and final Lean integration need the [full gates](docs/contributing.md#checks);
documentation-only changes need path, navigation and generator checks.
Before pushing, merge `origin/master` and run `scripts/coord-tools/gate.sh touched` on the
merged tree; it also builds the library modules that import a change ([before pushing](docs/contributing.md#before-pushing)).
End each milestone with independent read-only finder and skeptic reviews per area;
neither uses the Lean server. Fix findings and record their resolution concisely.
