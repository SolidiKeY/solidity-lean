# Working in this repository

A dependency-free Lean 4 model of [SolKey](https://github.com/SolidiKeY/solkey).
Find code with `rg` and local imports; open the [guidance](docs/README.md) only
when a task needs it.

## Constraints

- The core stays dependency-free; optional integrations go in `Bridge/`.
- Statements, formulas, terms, states and values stay intrinsic
  ([Gate G0](docs/intrinsic.md)).
- Rules mirror SolKey taclets (names, shapes, schema variables, side conditions,
  branches) in `dl{ … }` / `tm{ … }` with printers; keep the
  [rule map](docs/lean-key-rule-map.md) and [solc deviations](docs/solc-alignment.md) current.
- Imports stay local and acyclic; the core never imports elaborators, printers or
  tactic front ends. Register new modules as in [contributing](docs/contributing.md#new-modules);
  never hand-edit generated roots or indexes.
- Never raise `maxHeartbeats`; warn before a change that may slow checking
  ([design and speed](docs/contributing.md#design-and-speed)).

## Workflow

- Take the [writer lock](docs/contributing.md#worktrees-and-memory) before writes or
  Lean checks; parallel work uses its own worktree.
- Area conventions (paths under `Solidity/`):

  | Area | Read |
  |---|---|
  | Calculus rules, `SortCheck/` | [rule table](.claude/rules/rule-table.md) |
  | `Examples/`, `Theory/`, updates, notation | [derivations](.claude/rules/derivations.md) |
  | Soundness, `Counterexamples/` | [soundness](.claude/rules/soundness.md) |
  | `Typing/`, `Semantics/` | [typing](.claude/rules/typing.md) |
  | Rule or closer repairs | [rule repair](docs/rule-repair.md) |
  | Tactics | [tactics](docs/contributing.md#tactics) |

- Check Lean edits per file with the [lean-verify skill](.agents/skills/lean-verify/SKILL.md).
  Before pushing, merge `origin/master` and run `bash scripts/coord-tools/gate.sh touched`
  ([checks](docs/contributing.md#checks)).
- End each milestone with read-only finder and skeptic reviews
  ([reviews](docs/contributing.md#reviews)).
