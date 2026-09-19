# Working in this repository

A Lean 4 model of solkey, the KeY-based Solidity prover:
<https://github.com/SolidiKeY/solkey>. `lake exe solkeycheck` and
`scripts/solkey-port.mjs` expect a checkout beside this repository
(`../solkey`); both take an explicit path (`--key`/`SOLKEY_RULES`,
`--solkey`) when it lives elsewhere.

A second consumer is **the `SolKey` reader**, a Lean reader for KeY `.key`
files in a separate repository. It imports only `Solidity.Rules` (and through
it `Solidity.AST` and `Solidity.KeySort`). That is its whole dependency
surface: renaming a `RuleName` or changing a `ruleEffect` arm breaks its
correspondence proofs, which is the point of it.

## The one hard constraint

**The package has no external dependencies.** `lakefile.toml` declares no
`[[require]]`: no Mathlib, no Loom. Keep it that way — every require added
here is a clone every consumer has to pay for. Anything a proof needs from
Mathlib is a sign the proof should be done differently, or the lemma stated
locally.

## Where things are

`docs/module-map.md` — one line per module, with the open problems flagged.
Read it instead of searching when you need to know where something lives.

Layering: syntax in `AST.lean`, rule enumeration in `Rules.lean`, proof
relations in later files. Keep imports acyclic and local. Add new modules to
`Solidity.lean`.

Before editing one of these families, read its conventions file. Claude Code
loads them automatically when you open a matching file; other agents should
read them by path.

| Editing | Read first |
|---|---|
| `Rules.lean`, `RuleSyntax.lean`, `Uniqueness.lean`, `RuleValidation.lean`, `RuleShapes.lean`, `TacletAnnotations.lean` | `.claude/rules/rule-table.md` |
| `Examples/**`, `Update/**` (derivations and notation) | `.claude/rules/derivations.md` |
| `RuleSoundness.lean`, `Wp/**`, `Counterexamples/**` | `.claude/rules/soundness.md` |
| `Theory/**` (the term algebras and their rule names) | `.claude/rules/derivations.md` |
| `StorageTyping.lean`, `StateTyping.lean`, `TypeSoundness.lean`, `Reachability.lean`, `WellFormedConsumers.lean` | `.claude/rules/typing.md` |

Other prose: `docs/lean-key-rule-map.md` is the authority for the name-by-name
map to solkey's taclets (do not restate it in module docstrings);
`docs/solc-alignment.md` for where the interpreter follows solc over KeY;
`docs/compiler-verification.md`.

`docs/solkey-parity.md` is what the *interpreter* proves of solkey's suites,
`docs/calculus-parity.md` what the *rule table* does. `sol_wp` never reads
`Rules.lean`, so a number from the first says nothing about the calculus.
`docs/paper-parity.md` is the third: one row per worked example of the paper,
naming the chain in `Examples/Derivations/Paper/` that is it, or the reason
there is none. Add a row there before adding a chain.

## Checking your work

Prefer the Lean MCP server (diagnostics, goals, hover, outline) over the
shell. Per-file diagnostics after an edit are the check; a full build is for
import changes and final confirmation. The `lean-verify` skill in
`.claude/skills/` is the loop written out.

| Command | Cost | What it covers |
|---|---|---|
| `./run-lean.sh` | ~24 min CPU | `lake build` (default targets) then the solkey sort check |
| `./scripts/check-examples.sh` | ~7 min CPU | `SolidityExamples` (`Examples/Derivations/Paper/`) |
| `./scripts/check-paper-parity.sh` | seconds | `docs/paper-parity.md` names only chains that exist |
| `node scripts/check-theory-rules.mjs` | seconds | `Theory/Rewrite.lean` has a constructor per paper rewrite rule |
| `./scripts/check-solkey-parity.sh` | medium | the ported corpus against `tests/solkey/expected.tsv` |
| `./scripts/check-calculus-parity.sh` | long | the same corpus proved from `Rules.lean` alone, against `tests/solkey/expected-calculus.tsv` |
| `lake exe solkeycheck` | seconds | sort annotations against solkey's `.key` |

`solkeycheck` **currently fails**: the annotation table has drifted 78 rows
from upstream. It is pre-existing and re-syncing it is its own change,
because it also moves `SortFaithfulness.lean` and
`Counterexamples/PreFixSortAnnotations.lean`. Do not try to fix it in passing.

Run long builds in the background and grep the log for `error` rather than
reading it back whole.

## Lean notes

- Lake commands run from the project root, or use `./run-lean.sh`.
  (`scripts/lean-vscode/bin` wrappers exist only so the VS Code extension
  finds the Nix-provided `lean`/`lake` on NixOS; elan must come first on
  `PATH`, since it honours `lean-toolchain`.)
- **The language server needs `--tstack=131072`**, the number `lakefile.toml`
  already gives `lake build`. Without it a file worker on one of the worked
  derivations dies with "deep recursion was detected at 'interpreter'" before
  it reports a diagnostic, because a `sol_derivation` chain elaborates through
  a deeply recursive `rule_simp`. The server does not read `weakLeanArgs`, so
  the flag is set twice more: `.vscode/settings.json`'s `lean4.serverArgs` for
  the editor, and `scripts/lean-mcp/bin/lake` for the MCP, whose client spawns
  a hardcoded `lake serve` with no hook for arguments. The watchdog forwards
  the flag to each worker as `-s`; `ps -eo args | grep -- --worker` is how to
  check a running one has it.
- `grind` is built in on this toolchain. Try `grind` or `grind [lemmas]`
  before a long manual script. Tag safe reusable lemmas `@[grind]` when they
  do not blow up the search space. For Boolean/bitvector goals prefer
  `bv_decide`/`omega`.
- Membership proofs over the large `ruleNames` list use `decide`;
  `simp [ruleNames]` exceeds the recursion limit.
- Several files are very large (`RuleSoundness.lean` is 10k lines). Use the
  MCP outline and ranged reads; never read one whole. Use `rg`, which honours
  `.gitignore` and so skips the 541 MB `.lake/`.

## Reading before writing

Module docstrings carry the conventions and the rationale for their file.
They deliberately do not restate the declarations below them, so if you want
to know what a definition is, look at the definition.
