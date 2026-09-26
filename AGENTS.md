# Working in this repository

A Lean 4 model of solkey, the KeY-based Solidity prover:
<https://github.com/SolidiKeY/solkey>. `lake exe solkeycheck` expects a
checkout beside this repository (`../solkey`); it takes an explicit path
(`--key`/`SOLKEY_RULES`) when it lives elsewhere.

The design follows mini-solkey (`~/projects/side-projects/lean/mini-solkey`),
a small readable copy of the calculus: typed syntax, one inductive taclet
judgement written in the calculus's notation, and a sound proof system.
`docs/kernel-port.md` says which chapter landed where and what is still to
port.

**Updates are terms** (`Update.lean`): `STerm` at `structRules.key`'s
signature, `MTerm` at `memoryRules.key`'s — `save`/`delAt` nest, and so do
`write`/`addM`/`copySt`.  An allocation is the two parallel elements KeY
writes, a push and a pop are nested writes over `size`, and
`docs/lean-key-rule-map.md` is the symbol table.  A path alias binds bare
(`{ sp := alice.account }`); a read marks the *value* side instead
(`find`/`select`/`read`).

A second consumer is **the `SolKey` reader**, a Lean reader for KeY `.key`
files in a separate repository. It imports only `Solidity.Calculus.Rules` and
`Solidity.Calculus.KeyTaclets` (and through them the syntax). That is its
whole dependency surface: renaming a `Taclet` constructor breaks its
correspondence proofs, which is the point of it. It still names the old
`RuleName` table and is to be migrated (`docs/kernel-port.md`, "Port later").

## The one hard constraint

**The package has no external dependencies.** `lakefile.toml` declares no
`[[require]]`: no Mathlib, no Loom. Keep it that way — every require added
here is a clone every consumer has to pay for. Anything a proof needs from
Mathlib is a sign the proof should be done differently, or the lemma stated
locally.

## Where things are

`docs/module-map.md` — one line per module. Read it instead of searching
when you need to know where something lives.

Layering: types and names in `AST.lean`, the typed syntax in `Syntax.lean`,
the interpreter in `Semantics.lean`, terms and formulas in `Update.lean`, the
taclets in `Calculus/Rules.lean`, everything proved about them after. Keep
imports acyclic and local. Add new modules to `Solidity.lean`:
`node scripts/check-orphans.mjs` fails on a module nothing imports.

Before editing one of these families, read its conventions file. Claude Code
loads them automatically when you open a matching file; other agents should
read them by path.

| Editing | Read first |
|---|---|
| the rule table: `Calculus/{Rules,RuleSyntax,Completeness,RuleShapes,PrintedRules,KeyTaclets}.lean`, `SortCheck/**` | `.claude/rules/rule-table.md` |
| `Examples/**`, `Theory/**`, `Update.lean` (derivations and notation) | `.claude/rules/derivations.md` |
| `Calculus/{Sound*,RuleSoundness,Logic,Symex,Close}.lean`, `Counterexamples/**` | `.claude/rules/soundness.md` |
| `Typing/**`, `Semantics/**` | `.claude/rules/typing.md` |

`docs/README.md` indexes the documents. `docs/lean-key-rule-map.md` is the
authority for the name-by-name map to solkey's taclets (do not restate it in
module docstrings); `docs/solc-alignment.md` for where the interpreter follows
solc over KeY.
naming the example in `Solidity/Examples/` that is it, or the reason
there is none. Add a row there before adding one.

## Checking your work

Prefer the Lean MCP server (diagnostics, goals, hover, outline) over the
shell. Per-file diagnostics after an edit are the check; a full build is for
import changes and final confirmation. The `lean-verify` skill in
`.claude/skills/` is the loop written out.

| Command | What it covers |
|---|---|
| `./run-lean.sh` | `lake build` (default targets) then the solkey sort check |
| `node scripts/check-orphans.mjs` | every module is reachable from a library root |
| `./scripts/check-doc-paths.sh` | every backticked `*.lean` in the prose names a file that exists |
| `lake exe solkeycheck` | sort annotations against solkey's `.key` |

`solkeycheck` was at zero against solkey `8c5c69ca25` (2026-09-20). A newer
checkout reports drift (311 taclets, 5 mismatches as of 2026-09-26);
re-pinning is its own change: it regenerates `Calculus/KeyTaclets.lean`,
moves `SortCheck/Annotations.lean`, and re-partitions
`RuleShapes.taclets_partitioned`.

Run long builds in the background and grep the log for `error` rather than
reading it back whole.

## Lean notes

- Lake commands run from the project root, or use `./run-lean.sh`.
  (`scripts/lean-vscode/bin` wrappers exist only so the VS Code extension
  finds the Nix-provided `lean`/`lake` on NixOS; elan must come first on
  `PATH`, since it honours `lean-toolchain`.)
- **The language server needs `--tstack=131072`**, the number `lakefile.toml`
  already gives `lake build`: symbolic execution elaborates through deep
  recursion. The server does not read `weakLeanArgs`, so the flag is set twice
  more: `.vscode/settings.json`'s `lean4.serverArgs` for the editor, and
  `scripts/lean-mcp/bin/lake` for the MCP, whose client spawns a hardcoded
  `lake serve` with no hook for arguments.
- `lake env lean --tstack=131072 file.lean` checks one scratch file in
  seconds; the MCP server is slow on this package.
- `grind` is built in on this toolchain. Try `grind` or `grind [lemmas]`
  before a long manual script. For Boolean/bitvector goals prefer
  `bv_decide`/`omega`.
- Use `rg`, which honours `.gitignore` and so skips `.lake/`.

## Reading before writing

Module docstrings carry the conventions and the rationale for their file.
They deliberately do not restate the declarations below them, so if you want
to know what a definition is, look at the definition.
