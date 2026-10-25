# The examples site

<https://solidikey.github.io/solidity-lean/> shows the examples the way the
editor does: the source on the left and, for the line you click, the goal Lean
shows with the cursor at its end and the messages on it. The project picker
switches between the core's Solidity examples and Velvet's (`bridge.md`,
"Velvet"); the URL names the project, file and line
(`#project=Solidity&file=Solidity/Examples/Tactics/Tour.lean&line=43`), so a
link opens on that line.

GitHub Pages runs no Lean, so the page is read-only: every goal and message on
it was recorded from Lean's language server when the site was built, and none
is computed in the browser. To change an example and see it re-checked, open
it in an editor (the page's About box has the commands).

## How it is built

`.github/workflows/pages.yml` runs on every push to the default branch, and
by hand (`workflow_dispatch`) on any branch:

1. **Build** the project's libraries: `lake build Solidity SolkeyTestSuite`
   in the root (the core and solkey's test suite), or
   `lake build Velvet VelvetExamples SolidityVelvet` in `Bridge/` (Mathlib
   from its cache). The two projects are separate jobs.
2. **Record** with `node scripts/site/export.mjs --project <id> --out _site`.
   It starts `lake serve` (with `--tstack=131072`, as the editor), opens each
   example, waits until the file is elaborated (`textDocument/waitForDiagnostics`),
   and asks at the last non-blank column of every line for the tactic goal
   (`$/lean/plainGoal`) or, failing that, the expected type
   (`$/lean/plainTermGoal`). Diagnostics and goals go to
   `_site/data/<project>/`, one JSON file per example and an `index.json`
   with titles (the module docstring's `# ` heading and first paragraph), the
   commit and the toolchain.
3. **Assemble** the viewer (`site/index.html`, `site/app.js`,
   `site/style.css`, `site/examples.json`) with whatever was recorded. A
   project whose job failed shows as not recorded; the other still deploys.
4. **Deploy** to Pages, from the default branch only. On another branch the
   site is uploaded as the run's `github-pages` artifact instead.

The repository's Pages source must be **GitHub Actions** (Settings → Pages →
Build and deployment → Source), once.

`node --test scripts/site/export.test.mjs` checks the recorder against a
stand-in language server, without Lean; `lean.yml` runs it.

## Adding an example

Add a row to `site/examples.json` under its project: the `file` relative to
the project's `root`, and a `group` for the picker. The file must be built by
the project's step 1 (for the core, imported from `Solidity.lean` or
`SolkeyTestSuite.lean`). The title and summary come from the file's module
docstring; give `title` in the row for a file without one. A long file costs
its elaboration time again in the site's build, plus one or two goal requests
per line.

To look at the viewer locally, record one example and serve the result:

```sh
lake build Solidity
node scripts/site/export.mjs --project Solidity --out _site --only Solidity/Examples/Tactics/Tour.lean
cp site/index.html site/app.js site/style.css site/examples.json _site/
python3 -m http.server -d _site 8000
```
