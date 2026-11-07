# H28 mutation tools

## Current, self-contained (any checkout)

| Tool | Role |
|---|---|
| `sites.py` | Mechanical census: every constructor of `Taclet`, `LeanTaclet`, `CallbackTaclet`, `Rule`, and every match of each family operator in its premise text, plus the `Tms` helper operators. `--summary` prints counts. |
| `freeze.py` | Writes the frozen schema-3 `manifests/h28-full.json`: the census, the hand-selected semantic cases of the frozen pilot manifests (also run through the proof oracle), and the runner controls. |
| `mcprun.py` | Runs a frozen schema-3 manifest. Each check is a scratch file in the ignored `../.scratch/`, elaborated by the Lean language server through `scripts/coord-tools/lean-mcp` (several daemons with private sockets, one open file each). Writes one JSON record per check (diff, scratch hash, timing, all diagnostics, decision) and `summary.json`. |
| `test_mcprun.py` | Self-tests of the runner's decisions (false kills, false passes, unrun accounting). |

Run from the repository root:

```
python3 tests/h28-sol/mutation-testing/tools/freeze.py
python3 tests/h28-sol/mutation-testing/tools/mcprun.py run \
  tests/h28-sol/mutation-testing/manifests/h28-full.json OUT --jobs 3
(cd tests/h28-sol/mutation-testing/tools && python3 -m unittest test_mcprun)
```

`mcprun.py` refuses an uncommitted manifest, oracle, tool or production
input (`--allow-dirty` is for development runs only, never recorded), and
re-hashes the production inputs and `Calculus/Taclet.lean`.

## Legacy (Codex VM only)

`engine.py`, `runner.py`, `bounded.py`, `measure.c`, `backend_controls.py`,
`probe_cases.py`, `prepare_cache.py`, `extend_callback_cache.py`, `replay.py`,
`bulk_inputs.py`, `verify_bulk.py` and the pilot manifests' cache/runtime
fields drove the Docker backend against `/workspace/...` caches and the H44
off-Git bulk archive of the Codex VM. None of that exists elsewhere and it is
not used by the current runner; the files stay for the record of the pilot
runs (`docs/feature-work/h28-mutation-testing.md`). Their digests in
`bulk-data.json` describe the Codex VM archive, which was not moved.
