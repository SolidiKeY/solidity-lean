# Heartbeat collector

The shared speed metric: heartbeats, not wall time (H1076). One thread, synchronous
elaboration (`Elab.async=false`, so kernel checking counts) and a 128 MiB stack
(`--tstack=131072`) give the same count on idle, loaded and repeated runs. Wall
time is reported as well, but it is informational only.

```
scripts/heartbeats/collect.sh [--timeout S] MODULE|PATH.lean...
scripts/heartbeats/collect.sh --write BASELINE.json MODULE...
scripts/heartbeats/collect.sh --check BASELINE.json [--tolerance PCT] [--min UNITS] MODULE...
scripts/heartbeats/collect.sh --lake [the options above] MODULE...
```

Imports must already be built (`lake build`, or `lake build` of the module's
imports). The driver `hbcollect` (`Tools/Heartbeats/Main.lean`) is a lake exe
outside the default targets and outside the core; `collect.sh` builds it. It elaborates the
module itself with `Lean.Elab.Frontend.processCommand` and reads
`IO.getNumHeartbeats` around each command. `trace.profiler.useHeartbeats` was
tried first. It only lists every command at threshold 0, which dumps the whole
trace tree, and collecting traces inflates the counts (by 20–40% on the fixture).

Output: one JSON line per module on stdout. Heartbeats are in `maxHeartbeats`
units (raw / 1000, three exact decimals). `heartbeats` is the sum of
`commands`. The header (imports) is counted separately.

```json
{"module":"M", "file":"M.lean", "heartbeats":313.457, "wall_s":0.06, "import_heartbeats":1041.558,
 "import_wall_s":0.2, "errors":0, "commands":[{"line":7,"kind":"theorem","name":"heavy","heartbeats":235.348}, …]}
```

A `.lean` path outside the checkout is named by its basename. `name` is the
declared name under the current namespace, or `null` (`example`, `#eval`,
anonymous `instance`, …). Exit status: 0 = success, 1 = elaboration
errors or ratchet failure, 2 = usage or build error, 124 = `--timeout` expired.
`--timeout` is only a backstop against hangs and is off by default.

## One elaboration (`--lake`)

Without `--lake` the collector writes no build product, so a module that is counted
and then built is elaborated twice. With `--lake` the counted run is the module's
`lake build` (H1088): `collect.sh` runs `lake build MODULE` with `LEAN_SYSROOT` set to
a temporary copy of the toolchain made of links, whose `bin/lean` starts
`hbcollect --lean` for that one module and the real `lean` for anything else. The
driver takes the arguments Lake gives `lean` (`-o`, `-i`, `-c`, `--setup`, `--json`),
reads the imports Lake resolved, writes the `.olean`, `.ilean` and `.c`, and prints its
messages as `lean --json` does. Lake hashes the files and writes the trace itself, and
a trace names the toolchain by `lean --githash`, so Lake with the real `lean` then
takes the module as up to date and builds its importers against it. The JSON line and
the counts are the same as without `--lake`.

- A module that is already up to date is not elaborated: no line, a note on stderr,
  exit status unchanged. `--timeout` covers the whole `lake build`, imports included.
- The `.olean` is byte for byte the one `lean -DElab.async=false` writes. It can differ
  from the default (asynchronous) `lean`'s in the order of its constants, so an
  importer built against the other one is rebuilt once.
- The `.ilean` lists the imports but no references: info trees stay off, because
  recording them changes the counts. Editor "find references" for such a module needs a
  normal rebuild of it.
- Files with a `module` header, plugins, dynlibs and other `lean` arguments are
  refused (exit 2) rather than built differently.

`scripts/ci/build-slow-examples.sh` uses this for every slow module it has to rebuild.

## Ratchet

Baselines are JSON (`collect.d/ratchet.py`). `--write` records each module's total,
plus every command of at least `min_units` (default 10), keyed by name or
`kind#n`. It keeps other modules already in the file, and it refuses to write a
module that has errors. `--check` fails when a module or recorded
command exceeds its baseline by more than `--tolerance` percent (default 1) and by
more than 1 unit. A decrease, a new entry or a removed entry only prints. Baselines are
per module and per declaration, never one global number: milliseconds per heartbeat
vary 2.5× across modules. Regenerate them with `--write` on the merged head (or
the merge base) and check them in; consumers (hb1–hb3) own their baseline files.

Self-test: `python3 -B tests/heartbeats/test_collect.py`. It writes its fixture
(no new Lean lines under `tests/`) to a temporary file and checks that the
fixture's `decide +kernel` proof is counted, that repeated runs agree and that
the ratchet behaves as described. For `--lake` it sets up a small Lake project in a
temporary directory and checks that the counts equal the plain collector's, that Lake
takes the module as up to date, and that an importer builds without elaborating it again.
