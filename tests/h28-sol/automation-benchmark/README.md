# H28 compact integration controls

The published `Solidity.Automation.H28` modules provide additive opt-in wrappers.
This increment adds portable measurement/scope utilities and seven self-contained
smoke fixtures. It does not reproduce the historical full benchmark or make a new
performance claim. The original rejection and timing limitations remain binding.

Tracked scripts are `measure.py`, `scope_policy.py`, `run_controls.py` and their
unit tests. Every Lean fixture and local Python dependency is in this directory;
Lean imports resolve to public repository modules and the pinned toolchain.
Generated proof artifacts, logs and JSON reports are runtime outputs only.

Run the dependency-free Python checks with:

```sh
PYTHONPATH=tests/h28-sol/automation-benchmark python3 -m unittest test_controls test_scope_policy
```

For the Lean smoke suite, enter an approved serial scope with at most12GiB memory,
no swap, `LEAN_NUM_THREADS=1` and at least4GiB OS headroom. Prepare the public
imports using the repository build policy. Invoke `run_controls.py` through the
project Lake environment, supplying absolute `--lean`, `--lake` and `--output`
paths. The output directory must not already exist. The script enforces the
cgroup/thread bounds and launches Lean serially with `-j1 --tstack=131072` and
unchanged180-second per-file timeouts. Isolation/headroom provisioning belongs to
the caller; this script is not a container launcher or the former benchmark.

`ContextControls.lean`, `ScalarControls.lean` and `ChainControls.lean` contain
inhabited positive proofs, exact statement checks, kernel replays and literal
axiom prints. The four `ProveZero*`/`ChainRefusal*` fixtures deliberately exit1.
Acceptance requires successful positive preludes and exactly the expected owner
refusals inside `theorem rejected`. Import errors, arbitrary errors and timeouts
fail. Diagnostic filenames must match the actual fixture. Axiom sets/signatures must match the imported original theorem or ambient Context reference, and only standard axioms are allowed. No proof statement, owner step bound or heartbeat limit is raised.

The wrappers retain original tactic search/refusal behavior under a scoped
`compiler.extract_closed=false` setting. Universal Context lemmas preserve cached
limits, heartbeat origin and diagnostics. These controls establish only their
exact statements; they do not prove whole-compiler or Source/physical adequacy.

The [private H145 evidence archive](https://github.com/SolidiKeY/solidity-lean-coord/tree/de649e9c9648443622f3fc35b24999c15ecfb27a/evidence/solidity-h28-sol-20261104/automation-benchmark/h145-code-evidence/code-evidence/tests/h28-sol/automation-benchmark) contains the optional archival VM data index by path and SHA256.
It is not an input to this runner or its tests. Delivery history begins at the
coordinator-provided rewrite base; archived history is not part of the bundle.
