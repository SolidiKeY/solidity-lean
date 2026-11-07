#!/usr/bin/env python3
"""Task-owned bounded candidate gate. Does not claim full acceptance.
Run from any directory; SOL_QN_TOOLS selects the directory containing
lean-4.24.0-linux. Docker must expose the managed local socket.
"""
if not __debug__:
    raise SystemExit("Optimized Python disables required assertions; rerun without -O/PYTHONOPTIMIZE.")

import fcntl
import json
import hashlib
import re
import os
from pathlib import Path
import subprocess
import sys
import time
sys.dont_write_bytecode = True
from query_gate import lean_queries, compare_queries

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "tests/sol-qualified-units/evidence"
TOOLS = Path(os.environ.get("SOL_QN_TOOLS", "/home/agent/sol-qn-tools"))
# Adopted published dependency; original assignment base remains in scope.json.
REPOSITORY_BASE = "f77cf60d3cea8f7f1db8db29cc027532b0cd3fce"
MODE = sys.argv[1] if len(sys.argv) == 2 else "build"
assert MODE in ("build", "axioms", "solc", "keysort", "declarations", "queries", "repository", "signature-probes", "resolution-probes")
with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    OUT.mkdir(exist_ok=True)
    worktree_status = subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True)
    runner_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    source = ROOT / "lakefile.toml"
    original = source.read_bytes()
    temporary = ROOT / "tests/sol-qualified-units/runtime.lakefile.toml"
    configuration = original.decode().replace('version = "0.1.0"',
        f'version = "0.1.0"\nsrcDir = "{ROOT}"\nbuildDir = "{ROOT}/.lake/build"\nweakLeanArgs = ["-j1"]')
    configuration = configuration.replace('srcDir = "vendor/LeanTeX"', f'srcDir = "{ROOT}/vendor/LeanTeX"')
    environment = os.environ.copy()
    for key in ("DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"):
        environment.pop(key, None)
    name = f"sol-qn-{MODE}-{os.getpid()}"
    command = ["docker", "--host=unix:///var/run/docker.sock", "run", "--rm", "--name", name,
        "--memory=12g", "--memory-swap=12g", "--mount", f"type=bind,src={TOOLS},dst=/tools,readonly",
        "--mount", f"type=bind,src={ROOT},dst={ROOT}", "-w", str(ROOT), "-e", "LEAN_NUM_THREADS=1"]
    tracked = sorted((ROOT / "Solidity/Frontend/QualifiedUnits").rglob("*.lean"))
    scope = json.loads((ROOT / "tests/sol-qualified-units/scope.json").read_text())
    tracked += [ROOT / path for path in scope["inputs"]]
    hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in tracked}
    build_metadata = OUT / "candidate-build.json"
    if MODE in ("axioms", "declarations", "queries"):
        assert json.loads(build_metadata.read_text())["sources"] == hashes, "build freshness mismatch"
    runtime_bin = None
    runtime_wrapper = None
    stdin = None
    if MODE == "queries":
        matrix_pre = json.loads((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_text())
        compiler_pre = json.loads((OUT / "solc-report.json").read_text())
        assert compiler_pre["matrix_sha256"] == hashlib.sha256((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_bytes()).hexdigest(), "stale compiler matrix"
        assert [row["id"] for row in matrix_pre["rows"]] == [row["id"] for row in compiler_pre["rows"]], "compiler row inventory mismatch"
        for row, result in zip(matrix_pre["rows"], compiler_pre["rows"]):
            assert row["id"] == result["id"], "compiler row inventory mismatch"
            for unit, fixture in row["sources"].items():
                assert result["source_sha256"][unit] == hashlib.sha256((ROOT / "tests/sol-qualified-units" / fixture).read_bytes()).hexdigest(), "stale compiler fixture " + fixture
    if MODE == "queries":
        command += ["-i", "-e", f"LEAN_PATH={ROOT}/.lake/build/lib/lean"]
        stdin = lean_queries(json.loads((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_text()))
        command += ["debian:trixie-slim", "/tools/lean-4.24.0-linux/bin/lean", "-j1", "--tstack=131072", "--stdin"]
    elif MODE in ("axioms", "declarations"):
        command += ["-i", "-e", f"LEAN_PATH={ROOT}/.lake/build/lib/lean"]
        stdin = "import Lean\n" if MODE == "declarations" else ""
        theorem_names = []
        for path in sorted((ROOT / "Solidity/Frontend/QualifiedUnits").rglob("*.lean")):
            text = path.read_text()
            module = str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
            stdin += f"import {module}\n"
            namespace = re.search(r"^namespace (Solidity\.Frontend\.QualifiedUnits[\w.]*)", text, re.M)[1]
            theorem_names += [namespace + "." + name for name in re.findall(r"^theorem (\S+)", text, re.M)]
        if MODE == 'axioms':
            stdin += ''.join(f'#print axioms {name}\n' for name in theorem_names)
        else:
            stdin += '\nopen Lean in\nrun_cmd do\n  let env ← getEnv\n  let lanePrefix := `Solidity.Frontend.QualifiedUnits\n  let modules := env.header.moduleNames.filter (fun n => lanePrefix.isPrefixOf n)\n  let mut rows : Array Json := #[]\n  for (name, info) in env.constants.toList do\n    if let some index := env.getModuleIdxFor? name then\n      let moduleName := env.header.moduleNames[index]!\n      if lanePrefix.isPrefixOf moduleName then\n        let axioms ← collectAxioms name\n        let kind := match info with\n          | .axiomInfo _ => "axiom"\n          | .defnInfo _ => "definition"\n          | .thmInfo _ => "theorem"\n          | .opaqueInfo _ => "opaque"\n          | .quotInfo _ => "quotient"\n          | .inductInfo _ => "inductive"\n          | .ctorInfo _ => "constructor"\n          | .recInfo _ => "recursor"\n        rows := rows.push (Json.mkObj [\n          ("name", toJson name.toString),\n          ("module", toJson moduleName.toString),\n          ("kind", toJson kind),\n          ("unsafe", toJson info.isUnsafe),\n          ("partial", toJson info.isPartial),\n          ("axiom", toJson info.isAxiom),\n          ("axioms", toJson (axioms.map (fun n => n.toString)))])\n  logInfo m!"DECLARATION_INVENTORY {(Json.mkObj [("modules", toJson (modules.map (fun n => n.toString))), ("declarations", Json.arr rows)]).compress}"\n'
        command += ["debian:trixie-slim", "/tools/lean-4.24.0-linux/bin/lean", "-j1", "--tstack=131072", "--stdin"]
    elif MODE == "repository":
        subprocess.run(["git", "merge-base", "--is-ancestor", REPOSITORY_BASE, "HEAD"], cwd=ROOT, check=True)
        runtime_bin = OUT / f"runtime-bin-{os.getpid()}"
        runtime_wrapper = runtime_bin / "lake"
        node_root = Path(os.environ.get("SOL_QN_NODE", "/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin/node")).parent.parent
        python_root = Path(sys.executable).resolve().parent.parent
        command = [part + ",readonly" if part == f"type=bind,src={ROOT},dst={ROOT}" else part for part in command]
        command += ["--mount", "type=bind,src=/usr,dst=/usr,readonly",
            "--mount", f"type=bind,src={node_root},dst={node_root},readonly",
            "--mount", f"type=bind,src={python_root},dst={python_root},readonly",
            "--mount", f"type=bind,src={ROOT / '.lake'},dst={ROOT / '.lake'}",
            "--mount", f"type=bind,src={OUT},dst={OUT}",
            "-e", f"PATH={runtime_bin}:{node_root / 'bin'}:{python_root / 'bin'}:/usr/local/bin:/usr/bin:/bin",
            "-e", "GIT_CONFIG_COUNT=1", "-e", "GIT_CONFIG_KEY_0=safe.directory", "-e", f"GIT_CONFIG_VALUE_0={ROOT}",
            "--tmpfs", f"{ROOT}/Bridge/.lake:rw,noexec,nosuid,size=1m",
            "-e", "PYTHONDONTWRITEBYTECODE=1", "-e", f"GATE_LOGS={OUT / 'repository-gates'}",
            "-e", f"GATE_BASE={REPOSITORY_BASE}",
            "-e", f"SOLKEY_RULES={ROOT}/tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key",
            "debian:trixie-slim", "bash", "scripts/coord-tools/gate.sh", "checkpoint"]
    elif MODE == "keysort":
        gate = f"set -eu\n/tools/lean-4.24.0-linux/bin/lake -f {temporary} build solkeycheck\nexec ./.lake/build/bin/solkeycheck --key tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"
        command += ["debian:trixie-slim", "bash", "-c", gate]
    elif MODE in ("solc", "signature-probes", "resolution-probes"):
        node = Path(os.environ.get("SOL_QN_NODE", "/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin/node"))
        command += ["--mount", f"type=bind,src={node},dst=/usr/local/bin/node,readonly", "debian:trixie-slim", "node", {"solc":"tests/sol-qualified-units/solc-fixtures.mjs", "signature-probes":"tests/sol-qualified-units/h27-location-probe.mjs", "resolution-probes":"tests/sol-qualified-units/resolution-barrier-probe.mjs"}[MODE]]
    else:
        command += ["debian:trixie-slim", "/tools/lean-4.24.0-linux/bin/lake", "-f", str(temporary), "build", *[str(path.relative_to(ROOT).with_suffix("")).replace("/", ".") for path in sorted((ROOT / "Solidity/Frontend/QualifiedUnits").rglob("*.lean"))]]
    evidence = OUT / f"candidate-{MODE}.log"
    process = None
    minimum_available = None
    gate_passed = False
    configuration_owned = False
    runtime_owned = False
    try:
        with temporary.open("x") as configuration_file:
            configuration_owned = True
            configuration_file.write(configuration)
        if runtime_bin is not None:
            runtime_bin.mkdir()
            runtime_owned = True
            runtime_wrapper.write_text('#!/usr/bin/env bash\nexec /tools/lean-4.24.0-linux/bin/lake -f "' + str(temporary) + '" "$@"\n')
            runtime_wrapper.chmod(0o755)
        if stdin is not None:
            (OUT / f"{MODE}-input.lean.txt").write_text(stdin)
        with evidence.open("w") as log:
            log.write("COMMAND " + json.dumps(command) + "\n")
            log.write("WORKTREE_STATUS " + json.dumps(worktree_status.splitlines()) + "\n")
            log.flush()
            process = subprocess.Popen(command, cwd=ROOT, env=environment, text=True,
                stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                stdout=log, stderr=subprocess.STDOUT)
            if stdin is not None:
                process.stdin.write(stdin)
                process.stdin.close()
            while process.poll() is None:
                available = next(int(line.split()[1]) * 1024 for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:"))
                cgroup = Path("/sys/fs/cgroup")
                relative = next(line.split(":", 2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0::"))
                group = cgroup / relative.lstrip("/")
                while group == cgroup or cgroup in group.parents:
                    maximum = (group / "memory.max").read_text().strip()
                    current = int((group / "memory.current").read_text())
                    if maximum != "max":
                        available = min(available, max(0, int(maximum) - current))
                    if group == cgroup:
                        break
                    group = group.parent
                minimum_available = available if minimum_available is None else min(minimum_available, available)
                if available < 4 * 1024 ** 3:
                    subprocess.run(["docker", "--host=unix:///var/run/docker.sock", "stop", "-t", "1", name], env=environment, check=False)
                    process.wait()
                    raise RuntimeError("H1 reserve guard stopped the owned container")
                time.sleep(1)
            log.write(f"MINIMUM_AVAILABLE_BYTES {minimum_available}\n")
            log.write(f"EXIT {process.returncode}\n")
        assert process.returncode == 0, evidence.read_text()
        assert source.read_bytes() == original, "frozen lakefile changed"
        if MODE == "build":
            build_metadata.write_text(json.dumps({"sources": hashes, "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(), "command": command, "minimum_available_bytes": minimum_available, "runner_sha256": runner_sha}, indent=2) + "\n")
        elif MODE == "axioms":
            expected = json.loads((ROOT / "tests/sol-qualified-units/axiom-pins.json").read_text())
            observed = {}
            for match in re.finditer(r"^'([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", evidence.read_text(), re.M):
                observed[match[1]] = [] if match[2] is None else [name.strip() for name in match[2].split(",")]
            assert observed == expected, "live axiom pin mismatch"
            with evidence.open("a") as log:
                log.write(f"AXIOM_PINS_PASS {len(expected)}\n")
        elif MODE == "queries":
            match = re.search(r"RESOLVER_QUERY_REPORT (\[.*\])", evidence.read_text())
            assert match, "missing resolver query report"
            matrix_path = ROOT / "tests/sol-qualified-units/compiler-matrix.json"
            matrix = json.loads(matrix_path.read_text())
            compiler = json.loads((OUT / "solc-report.json").read_text())
            assert compiler["matrix_sha256"] == hashlib.sha256(matrix_path.read_bytes()).hexdigest(), "stale compiler evidence"
            observed = json.loads(match[1])
            result = compare_queries(observed, matrix, compiler)
            result.update({"observed": observed, "sources": hashes, "matrix_sha256": compiler["matrix_sha256"],
                "query_gate_sha256": hashlib.sha256((ROOT / "tests/sol-qualified-units/query_gate.py").read_bytes()).hexdigest(), "runner_sha256": runner_sha, "input_sha256": hashlib.sha256(stdin.encode()).hexdigest(), "compiler_report_sha256": hashlib.sha256((OUT / "solc-report.json").read_bytes()).hexdigest()})
            (OUT / "query-report.json").write_text(json.dumps(result, indent=2) + "\n")
            with evidence.open("a") as log:
                log.write("DIRECT_DIFFERENTIAL " + ("PASS" if result["compiler_agreement"] else "FAIL") + " " + json.dumps(result["mismatches"]) + "\n")
            if not result["compiler_agreement"]:
                print("DIRECT_DIFFERENTIAL_FAIL " + ", ".join(result["mismatches"]))
                sys.exit(1)
        elif MODE == "declarations":
            match = re.search(r"DECLARATION_INVENTORY (\{.*\})", evidence.read_text())
            assert match, "missing declaration inventory"
            result = json.loads(match[1])
            for row in result["declarations"]:
                row["axioms"] = sorted(row["axioms"])
            result["declarations"].sort(key=lambda row: row["name"])
            result["modules"].sort()
            result["sources"] = hashes
            result["runner_sha256"] = runner_sha
            result["input_sha256"] = hashlib.sha256(stdin.encode()).hexdigest()
            result["head"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            (OUT / "declaration-report.json").write_text(json.dumps(result, indent=2) + "\n")
            pins_file = ROOT / "tests/sol-qualified-units/declaration-pins.json"
            assert pins_file.is_file(), "declaration inventory saved; explicit pins require review"
            assert json.loads(pins_file.read_text()) == {"modules": result["modules"], "declarations": result["declarations"]}, "declaration inventory/pin mismatch"
            with evidence.open("a") as log:
                log.write(f"DECLARATION_PINS_PASS {len(result['declarations'])}\n")
        elif MODE == "solc":
            text = evidence.read_text()
            result = json.loads(text[text.index("\n{") + 1:text.rindex("\nMINIMUM_AVAILABLE_BYTES")])
            result["matrix_sha256"] = hashlib.sha256((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_bytes()).hexdigest()
            result["runner_sha256"] = runner_sha
            result["fixture_script_sha256"] = hashlib.sha256((ROOT / "tests/sol-qualified-units/solc-fixtures.mjs").read_bytes()).hexdigest()
            (OUT / "solc-report.json").write_text(json.dumps(result, indent=2) + "\n")
            assert result["compiler_fixtures_pass"], "compiler fixture mismatch"
        if MODE == "declarations":
            print(f"DECLARATION_PINS_PASS {len(result['declarations'])} {OUT / 'declaration-report.json'}")
        elif MODE == "solc":
            print(f"SOLC_FIXTURES_PASS {len(result['rows'])} {OUT / 'solc-report.json'}")
        elif MODE == "axioms":
            print(f"AXIOM_PINS_PASS {len(expected)} {evidence}")
        elif MODE == "build":
            print(f"CANDIDATE_BUILD_PASS {len(list((ROOT / 'Solidity/Frontend/QualifiedUnits').rglob('*.lean')))} modules {evidence}")
        else:
            print(evidence.read_text())
        gate_passed = True
    finally:
        if process is not None and process.poll() is None:
            subprocess.run(["docker", "--host=unix:///var/run/docker.sock", "stop", "-t", "1", name], env=environment, check=True)
            process.wait(timeout=30)
        if runtime_owned:
            runtime_wrapper.unlink(missing_ok=True)
            runtime_bin.rmdir()
        if configuration_owned:
            temporary.unlink(missing_ok=True)
        assert source.read_bytes() == original, "frozen lakefile changed"
        (OUT / f"gate-{MODE}.json").write_text(json.dumps({
            "mode": MODE, "passed": gate_passed, "repository_base": REPOSITORY_BASE, "lakefile_sha256": hashlib.sha256(original).hexdigest(), "process_exit": None if process is None else process.returncode,
            "sources": hashes, "runner_sha256": runner_sha, "command": command,
            "minimum_available_bytes": minimum_available,
            "log_sha256": hashlib.sha256(evidence.read_bytes()).hexdigest()}, indent=2) + "\n")
