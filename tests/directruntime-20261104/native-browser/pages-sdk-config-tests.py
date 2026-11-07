"""Guard OT-PAGES-IDE: pinned container config reaches the strict WASM builder.

Executes the real shell entrypoint with a capture-only builder in bounded Docker.
This tests config plumbing, not compilation or GitHub Pages acceptance.
"""
import hashlib, json, os, pathlib, subprocess, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[3]
OUTPUT = pathlib.Path(os.environ["PAGES_SDK_TEST_OUTPUT"])
OUTPUT.mkdir(parents=True, exist_ok=False)
docker = ["docker", "--host=unix:///var/run/docker.sock"]
env = dict(os.environ)
for key in ["DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"]:
    env.pop(key, None)
results = []
with tempfile.TemporaryDirectory(prefix="pages-sdk-", dir=ROOT / ".lake") as tmp:
    tmp = pathlib.Path(tmp)
    prefix = tmp / "prefix"
    (prefix / "bin").mkdir(parents=True)
    (tmp / "work/direct").mkdir(parents=True)
    (tmp / "work/lean4").mkdir()
    probe = prefix / "bin/python3"
    probe.write_text('#!/bin/bash\nset -eu\n[[ "$EM_CONFIG" == /emsdk/.emscripten ]]\n[[ -f "$EM_CONFIG" ]]\nprintf "%s\\n" "$EM_CONFIG" "$@" > "$PROBE_OUTPUT"\n')
    probe.chmod(0o755)
    for name, inherited, config in [("unset", "", True), ("inherited-other-config", "/untrusted/config", True), ("missing-sdk-config", "", False)]:
        sdk = tmp / name
        sdk.mkdir()
        (sdk / "emsdk_env.sh").write_text(': # activation need not export EM_CONFIG\n')
        if config:
            (sdk / ".emscripten").write_text('# fixture SDK config; no compiler invoked\n')
        captured = tmp / (name + ".capture")
        command = docker + ["run", "--rm", "--memory=12g", "--memory-swap=12g", "--cpus=1",
            "--user=" + str(os.getuid()) + ":" + str(os.getgid()),
            "-v", "/workspace:/workspace", "-v", str(sdk) + ":/emsdk:ro", "-w", str(ROOT),
            "-e", "NATIVE_LEAN_PREFIX=" + str(prefix), "-e", "LEAN_BROWSER_WORK=" + str(tmp / "work"),
            "-e", "PROBE_OUTPUT=" + str(captured), "-e", "EM_CONFIG=" + inherited,
            "ubuntu:24.04", "bash", "web/tools/lean-wasm/build-direct.sh"]
        run = subprocess.run(command, env=env, text=True, capture_output=True)
        if config:
            assert run.returncode == 0, run.stderr
            lines = captured.read_text().splitlines()
            assert lines == ["/emsdk/.emscripten", "scripts/build-direct-runtime.py", str(prefix), str(tmp / "work/build64/stage1"), str(tmp / "work/direct")], lines
        else:
            assert run.returncode != 0 and "Missing pinned SDK config: /emsdk/.emscripten" in run.stderr, run.stderr
            assert not captured.exists(), "builder invoked despite missing SDK config"
        results.append({"case": name, "exitCode": run.returncode, "expectedBoundarySatisfied": True,
                        "stderr": run.stderr, "command": command})
report = {"cases": results, "passed": True,
          "entrypointSha256": hashlib.sha256((ROOT / "web/tools/lean-wasm/build-direct.sh").read_bytes()).hexdigest(),
          "boundary": "Real shell entrypoint; fixture SDK plus capture-only Python builder. No Lean, compiler, runtime or website build and no CI success claimed."}
(OUTPUT / "controls.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": True, "cases": len(results)}))
