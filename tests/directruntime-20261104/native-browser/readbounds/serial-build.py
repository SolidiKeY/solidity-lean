"""Guard ReadBounds importer rebuilding against an aggregate/module timer mixup.

This is a dependency-ordered local build helper, not the H127 authenticated
measurement runner. It authenticates tracked source bytes and stops on the first
failed 300-second target invocation. No runtime or performance acceptance follows.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, time

ROOT = pathlib.Path(__file__).resolve().parents[4]
TARGET = "Solidity.Tools.DirectRuntime"
LAKE = ROOT / ".lake/native-browser-rowsnine-gates/bin/lake"
PINNED = pathlib.Path("/workspace/.setup/tools/lean-4.24.0-linux/bin")

def execution_inputs():
    paths = [ROOT / "lakefile.toml", ROOT / "lean-toolchain",
             ROOT / ".lake/native-browser-serial.toml", LAKE,
             PINNED / "lake", PINNED / "lean"]
    return [{"path": str(p), "sha256": sha(p.read_bytes())} for p in paths]


def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])

def prepare():
    entries, visiting, seen = [], set(), set()
    def visit(name):
        if not name.startswith("Solidity."):
            return
        if name in visiting:
            raise ValueError("import cycle: " + name)
        if name in seen:
            return
        visiting.add(name)
        relative = name.replace(".", "/") + ".lean"
        data = (ROOT / relative).read_bytes()
        if data != git("show", "HEAD:" + relative):
            raise ValueError("source differs from HEAD: " + relative)
        # Only the leading import header is relevant. Later docstrings may
        # contain prose beginning with the word "import".
        text = data.decode()
        imports, pos = [], 0
        while pos < len(text):
            if text[pos].isspace():
                pos += 1
                continue
            if text.startswith("--", pos):
                end = text.find("\n", pos)
                pos = len(text) if end < 0 else end + 1
                continue
            if text.startswith("/-", pos):
                depth, pos = 1, pos + 2
                while depth and pos < len(text):
                    if text.startswith("/-", pos):
                        depth, pos = depth + 1, pos + 2
                    elif text.startswith("-/", pos):
                        depth, pos = depth - 1, pos + 2
                    else:
                        pos += 1
                if depth:
                    raise ValueError("unterminated header comment: " + relative)
                continue
            if not re.match(r"import\b", text[pos:]):
                if re.match(r"(?:public\s+import|prelude)\b", text[pos:]):
                    raise ValueError("unsupported import header: " + relative)
                break
            end = text.find("\n", pos)
            end = len(text) if end < 0 else end
            values = text[pos:end].split("--", 1)[0].split()[1:]
            if not values or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", v) for v in values):
                raise ValueError("unsupported import syntax: " + relative)
            imports.extend(values)
            pos = end
        for dep in imports:
            visit(dep)
        entries.append({"module": name, "path": relative, "sha256": sha(data), "imports": imports})
        visiting.remove(name)
        seen.add(name)
    visit(TARGET)
    return {"head": git("rev-parse", "HEAD").decode().strip(), "target": TARGET,
            "deadlinePerTargetSeconds": 300, "executionInputs": execution_inputs(), "entries": entries}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("plan", type=pathlib.Path)
    p.add_argument("--run", type=pathlib.Path, metavar="NEW_LOG_DIRECTORY")
    p.add_argument("--expected-sha256")
    a = p.parse_args()
    plan = prepare()
    if a.run is None:
        with a.plan.open("x") as f:
            json.dump(plan, f, indent=2)
            f.write("\n")
        print(sha(a.plan.read_bytes()))
        return
    raw = a.plan.read_bytes()
    if not a.expected_sha256 or sha(raw) != a.expected_sha256 or json.loads(raw) != plan:
        raise ValueError("plan pin or complete current source inventory differs")
    if os.environ.get("LEAN_NUM_THREADS") != "1":
        raise ValueError("requires LEAN_NUM_THREADS=1")
    a.run.mkdir(exist_ok=False)
    for i, entry in enumerate(plan["entries"]):
        # Recheck all previously inventoried source bytes before each target.
        if execution_inputs() != plan["executionInputs"] or any(sha((ROOT / e["path"]).read_bytes()) != e["sha256"] for e in plan["entries"]):
            raise ValueError("source changed during rebuild")
        command = ["timeout", "--kill-after=10s", "300s", str(LAKE), "build", entry["module"]]
        start = time.monotonic_ns()
        with (a.run / (str(i) + ".log")).open("xb") as f:
            result = subprocess.run(command, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        elapsed = time.monotonic_ns() - start
        status = result.returncode or (124 if elapsed > 300_000_000_000 else 0)
        record = {"module": entry["module"], "command": command, "exit": status, "processExit": result.returncode,
                  "wallNanoseconds": elapsed}
        with (a.run / "targets.jsonl").open("a") as f:
            f.write(json.dumps(record) + "\n")
        print(json.dumps(record), flush=True)
        if status:
            raise SystemExit(status)
    if prepare() != plan:
        raise ValueError("source or HEAD changed before completion")

if __name__ == "__main__":
    main()
