#!/usr/bin/env python3
"""Every check CI runs is either run by the lane gate or listed as CI-only with a reason.

For .github/workflows/{lean,trust,prose-budget}.yml, every step that runs something (a
`run:` step, or a `leanprover/lean-action` step that builds) must be covered:
  * a `run:` step that calls scripts/ci/checks-fast.sh, or whose every command line equals
    a checks-fast command (or one `&&` part of one), is run by `gate.sh` (checks-fast);
  * any other step must have a row "<workflow>\t<job>\t<step>\t<reason>" in
    scripts/ci/ci-only.tsv (step = its `name:`, else its first command line).
A row naming no such step is stale and fails too. Setup steps (checkout, setup-*, cache,
artifact upload, a lean-action with `build: false`) run nothing and are skipped.
No YAML library: the workflows' block style is read line by line.
Usage: check-ci-coverage.py [ROOT]. Exit 0 covered, 1 uncovered or stale rows, 2 bad input.
"""
import pathlib, re, sys

WORKFLOWS = ["lean.yml", "trust.yml", "prose-budget.yml"]
root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")


def steps(path):
    """Yield (job, label, run_lines, uses, with_build) for each step of each job."""
    lines = path.read_text().splitlines()
    job, in_jobs, step, out = None, False, None, []
    i = 0
    def flush():
        if step is not None:
            out.append((job, step))
    while i < len(lines):
        line = lines[i]
        if re.match(r"^jobs:\s*$", line):
            in_jobs = True; i += 1; continue
        if in_jobs and re.match(r"^\S", line):
            in_jobs = False
        if not in_jobs:
            i += 1; continue
        m = re.match(r"^  ([A-Za-z0-9_-]+):\s*$", line)
        if m:
            flush(); step = None; job = m.group(1); i += 1; continue
        m = re.match(r"^(\s*)- (\w[\w-]*):\s*(.*)$", line)
        if m and job and len(m.group(1)) >= 4 and step_list_indent.get(job) in (None, len(m.group(1))):
            step_list_indent[job] = len(m.group(1))
            flush(); step = {"name": None, "run": [], "uses": None, "build": None}
            key_indent = len(m.group(1)) + 2
            line = " " * key_indent + m.group(2) + ": " + m.group(3)
        if step is not None:
            m = re.match(r"^(\s*)(name|run|uses|build):\s*(.*)$", line)
            if m:
                key, val, ind = m.group(2), m.group(3).strip(), len(m.group(1))
                if key == "run":
                    if val in ("|", ">", "|-", ">-"):
                        j = i + 1
                        while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > ind):
                            j += 1
                        block = lines[i + 1:j]
                        step["run"] = [l.strip() for l in block if l.strip()]
                        i = j; continue
                    step["run"] = [val]
                elif key == "name" and step["name"] is None and ind > step_list_indent[job]:
                    step["name"] = val.strip("'\"")
                elif key == "uses":
                    step["uses"] = val
                elif key == "build":
                    step["build"] = val.strip("'\"")
        i += 1
    flush()
    for job, s in out:
        label = s["name"] or (s["run"][0] if s["run"] else s["uses"] or "?")
        yield job, label, s["run"], s["uses"], s["build"]


step_list_indent = {}


def checks_fast_commands():
    text = (root / "scripts/ci/checks-fast.sh").read_text()
    table = text.split("checks=$(cat <<'EOF'\n", 1)[1].split("\nEOF\n", 1)[0]
    cmds = set()
    for row in table.splitlines():
        cmd = row.split("\t", 3)[3]
        cmds.add(cmd.strip())
        for part in cmd.split(" && "):
            cmds.add(part.strip())
    return cmds


def main():
    cmds = checks_fast_commands()
    listed = {}
    for n, row in enumerate((root / "scripts/ci/ci-only.tsv").read_text().splitlines(), 1):
        if not row.strip() or row.startswith("#"):
            continue
        parts = row.split("\t")
        if len(parts) != 4 or not parts[3].strip():
            print(f"ci-coverage: ci-only.tsv:{n}: need workflow, job, step, reason"); return 2
        listed[tuple(parts[:3])] = parts[3]
    seen, bad = set(), 0
    for wf in WORKFLOWS:
        global step_list_indent
        step_list_indent = {}
        for job, label, run, uses, build in steps(root / ".github/workflows" / wf):
            if not run:
                if not (uses or "").startswith("leanprover/lean-action") or build == "false":
                    continue  # setup only
            key = (wf, job, label)
            covered = bool(run) and (any("scripts/ci/checks-fast.sh" in l for l in run)
                                     or all(l in cmds for l in run))
            if key in listed:
                seen.add(key)
                if covered:
                    print(f"ci-coverage: {wf} {job} '{label}' is run by checks-fast; remove its ci-only row"); bad = 1
            elif not covered:
                print(f"ci-coverage: {wf} {job} '{label}' is neither in checks-fast nor in scripts/ci/ci-only.tsv"); bad = 1
    for key in sorted(set(listed) - seen):
        print(f"ci-coverage: stale ci-only row {key}"); bad = 1
    if not bad:
        print(f"ci-coverage: every step of {', '.join(WORKFLOWS)} is gated by checks-fast or listed CI-only ({len(listed)} rows)")
    return bad


if __name__ == "__main__":
    sys.exit(main())
