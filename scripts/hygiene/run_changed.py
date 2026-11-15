#!/usr/bin/env python3
"""Run what a change adds or changes that CI or tests would execute, on HEAD.

For BASE..HEAD (rename-aware, deletions ignored) it collects:
  (a) tests: added/modified *.test.mjs|js|cjs (`node --test FILE`) and test_*.py, test-*.py,
      *_test.py (`python3 -B FILE`, or unittest discovery when the file has no __main__ guard);
  (b) workflows: for each added/modified .github/workflows/*.yml that runs on push or
      pull_request, the `run:` steps of its jobs;
  (c) callers: run: steps of any push/pull_request workflow at HEAD that name a changed path.
Steps that need Lean (lean-action, lake, elan), the network (curl, wget, gh, npm ci/install,
pip install, apt-get, docker) or only schedule/dispatch events are skipped and reported.
Commands that scripts/ci/checks-fast.sh at HEAD already runs (the lane gate and CI's
`checks` job run that script) are reported as covered and not run (--include-covered runs them).

HEAD is checked out in a temporary detached worktree (full history, so baselines that walk
merge parents work). Steps of one job run in order in one shell environment per step;
commands of different jobs/tests run in parallel (--jobs).

Usage: run_changed.py --base REV --head REV [--repo DIR] [--timeout 120] [--jobs N]
                      [--list] [--include-covered] [--json] [--keep]
A failing command is rerun at BASE (unless --no-base-check) when everything it names exists
there; failing there too makes it `pre-existing`, which does not fail the run.
A command that reaches for lake/lean/elan is stopped by shims (status needs-lean); one that
fails printing its usage is needs-args. Neither fails the run.
--block KINDS (comma list of workflow, test, validator; default all): only failures of these
kinds fail the run; the others print as ADVISORY. gate.sh touched blocks on workflow steps only
(no false alarm on 370 merged heads; tests and validators failed on about 3% for host reasons).
Exit 0: every command passed, was pre-existing, or nothing to run (timeouts, needs-lean and
        needs-args only warn); 1: a command failed at HEAD only; 2: usage, git or worktree error.
"""
import argparse, concurrent.futures as cf, fnmatch, json, os, re, shlex, shutil, subprocess, sys, tempfile, time

# ------------------------------------------------------------------ tiny YAML subset
def _strip_comment(s):
    out, q = [], None
    for i, ch in enumerate(s):
        if q:
            if ch == q:
                q = None
        elif ch in "'\"":
            q = ch
        elif ch == "#" and (i == 0 or s[i - 1] in " \t"):
            break
        out.append(ch)
    return "".join(out).rstrip()


def _scalar(v):
    v = v.strip()
    if not v:
        return None
    if v[0] == v[-1] and v[0] in "'\"" and len(v) >= 2:
        return v[1:-1].replace("''", "'") if v[0] == "'" else v[1:-1]
    if v.startswith("[") and v.endswith("]"):
        return [_scalar(x) for x in v[1:-1].split(",") if x.strip()]
    if v.startswith("{") and v.endswith("}"):
        d = {}
        for part in v[1:-1].split(","):
            if ":" in part:
                k, x = part.split(":", 1)
                d[k.strip()] = _scalar(x)
        return d
    return v


KEY = re.compile(r"^((?:'[^']*'|\"[^\"]*\"|[^:#'\"\s][^:#]*?)):(?:\s+(.*)|$)")


def yaml_load(text):
    """Block mappings, sequences, block scalars (| > with chomping), flow [] {} one-liners."""
    raw = text.split("\n")
    lines = []  # (indent, content, rawline index)
    for i, l in enumerate(raw):
        s = _strip_comment(l) if not l.lstrip().startswith("#") else ""
        if s.strip():
            lines.append((len(s) - len(s.lstrip()), s.strip(), i))
    pos = [0]

    def block_scalar(style, parent_indent, start_raw):
        body, ind = [], None
        j = start_raw + 1
        while j < len(raw):
            l = raw[j]
            if l.strip():
                k = len(l) - len(l.lstrip())
                if k <= parent_indent:
                    break
                ind = k if ind is None else ind
                body.append(l[ind:])
            else:
                body.append("")
            j += 1
        while pos[0] < len(lines) and lines[pos[0]][2] < j:
            pos[0] += 1
        while body and not body[-1]:
            body.pop()
        if style.startswith(">"):
            return " ".join(x for x in body) + ("" if style.endswith("-") else "\n")
        return "\n".join(body) + ("" if style.endswith("-") else "\n")

    def value(rest, indent, raw_i):
        if rest is None or rest == "":
            if pos[0] < len(lines) and (lines[pos[0]][0] > indent or
                                        (lines[pos[0]][0] == indent and lines[pos[0]][1].startswith("- "))):
                return parse(lines[pos[0]][0])
            return None
        if rest[0] in "|>":
            return block_scalar(rest, indent, raw_i)
        return _scalar(rest)

    def parse(indent):
        if pos[0] >= len(lines):
            return None
        if lines[pos[0]][1].startswith("- ") or lines[pos[0]][1] == "-":
            seq = []
            while pos[0] < len(lines) and lines[pos[0]][0] == indent and (
                    lines[pos[0]][1].startswith("- ") or lines[pos[0]][1] == "-"):
                ind, content, ri = lines[pos[0]]
                item = content[2:].strip() if content != "-" else ""
                pos[0] += 1
                m = KEY.match(item) if item else None
                if m and not item.startswith(("'", '"', "[", "{")):
                    # mapping inside the item: its keys sit at indent + 2
                    sub_ind = ind + 2
                    d = {}
                    d[_scalar(m.group(1))] = value(m.group(2), sub_ind, ri)
                    while pos[0] < len(lines) and lines[pos[0]][0] == sub_ind and not lines[pos[0]][1].startswith("- "):
                        _, c, r2 = lines[pos[0]]
                        m2 = KEY.match(c)
                        pos[0] += 1
                        if m2:
                            d[_scalar(m2.group(1))] = value(m2.group(2), sub_ind, r2)
                    seq.append(d)
                elif item:
                    seq.append(value(item, ind, ri))
                else:
                    seq.append(value(None, ind, ri))
            return seq
        d = {}
        while pos[0] < len(lines) and lines[pos[0]][0] == indent and not lines[pos[0]][1].startswith("- "):
            _, c, ri = lines[pos[0]]
            pos[0] += 1
            m = KEY.match(c)
            if not m:
                continue
            d[_scalar(m.group(1))] = value(m.group(2), indent, ri)
        return d

    return parse(lines[0][0]) if lines else {}


# ------------------------------------------------------------------ git helpers
class SetupError(Exception):
    pass


def git(repo, *args):
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise SetupError("git %s: %s" % (" ".join(args[:3]), r.stderr.strip()))
    return r.stdout


def changed_paths(repo, base, head):
    out = {}
    for l in git(repo, "diff", "--name-status", "-M", base, head).splitlines():
        parts = l.split("\t")
        st = parts[0][0]
        if st == "D":
            continue
        out[parts[-1]] = st
    return out


# ------------------------------------------------------------------ collection
LEAN = re.compile(r"\blake\b|lean-action|\belan\b|\blean\s+--|lean-toolchain|fetch-lake-cache|restore-lake-artifacts|build-lean-browser")
# a skipped step that builds or installs something later steps of its job may read
SETUP = re.compile(r"\blake\s+build|\bnpm\s+(?:ci|install)|\bnpx\b|build-lean-browser|git\s+clone|download-artifact")
NET = re.compile(r"\bxvfb-run\b|\bsudo\b|\bcurl\b|\bwget\b|(?:^|[\s;&|(])gh\s|\bnpm\s+(?:ci|install|i)\b|\bpip3?\s+install\b|\bapt(?:-get)?\b|\bdocker\b|git\s+push|\bnpx\b")
SCHED = re.compile(r"github\.event_name\s*==\s*'(?:schedule|workflow_dispatch|release)'")
LEAN_SCRIPT = re.compile(r"\blake\s+(?:build|env|exe|lean)\b|\belan\b|[\"']lake[\"']")
VALIDATOR = re.compile(r"^(?:check|validate|verify)[\w-]*\.(?:py|mjs)$")
TEST_JS = re.compile(r"\.test\.(?:mjs|js|cjs)$")
TEST_PY = re.compile(r"(?:^|/)(?:test[_-][^/]*|[^/]*_test)\.py$")
SKIP_TEST_DIRS = ("node_modules/", "vendor/", "/fixtures/")


def ci_triggered(wf):
    on = wf.get("on", wf.get(True))
    if isinstance(on, str):
        on = [on]
    if isinstance(on, dict):
        on = list(on)
    return bool(on) and any(t in ("push", "pull_request") for t in on)


def expr_env(v, wt):
    if v is None:
        return ""
    v = str(v)
    v = v.replace("${{ github.workspace }}", wt)
    return re.sub(r"\$\{\{.*?\}\}", "", v)


def workflow_steps(wf_path, text):
    """Yield dicts for every run: step: job, name, run, env, skip reason or None."""
    try:
        wf = yaml_load(text)
    except Exception as e:  # malformed: report as one skipped item
        yield dict(kind="workflow", job="?", name=wf_path, run="", env={}, skip="unparsed yaml: %s" % e)
        return
    if not isinstance(wf, dict):
        return
    trig = ci_triggered(wf)
    wenv = wf.get("env") or {}
    for jname, job in (wf.get("jobs") or {}).items():
        if not isinstance(job, dict):
            continue
        jenv = dict(wenv, **(job.get("env") or {}))
        lean_job = any(isinstance(s, dict) and "lean-action" in str(s.get("uses", "")) for s in job.get("steps") or [])
        needs = job.get("needs")
        setup_skipped = None
        for k, st in enumerate(job.get("steps") or []):
            if not isinstance(st, dict):
                continue
            if "run" not in st:
                uses = str(st.get("uses", ""))
                if "download-artifact" in uses:
                    setup_skipped = "artifact download"
                elif "lean-action" in uses and str((st.get("with") or {}).get("build", "true")).lower() != "false":
                    setup_skipped = "lean-action build"
                continue
            run = str(st.get("run") or "")
            name = st.get("name") or run.strip().split("\n")[0][:60]
            cond = " ".join(str(x) for x in (job.get("if"), st.get("if")) if x)
            skip = None
            if not trig:
                skip = "workflow not run on push/pull_request"
            elif SCHED.search(cond):
                skip = "schedule/dispatch-only step"
            elif LEAN.search(run):
                skip = "needs Lean"
            elif NET.search(run):
                skip = "needs network"
            elif "checks-fast.sh" in run:
                skip = "covered: checks-fast.sh (gate)"
            elif needs:
                skip = "job needs other jobs (%s)" % needs
            elif setup_skipped:
                skip = "after skipped setup step: %s" % setup_skipped
            if skip and SETUP.search(run) and not setup_skipped:
                setup_skipped = name
            yield dict(kind="workflow", wf=wf_path, job=jname, idx=k, name=name, run=run,
                       env=dict(jenv, **(st.get("env") or {})), wd=st.get("working-directory"),
                       skip=skip, lean_job=lean_job)


def checks_fast_cmds(text):
    m = re.search(r"checks=\$\(cat <<'EOF'\n(.*?)\nEOF", text, re.S)
    out = {}
    if m:
        for l in m.group(1).splitlines():
            if "\t" in l:
                n, c = l.split("\t", 1)
                out[c.strip()] = n
    return out


def path_in_run(path, run):
    for tok in re.findall(r"[\w./*{}\-]+", run):
        tok = tok.strip("'\"")
        if "/" not in tok and "." not in tok:
            continue
        if tok == path or tok.rstrip("/") == path or fnmatch.fnmatchcase(path, tok):
            return True
    return False


def collect(repo, base, head, wt, validators=False):
    ch = changed_paths(repo, base, head)
    items, covered = [], []
    cf_path = os.path.join(wt, "scripts/ci/checks-fast.sh")
    fast = checks_fast_cmds(open(cf_path).read()) if os.path.exists(cf_path) else {}
    fast_files = set()
    for c in fast:
        fast_files.update(t for t in shlex.split(c) if "/" in t)

    def is_covered(cmd):
        if cmd.strip() in fast:
            return "covered: checks-fast %s" % fast[cmd.strip()]
        toks = [t for t in shlex.split(cmd) if "/" in t] if cmd else []
        if toks and all(t in fast_files for t in toks):
            return "covered: checks-fast runs %s" % " ".join(toks)
        return None

    # (a) tests
    for p, st in sorted(ch.items()):
        if any(s in "/" + p for s in SKIP_TEST_DIRS) or not os.path.isfile(os.path.join(wt, p)):
            continue
        if TEST_JS.search(p):
            cmd = "node --test " + shlex.quote(p)
        elif TEST_PY.search(p):
            src = open(os.path.join(wt, p), errors="replace").read()
            if LEAN_SCRIPT.search(src):
                items.append(dict(kind="test", name=p, cmd="", skip="needs Lean", src=p))
                continue
            if re.search(r"sys\.argv\[[1-9]", src):
                items.append(dict(kind="test", name=p, cmd="", skip="needs arguments from a caller", src=p))
                continue
            if "__main__" in src:
                cmd = "python3 -B " + shlex.quote(p)
            else:
                d, b = os.path.split(p)
                cmd = "python3 -B -m unittest discover -s %s -p %s -t %s" % (shlex.quote(d or "."), shlex.quote(b), shlex.quote(d or "."))
        else:
            continue
        items.append(dict(kind="test", name=p, cmd=cmd, skip=is_covered(cmd), src=p))
    # (d, opt-in) changed validators: check*/validate*/verify* scripts, run without arguments
    if validators:
        for p, st in sorted(ch.items()):
            b = os.path.basename(p)
            if not VALIDATOR.match(b) or TEST_PY.search(p) or TEST_JS.search(p) or not os.path.isfile(os.path.join(wt, p)):
                continue
            src = open(os.path.join(wt, p), errors="replace").read()
            cmd = ("python3 -B " if p.endswith(".py") else "node ") + shlex.quote(p)
            skip = "needs Lean" if LEAN_SCRIPT.search(src) else (
                "needs arguments from a caller" if re.search(r"sys\.argv\[[1-9]|required=True", src) else None)
            items.append(dict(kind="validator", name=p, cmd=cmd, skip=skip or is_covered(cmd), src=p))
    # (b) changed workflows, (c) steps naming changed paths
    wfdir = os.path.join(wt, ".github/workflows")
    seen = set()
    for f in sorted(os.listdir(wfdir)) if os.path.isdir(wfdir) else []:
        if not f.endswith((".yml", ".yaml")):
            continue
        rel = ".github/workflows/" + f
        for s in workflow_steps(rel, open(os.path.join(wfdir, f)).read()):
            why = "workflow changed" if rel in ch else None
            if not why:
                hit = [p for p in ch if path_in_run(p, s["run"])]
                if hit:
                    why = "names changed " + ", ".join(hit[:3])
            if not why:
                continue
            key = (rel, s["job"], s.get("idx"))
            if key in seen:
                continue
            seen.add(key)
            s["why"] = why
            s["cmd"] = s["run"]
            if not s["skip"]:
                for tok in re.findall(r"[\w./\-]+", s["run"]):
                    f = os.path.join(wt, tok.lstrip("./") if tok.startswith("./") else tok)
                    if "/" in tok and os.path.isfile(f) and LEAN_SCRIPT.search(open(f, errors="replace").read()):
                        s["skip"] = "needs Lean (%s runs lake)" % tok
                        break
            if not s["skip"]:
                s["skip"] = is_covered(s["run"].strip())
            items.append(s)
    # tests already run by a selected workflow step are not run twice
    wf_runs = " ".join(i["run"] for i in items if i["kind"] == "workflow" and not i["skip"])
    for i in items:
        if i["kind"] == "test" and not i["skip"] and path_in_run(i["src"], wf_runs):
            i["skip"] = "run by a selected workflow step"
    return ch, items


# ------------------------------------------------------------------ running
BLOCKED = "run_changed: Lean tool blocked"
USAGE = re.compile(r"(?i)\busage: |the following arguments are required")


def make_shims(root):
    """lake/lean/elan stand-ins on PATH and under a fake HOME/.elan: any command that reaches
    for Lean stops at once (exit 97) and is reported as needing Lean, never run."""
    home = os.path.join(root, "home")
    for d in (os.path.join(root, "bin"), os.path.join(home, ".elan", "bin")):
        os.makedirs(d, exist_ok=True)
        for tool in ("lake", "lean", "elan", "leanc"):
            f = os.path.join(d, tool)
            with open(f, "w") as fh:
                fh.write("#!/bin/sh\necho '%s:' \"$0\" \"$@\" >&2\nexit 97\n" % BLOCKED)
            os.chmod(f, 0o755)
    return os.path.join(root, "bin"), home


def run_cmd(cmd, wt, env, timeout, wd=None, shims=None):
    t = time.time()
    e = dict(os.environ)
    e.update({k: expr_env(v, wt) for k, v in (env or {}).items()})
    e.update(CI="true", GITHUB_WORKSPACE=wt, PYTHONDONTWRITEBYTECODE="1")
    if shims:
        e["PATH"] = os.pathsep.join([shims[0]] + [d for d in e.get("PATH", "").split(os.pathsep) if ".elan" not in d])
        e["HOME"], e["ELAN_HOME"] = shims[1], os.path.join(shims[1], ".elan")
    try:
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", cmd],
                           cwd=os.path.join(wt, wd) if wd else wt, env=e, capture_output=True,
                           text=True, errors="replace", timeout=timeout, start_new_session=True)
        status, out = ("pass" if r.returncode == 0 else "fail"), (r.stdout + r.stderr)
        code = r.returncode
    except subprocess.TimeoutExpired as x:
        status, code = "timeout", None
        out = ((x.stdout or b"").decode(errors="replace") if isinstance(x.stdout, bytes) else (x.stdout or "")) + \
              ((x.stderr or b"").decode(errors="replace") if isinstance(x.stderr, bytes) else (x.stderr or ""))
    if BLOCKED in out:
        status = "needs-lean"
    elif status == "fail" and USAGE.search(out):
        status = "needs-args"  # a caller-driven script printed its usage: not a verdict
    return dict(status=status, code=code, secs=round(time.time() - t, 1), tail="\n".join(out.strip().splitlines()[-15:]))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--base", required=True)
    ap.add_argument("--head", required=True)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--timeout", type=float, default=120)
    ap.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 2))
    ap.add_argument("--list", action="store_true", help="only list what would run")
    ap.add_argument("--include-covered", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--keep", action="store_true", help="keep the worktree")
    ap.add_argument("--validators", action="store_true",
                    help="(d) also run changed check*/validate*/verify* scripts without arguments")
    ap.add_argument("--no-base-check", action="store_true", help="do not rerun failures at BASE")
    ap.add_argument("--workdir", help="parent directory for the worktree (default: $TMPDIR)")
    ap.add_argument("--block", default="workflow,test,validator",
                    help="kinds whose failures fail the run; others are advisory")
    try:
        a = ap.parse_args(argv)
    except SystemExit as e:
        return 2 if e.code else 0
    wt = None
    try:
        repo = git(a.repo, "rev-parse", "--show-toplevel").strip()
        base = git(repo, "rev-parse", "--verify", a.base + "^{commit}").strip()
        head = git(repo, "rev-parse", "--verify", a.head + "^{commit}").strip()
        wt = tempfile.mkdtemp(prefix="run-changed-", dir=a.workdir)
        git(repo, "worktree", "add", "--detach", "--force", wt, head)
        shims = make_shims(tempfile.mkdtemp(prefix="run-changed-shims-", dir=a.workdir))
        ch, items = collect(repo, base, head, wt, a.validators)
    except (SetupError, OSError) as e:
        print("run_changed: %s" % e, file=sys.stderr)
        if wt:
            cleanup(repo if "repo" in dir() else a.repo, wt)
        return 2
    if a.include_covered:
        for i in items:
            if i["skip"] and i["skip"].startswith("covered"):
                i["skip"] = None
    todo = [i for i in items if not i["skip"]]
    t0 = time.time()
    if not a.list and todo:
        # steps of one job run in order; tests and jobs in parallel
        groups = {}
        for i in todo:
            groups.setdefault((i.get("wf"), i.get("job")) if i["kind"] == "workflow" else (i["kind"], i["name"]), []).append(i)

        def run_group(g):
            for i in g:
                if i is not g[0] and any(x.get("status") in ("fail", "timeout") for x in g[:g.index(i)]):
                    i.update(status="not-run", tail="an earlier step of the job did not pass")
                    continue
                i.update(run_cmd(i["cmd"], wt, i.get("env"), a.timeout, i.get("wd"), shims))
        with cf.ThreadPoolExecutor(a.jobs) as ex:
            list(ex.map(run_group, groups.values()))
        # a failure that BASE shows too is not this change's: rerun failures at BASE when every
        # path the command names at HEAD also exists at BASE (else the failing code is new)
        failed = [i for i in todo if i.get("status") in ("fail", "timeout")]
        if failed and not a.no_base_check:
            try:
                bwt = tempfile.mkdtemp(prefix="run-changed-base-", dir=a.workdir)
                git(repo, "worktree", "add", "--detach", "--force", bwt, base)
                def at_base(i):
                    paths = [t for t in re.findall(r"[\w./\-]+", i["cmd"]) if "/" in t and
                             os.path.exists(os.path.join(wt, t))]
                    if any(not os.path.exists(os.path.join(bwt, t)) for t in paths):
                        i["base"] = "absent"
                        return
                    r = run_cmd(i["cmd"], bwt, i.get("env"), a.timeout, i.get("wd"), shims)
                    i["base"] = r["status"]
                    if r["status"] != "pass":
                        i["status"] = "pre-existing"
                with cf.ThreadPoolExecutor(a.jobs) as ex:
                    list(ex.map(at_base, failed))
            finally:
                cleanup(repo, bwt)
    total = round(time.time() - t0, 1)
    if not a.keep:
        cleanup(repo, wt)
        shutil.rmtree(os.path.dirname(shims[0]), ignore_errors=True)
    blocking = {k.strip() for k in a.block.split(",") if k.strip()}
    for i in todo:
        if i.get("status") == "fail" and i["kind"] not in blocking:
            i["status"] = "advisory"
    fails = [i for i in todo if i.get("status") == "fail"]
    touts = [i for i in todo if i.get("status") == "timeout"]
    leans = [i for i in todo if i.get("status") == "needs-lean"]
    if a.json:
        print(json.dumps(dict(base=base, head=head, changed=len(ch), secs=total, items=[
            {k: v for k, v in i.items() if k not in ("env",)} for i in items]), indent=1))
    else:
        for i in items:
            label = i["kind"] + (":" + i["wf"] + "/" + i["job"] if i["kind"] == "workflow" else "")
            st = i.get("status") or ("SKIP " + i["skip"] if i["skip"] else "would run")
            print("%-9s %s %s%s" % (st.upper() if not i["skip"] else st, label, i["name"],
                                    " (%ss)" % i["secs"] if "secs" in i else ""))
            if i.get("status") in ("fail", "advisory", "timeout", "needs-lean", "needs-args", "pre-existing"):
                print("    " + i["tail"].replace("\n", "\n    "))
        print("run_changed: %d run, %d failed, %d timed out, %d stopped at Lean, %d skipped, %.1fs" % (
            len(todo) if not a.list else 0, len(fails), len(touts), len(leans), len(items) - len(todo), total))
    return 1 if fails else 0


def cleanup(repo, wt):
    subprocess.run(["git", "-C", repo, "worktree", "remove", "--force", wt], capture_output=True)
    shutil.rmtree(wt, ignore_errors=True)
    subprocess.run(["git", "-C", repo, "worktree", "prune"], capture_output=True)


if __name__ == "__main__":
    sys.exit(main())
