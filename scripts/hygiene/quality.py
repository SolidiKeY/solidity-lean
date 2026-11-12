#!/usr/bin/env python3
"""Quality ratchets (plan step q2-quality-ratchets): counts that may only go down.

Every count is measured on the tracked content of a commit (Git objects, never the working
tree) and compared with scripts/hygiene/baseline.json. The count definitions:

  lean_long_files           tracked .lean files over 1500 lines. Excluded by path only (file text
                            never excludes a file, so no comment or string can opt out): vendored
                            paths (a `vendor` segment), the generated library roots, Corpus files
                            and AxiomPins files (reach.py's path rules for generated files).
  long_proofs               theorem, lemma and example spans over 150 lines in the same files.
                            A span runs from the declaration keyword (attributes included) to the
                            next declaration or command (reach.py's DECL and COMMAND) or column-0
                            directive (an indented `open … in` inside a proof does not end it),
                            less its trailing blank lines (blanked comments and docstrings included).
  duplicate_windows         repeated normalized 30-line windows over the code files (.lean .py
                            .mjs .js .cjs .ts .sh) under Solidity/ and scripts/, with the path
                            exclusions above. Lines are normalized to their tokens (Lean comments
                            and string contents blanked with reach.py's `clean`; other files drop
                            comment-only lines; identifiers are kept, so this finds copies, not
                            renamed clones); blank lines are skipped. The count is the number of
                            windows minus the number of distinct windows (overlapping windows, so
                            one extra copy of an N-line block adds N-29), and deleting a copy
                            lowers it.
  unreachable_declarations  reach.py's census, run on the commit: declarations with no candidate
                            path from a goal, test, CI build target (CLIs included) or their
                            implicit dispatch (docs/audits/direction-tools/reachability/reach.py,
                            the sum of `decls` of its unreachable rows). reach.py is imported, not
                            copied; its character-level `clean` is swapped for an identical
                            regex version (test_quality.py checks they agree) so it runs in about
                            a minute instead of four. k1's certificate classifier
                            (scripts/lean-inventory) has no classifier on master yet: it needs an
                            elaborated extraction, so it cannot run in a fast check.
  python_dead_code          ruff's F401 (unused import), F811 (redefinition of an unused name) and
                            F841 (unused local) findings over tracked .py files outside vendor
                            paths, counted with the ruff pinned in ruff-requirements.txt (vulture
                            is not used). PATH's ruff is used when it is that version; otherwise
                            the pinned wheel is installed with pip --require-hashes under Git's
                            directory (once; about 2 s), so CI needs no setup step. The count is
                            enforced: a run that cannot get the pinned ruff FAILS, since rule
                            details change between versions.
  lean_warnings             distinct `warning: FILE:LINE:COL: …` lines of a Lake build log given
                            with --lean-log (opt-in; off by default). Lake's artifact cache keeps
                            no logs, so only a build that compiled every module sees every
                            warning. While the baseline value is null it is reported, not enforced.

A count the baseline sets (a number) is always enforced: a run that cannot measure it (tool or
--lean-log missing, other ruff version) fails. So set a count only when every gate can measure it.

Ratchet (base: --base REV, else $HYGIENE_BASE, else the merge base with origin/master, as
check.py): a count passes when its head value is at most the baseline value. When the inputs a
count reads are byte-identical at base and head, it passes without measuring. When head is over
the baseline, base is measured too: if base is already over the baseline (master grew before the
baseline was refreshed) head passes when it is at most base, so the merged head of a lane that
grew nothing passes; otherwise the count fails. baseline.json may only go down: against base's
copy no value may rise, no enforced value may become null and the ruff version may not change
while its count is set. `seed` writes a full baseline measured on a commit (the merge base);
`update` lowers the committed values to the head's measurements.

Usage: quality.py [check] [--base REV] [--head REV] [--only NAME,...] [--lean-log FILE] [--no-cache]
       quality.py measure [--rev REV] [--only NAME,...] [--lean-log FILE]   counts as JSON
       quality.py seed [--rev REV]      print a baseline.json measured on REV (default: the merge base)
       quality.py update                lower baseline.json (working tree) to the head's counts
Exit 0 pass, 1 policy failure, 2 setup error. Each count prints its time.
"""
import argparse, functools, hashlib, importlib.util, json, os, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import check as hygiene  # noqa: E402  (git helpers and the base rule shared with check.py)

BASELINE = "scripts/hygiene/baseline.json"
REACH = "docs/audits/direction-tools/reachability/reach.py"
METRICS = ("lean_long_files", "long_proofs", "duplicate_windows", "unreachable_declarations",
           "python_dead_code", "lean_warnings")
FILE_LINES, PROOF_LINES, WINDOW = 1500, 150, 30
CODE_EXT = (".lean", ".py", ".mjs", ".js", ".cjs", ".ts", ".sh")
RUFF_RULES = "F401,F811,F841"
PROOF_KINDS = ("theorem", "lemma")
DIRECTIVE = re.compile(r'^(?:namespace|section|end|open|variable|attribute|set_option|import)\b', re.M)
ROOTS = ("Solidity.lean", "SolidityExamples.lean", "Bridge/SolidityBridge.lean", "SolidityCorpus.lean")
PUNCT = re.compile(r"[^\w\s]")
WARNING = re.compile(r"^warning: (\S+?):(\d+):(\d+): (.*)$", re.M)


class SetupError(Exception):
    pass


def git(*args, inp=None):
    try:
        return hygiene.git(*args, inp=inp)
    except hygiene.SetupError as e:
        raise SetupError(str(e))


# ---- reach.py, imported (never copied) -------------------------------------------------

_NORMAL, _COMMENT, _STRING = re.compile(r'/-|--|"'), re.compile(r'/-|-/'), re.compile(r'\\[\s\S]|"')
_NONNL = re.compile(r'[^\n]')


def _blank(s): return _NONNL.sub(' ', s)


def fast_clean(text):
    """reach.clean, character for character (nested comments, strings with escapes, line
    comments blanked; offsets and newlines kept), jumping between special tokens."""
    out, i, n = [], 0, len(text)
    while i < n:
        m = _NORMAL.search(text, i)
        if not m:
            out.append(text[i:]); break
        out.append(text[i:m.start()]); tok = m.group(); i = m.end()
        if tok == '--':
            e = text.find('\n', m.start()); e = n if e < 0 else e
            out.append(' ' * (e - m.start())); i = e
        elif tok == '/-':
            out.append('  '); depth = 1
            while depth and i < n:
                c = _COMMENT.search(text, i)
                if not c:
                    out.append(_blank(text[i:])); i = n; break
                out.append(_blank(text[i:c.start()])); out.append('  ')
                depth += 1 if c.group() == '/-' else -1; i = c.end()
        else:
            out.append(' ')
            while i < n:
                c = _STRING.search(text, i)
                if not c:
                    out.append(_blank(text[i:])); i = n; break
                out.append(_blank(text[i:c.start()])); i = c.end()
                if c.group() == '"':
                    out.append(' '); break
                out.append('  ')
    return ''.join(out)


@functools.lru_cache(maxsize=None)
def reach_module():
    path = os.path.join(os.path.dirname(os.path.dirname(HERE)), REACH)  # this checkout's copy
    if not os.path.exists(path):
        raise SetupError(f"{REACH} is missing; the unreachable_declarations count reuses it")
    spec = importlib.util.spec_from_file_location("reach_census", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.clean = functools.lru_cache(maxsize=None)(fast_clean)
    return mod


# ---- Git content --------------------------------------------------------------------------

def tree(commit):
    """{path: blob sha} of the blobs of `commit`."""
    return {p: sha for p, (sha, _) in hygiene.tree(commit).items()}


def blobs(t, paths):
    """{path: text} for `paths` of tree `t`, read in one cat-file batch."""
    paths = [p for p in paths if p in t]
    if not paths: return {}
    data = git("cat-file", "--batch", inp="".join(t[p] + "\n" for p in paths).encode())
    out, pos = {}, 0
    for p in paths:
        nl = data.index(b"\n", pos); size = int(data[pos:nl].split()[2])
        out[p] = data[nl + 1: nl + 1 + size].decode("utf-8", "replace"); pos = nl + 2 + size
    return out


def vendored(p): return "vendor" in p.split("/")[:-1]


def excluded(p):
    """Vendored or generated by path: the rules of reach.py's `generated` that read only the path."""
    return vendored(p) or p in ROOTS or "/Corpus/" in p or "AxiomPins" in p


# ---- Counts -------------------------------------------------------------------------------

def lean_sources(t):
    """{path: text} of the counted Lean files (see `excluded`)."""
    return blobs(t, sorted(p for p in t if p.endswith(".lean") and not excluded(p)))


def nlines(text, a=0, b=None):
    """Lines of text[a:b]: its newlines, plus one for an unterminated last line."""
    b = len(text) if b is None else b
    return text.count("\n", a, b) + (1 if b > a and text[b - 1] != "\n" else 0)


def long_files(texts):
    return sorted((p, nlines(s)) for p, s in texts.items() if nlines(s) > FILE_LINES)


def proof_spans(text):
    """[(kind, name, first line, lines)] of the theorem, lemma and example spans of `text`."""
    import bisect
    r = reach_module(); ct = r.clean(text)
    starts = list(r.DECL.finditer(ct)); commands = list(r.COMMAND.finditer(ct))
    bounds = sorted(set([len(ct)] + [m.start() for m in starts] + [m.start() for m in commands]
                        + [m.start() for m in DIRECTIVE.finditer(ct)]))
    spans = [(m.group(1), m.group(2) or "", m) for m in starts if m.group(1) in PROOF_KINDS]
    spans += [("example", "", m) for m in commands if m.group().lstrip().startswith("example")]
    out = []
    for kind, name, m in spans:
        end = bounds[bisect.bisect_right(bounds, m.start())]
        end = len(ct[m.start():end].rstrip()) + m.start()  # trailing blanks and blanked docs
        n = nlines(ct, m.start(), end)
        out.append((kind, name, ct.count("\n", 0, m.start()) + 1 if n > PROOF_LINES else 0, n))
    return sorted(out, key=lambda x: x[2])


def long_proofs(texts):
    return [(p, kind, name, line, n) for p in sorted(texts)
            for kind, name, line, n in proof_spans(texts[p]) if n > PROOF_LINES]


def code_paths(t):
    return sorted(p for p in t if p.startswith(("Solidity/", "scripts/")) and p.endswith(CODE_EXT)
                  and not excluded(p) and "/node_modules/" not in p)


def normalized_lines(path, text):
    """The non-blank lines of `text` as space-separated tokens (words and single symbols)."""
    if path.endswith(".lean"):
        text = reach_module().clean(text)
    else:
        text = "\n".join(l for l in text.split("\n") if not l.lstrip().startswith(("#", "//")))
    return [x for x in (" ".join(l.split()) for l in PUNCT.sub(r" \g<0> ", text).split("\n")) if x]


def window_hashes(path, text):
    rows = normalized_lines(path, text)
    return [hashlib.blake2b("\n".join(rows[i:i + WINDOW]).encode(), digest_size=8).digest()
            for i in range(len(rows) - WINDOW + 1)]


def duplicate_windows(texts):
    """(count, {path: repeated windows}) over `texts`."""
    seen, per, total = {}, {}, 0
    for p in sorted(texts):
        for h in window_hashes(p, texts[p]):
            total += 1
            first = seen.setdefault(h, p)
            if first is not p:
                per[p] = per.get(p, 0) + 1
    return total - len(seen), per


RUFF_REQUIREMENTS = os.path.join(HERE, "ruff-requirements.txt")
RUFF_PROBLEM = []  # why the pinned ruff is unavailable, for the report


def ruff_pin():
    with open(RUFF_REQUIREMENTS) as f:
        m = re.search(r"^ruff==([0-9][0-9A-Za-z.]*)", f.read(), re.M)
    if not m: raise SetupError(f"{RUFF_REQUIREMENTS}: no ruff==VERSION line")
    return m.group(1)


def _version_of(exe):
    try:
        r = subprocess.run([exe, "--version"], capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    return r.stdout.strip() if r.returncode == 0 else None


@functools.lru_cache(maxsize=None)
def ruff_exe():
    """A ruff of the pinned version: PATH's when it matches, else one installed from the hashed
    wheels of ruff-requirements.txt under Git's directory (kept for later runs). None, with the
    reason in RUFF_PROBLEM, when neither works; an enforced count then fails."""
    want = "ruff " + ruff_pin()
    exe = shutil.which("ruff")
    if exe and _version_of(exe) == want: return exe
    d = cache_dir()
    if d is None:
        RUFF_PROBLEM.append("no Git directory to install it in"); return None
    target = os.path.join(os.path.dirname(d), "hygiene-tools", want.replace(" ", "-"))
    local = os.path.join(target, "bin", "ruff.exe" if os.name == "nt" else "ruff")
    if os.path.exists(local) and _version_of(local) == want: return local
    # Install beside the target and rename it into place, so a concurrent or interrupted run
    # never sees (or deletes) a half-installed copy.
    os.makedirs(os.path.dirname(target), exist_ok=True)
    stage = tempfile.mkdtemp(prefix=os.path.basename(target) + ".", dir=os.path.dirname(target))
    try:
        r = subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", "--disable-pip-version-check",
                            "--no-deps", "--only-binary", ":all:", "--require-hashes", "--target", stage,
                            "-r", RUFF_REQUIREMENTS], capture_output=True, text=True, timeout=300,
                           env={**os.environ, "PIP_ROOT_USER_ACTION": "ignore"})
        staged = os.path.join(stage, "bin", os.path.basename(local))
        if r.returncode == 0 and os.path.exists(staged) and _version_of(staged) == want:
            shutil.rmtree(target, ignore_errors=True)
            try:
                os.rename(stage, target)
            except OSError:
                pass  # a concurrent run placed its copy first
            if os.path.exists(local) and _version_of(local) == want: return local
        problem = r.stderr.strip()[-300:] or "no ruff binary"
    except (OSError, subprocess.SubprocessError) as e:
        problem = str(e)
    finally:
        shutil.rmtree(stage, ignore_errors=True)
    RUFF_PROBLEM.append(f"installing {want} with pip failed: {problem}")
    return None


def ruff_version():
    """'ruff X' of the pinned ruff this run can use, else None."""
    exe = ruff_exe()
    return _version_of(exe) if exe else None


def python_dead_code(commit, t):
    """(count, findings) of ruff's RUFF_RULES over the tracked .py files of `commit`."""
    paths = sorted(p for p in t if p.endswith(".py") and not vendored(p))
    with tempfile.TemporaryDirectory(prefix="hygiene-ruff.") as d:
        for i in range(0, len(paths), 500):
            arch = git("archive", "--format=tar", commit, "--", *paths[i:i + 500])
            r = subprocess.run(["tar", "-x", "-C", d], input=arch, capture_output=True)
            if r.returncode: raise SetupError("cannot unpack Python sources: " + r.stderr.decode(errors="replace"))
        r = subprocess.run([ruff_exe(), "check", "--isolated", "--no-cache", "--select", RUFF_RULES,
                            "--output-format", "json", "--exit-zero", "."], cwd=d, capture_output=True, text=True)
        if r.returncode: raise SetupError("ruff failed: " + r.stderr.strip()[-500:])
        rows = [x for x in json.loads(r.stdout or "[]") if x.get("code") in RUFF_RULES.split(",")]
        found = sorted((os.path.relpath(x["filename"], d), x["location"]["row"], x["code"]) for x in rows)
    return len(found), found


def lean_warnings(log_path):
    with open(log_path, encoding="utf-8", errors="replace") as f:
        found = sorted(set(WARNING.findall(f.read())))
    return len(found), found


def unreachable_declarations(commit):
    r = reach_module()
    r.BASE = commit
    _, unreachable, *_ = r.build()
    return sum(row["decls"] for row in unreachable)


# ---- Inputs, cache and measurement ---------------------------------------------------------

def inputs_key(metric, commit, t):
    """A digest of what `metric` reads at `commit` (None: not keyed)."""
    if metric in ("lean_long_files", "long_proofs"):
        sel = [p for p in t if p.endswith(".lean")]
    elif metric == "duplicate_windows":
        sel = [p for p in t if p.startswith(("Solidity/", "scripts/")) and p.endswith(CODE_EXT)]
    elif metric == "unreachable_declarations":
        sel = [p for p in t if p.endswith(".lean") or p.startswith(".github/workflows/")
               or p in ("lakefile.toml", "docs/audits/architecture-tools/timing-sample.tsv")]
    elif metric == "python_dead_code":
        sel = [p for p in t if p.endswith(".py")]
    else:
        return None
    h = hashlib.sha256(metric.encode())
    for p in sorted(sel): h.update(f"{p}\0{t[p]}\n".encode())
    h.update(tool_digest().encode())
    return h.hexdigest()


@functools.lru_cache(maxsize=None)
def tool_digest():
    """The code that defines the counts as it runs here (this checkout's files, committed or
    not), so a cached or shortcut result never outlives a change of definition."""
    root, h = os.path.dirname(os.path.dirname(HERE)), hashlib.sha256()
    for rel in (REACH, "scripts/hygiene/quality.py", "scripts/hygiene/check.py"):
        try:
            with open(os.path.join(root, rel), "rb") as f: h.update(rel.encode() + b"\0" + f.read())
        except OSError:
            h.update(rel.encode() + b"\0missing")
    return h.hexdigest()


def cache_dir():
    try:
        d = git("rev-parse", "--path-format=absolute", "--git-common-dir").decode().strip()
    except SetupError:
        return None
    return os.path.join(d, "hygiene-quality-cache")


def cached(key, compute, use_cache):
    """compute() memoized on disk under Git's directory by `key` (best effort)."""
    d = cache_dir() if use_cache else None
    f = os.path.join(d, key + ".json") if d else None
    if f and os.path.exists(f):
        try:
            with open(f) as h: v = json.load(h)["value"]
            if isinstance(v, int) and not isinstance(v, bool) and v >= 0: return v
        except (OSError, ValueError, KeyError, TypeError):
            pass
    value = compute()
    if f:
        try:
            os.makedirs(d, exist_ok=True)
            with open(f + ".tmp", "w") as h: json.dump({"value": value}, h)
            os.replace(f + ".tmp", f)
        except OSError:
            pass
    return value


class Measure:
    """Counts of one commit, computed on demand: m.get(metric) -> (value or None, note, details)."""

    def __init__(self, commit, lean_log=None, use_cache=True):
        self.commit, self.lean_log, self.use_cache = commit, lean_log, use_cache
        self.t = tree(commit); self._texts = None; self.done = {}; self.seconds = {}

    def lean_texts(self):
        if self._texts is None: self._texts = lean_sources(self.t)
        return self._texts

    def key(self, metric): return inputs_key(metric, self.commit, self.t)

    def get(self, metric):
        if metric not in self.done:
            start = time.monotonic()
            self.done[metric] = self._compute(metric)
            self.seconds[metric] = time.monotonic() - start
        return self.done[metric]

    def _compute(self, metric):
        if metric == "lean_long_files":
            rows = long_files(self.lean_texts())
            return len(rows), "", [f"{p} ({n} lines)" for p, n in rows]
        if metric == "long_proofs":
            rows = long_proofs(self.lean_texts())
            return len(rows), "", [f"{p}:{l} {k} {nm} ({n} lines)" for p, k, nm, l, n in rows]
        if metric == "duplicate_windows":
            texts = blobs(self.t, code_paths(self.t))
            n, per = duplicate_windows(texts)
            top = sorted(per.items(), key=lambda x: (-x[1], x[0]))[:15]
            return n, "", [f"{p}: {k} repeated window(s)" for p, k in top]
        if metric == "unreachable_declarations":
            n = cached(self.key(metric), lambda: unreachable_declarations(self.commit), self.use_cache)
            return n, "", []
        if metric == "python_dead_code":
            v = ruff_version()
            if v is None:
                return None, (f"ruff {ruff_pin()} is not on PATH and could not be installed: "
                              f"{'; '.join(RUFF_PROBLEM) or 'unknown reason'}"), []
            n, rows = python_dead_code(self.commit, self.t)
            return n, v, [f"{p}:{l} {c}" for p, l, c in rows]
        if metric == "lean_warnings":
            if not self.lean_log: return None, "skipped: no --lean-log (opt-in: a full Lake build log)", []
            n, rows = lean_warnings(self.lean_log)
            return n, "", [f"{p}:{l}:{c} {msg[:100]}" for p, l, c, msg in rows]
        raise ValueError(metric)


# ---- Baseline and ratchet ------------------------------------------------------------------

def read_baseline(commit):
    r = subprocess.run(["git", "show", f"{commit}:{BASELINE}"], capture_output=True)
    if r.returncode: return None
    return parse_baseline(r.stdout, commit[:12])


def parse_baseline(data, where):
    try:
        b = json.loads(data)
    except ValueError as e:
        raise SetupError(f"{BASELINE} at {where} is not JSON: {e}")
    ok = (isinstance(b, dict) and set(b) - {"comment"} == {"seed", "python_dead_code_tool", "metrics"}
          and isinstance(b["seed"], str) and re.fullmatch(r"[0-9a-f]{40}", b["seed"])
          and (b["python_dead_code_tool"] is None or isinstance(b["python_dead_code_tool"], str))
          and isinstance(b["metrics"], dict) and set(b["metrics"]) == set(METRICS)
          and all(v is None or (isinstance(v, int) and not isinstance(v, bool) and v >= 0)
                  for v in b["metrics"].values()))
    if not ok:
        raise SetupError(f"{BASELINE} at {where} is malformed: need seed (40-hex commit), "
                         f"python_dead_code_tool (string or null) and metrics with exactly the keys "
                         f"{', '.join(METRICS)} (non-negative int or null), and an optional comment")
    return b


def baseline_history(base_b, head_b, where):
    """Failure lines when the head baseline is not a lowering of base's."""
    if head_b is None:
        return [f"FAIL {where}: {BASELINE} is missing" + (" (base has one; lower its values instead)" if base_b else "")]
    if base_b is None: return []
    bad = []
    for m in METRICS:
        old, new = base_b["metrics"][m], head_b["metrics"][m]
        if old is None: continue
        if new is None: bad.append(f"FAIL {where}: {m} goes from {old} to null; a set count stays set")
        elif new > old: bad.append(f"FAIL {where}: {m} rises from {old} to {new}; counts may only go down")
    if (base_b["metrics"]["python_dead_code"] is not None
            and head_b["python_dead_code_tool"] != base_b["python_dead_code_tool"]):
        bad.append(f"FAIL {where}: python_dead_code_tool changes from {base_b['python_dead_code_tool']!r} to "
                   f"{head_b['python_dead_code_tool']!r} while its count is set")
    return bad


def enforced(b, metric, head_value, note):
    """("enforce" | "report" | "unmeasurable", reason) for `metric` under baseline `b` and the
    head's measurement. A count the baseline sets must be measured: it never passes unmeasured."""
    if b["metrics"][metric] is None:
        return "report", (note if head_value is None else "baseline is null: reported, not enforced")
    if head_value is None: return "unmeasurable", note
    if metric == "python_dead_code" and note != b["python_dead_code_tool"]:
        return "unmeasurable", f"baseline counted with {b['python_dead_code_tool']}, this host has {note}"
    return "enforce", ""


def judge(metric, limit, head_m, base_m):
    """(ok, line, details) for an enforced metric with baseline `limit`."""
    if base_m is not None and head_m.key(metric) is not None and head_m.key(metric) == base_m.key(metric):
        return True, f"ok {metric}: inputs unchanged from base (baseline {limit})", []
    value, _, details = head_m.get(metric)
    if value <= limit:
        return True, f"ok {metric}: {value} (baseline {limit})", []
    if base_m is not None:
        base_value = base_m.get(metric)[0]
        if base_value is not None and base_value > limit:
            if value <= base_value:
                return True, (f"ok {metric}: {value}, within base's {base_value}; the baseline ({limit}) is stale: "
                              f"lower it with `quality.py update` once the count is back to {limit}"), []
            return False, f"FAIL {metric}: {value}, over base's {base_value} (baseline {limit}, stale)", details
        return False, f"FAIL {metric}: {value}, over the baseline {limit} (base {base_value})", details
    return False, f"FAIL {metric}: {value}, over the baseline {limit}", details


def evaluate(base, head, only, lean_log, use_cache):
    """(ok, report lines)."""
    head_b = read_baseline(head)
    bad = baseline_history(read_baseline(base) if base else None, head_b,
                           f"head {head[:12]}" + (f" (vs base {base[:12]})" if base else ""))
    if head_b is None: return False, bad
    head_m = Measure(head, lean_log, use_cache)
    base_m = Measure(base, None, use_cache) if base else None
    rep = []
    for metric in only:
        start = time.monotonic()
        limit = head_b["metrics"][metric]
        if limit is None or metric in ("python_dead_code", "lean_warnings"):
            value, note, _ = head_m.get(metric)
            state, why = enforced(head_b, metric, value, note)
        else:
            state, why = "enforce", ""
        if state == "enforce":
            ok, line, details = judge(metric, limit, head_m, base_m)
        elif state == "unmeasurable":
            ok, details = False, []
            line = (f"FAIL {metric}: the baseline enforces {limit} but this run cannot measure it ({why}); "
                    f"provide the tool or input, never skip an enforced count")
        else:
            value = head_m.get(metric)[0]
            ok, line, details = True, f"ok {metric}: {'-' if value is None else value} ({why})", []
        line += f" [{time.monotonic() - start:.1f}s]"
        (rep if ok else bad).append(line)
        if not ok: bad.extend("  " + d for d in details[:20])
    stale = [l.split(":")[0][3:] for l in rep if "is stale" in l]
    if stale:
        rep.append(f"quality: WARNING: base is already over the baseline for {', '.join(stale)}; "
                   f"this run allowed base's count. Bring the count back down and run `quality.py update`.")
    return not bad, (bad + rep if bad else rep)


def measure_all(commit, only, lean_log=None, use_cache=True):
    m = Measure(commit, lean_log, use_cache)
    out = {}
    for metric in only:
        value, note, _ = m.get(metric)
        out[metric] = {"value": value, "note": note, "seconds": round(m.seconds[metric], 2)}
    return out


def seed_baseline(commit):
    counts = measure_all(commit, METRICS, None, True)
    # lean_warnings stays null: no gate has a full build log. Every other count is enforced.
    metrics = {k: counts[k]["value"] for k in METRICS}
    if metrics["python_dead_code"] is None:
        raise SetupError("cannot seed python_dead_code: " + counts["python_dead_code"]["note"])
    metrics["lean_warnings"] = None
    return {"comment": "Quality ratchet counts (scripts/hygiene/quality.py); measured on `seed`; values may only go down. "
                       "A set count is always enforced; lean_warnings is null (reported with --lean-log).",
            "seed": commit, "python_dead_code_tool": counts["python_dead_code"]["note"], "metrics": metrics}


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", default="check", choices=["check", "measure", "seed", "update"])
    ap.add_argument("--base"); ap.add_argument("--head", default="HEAD"); ap.add_argument("--rev")
    ap.add_argument("--only", help="comma-separated counts (default: all)")
    ap.add_argument("--lean-log", help="Lake build log for lean_warnings (opt-in)")
    ap.add_argument("--no-cache", action="store_true", help="do not reuse cached census results")
    a = ap.parse_args(argv)
    for f in (sys.stdout, sys.stderr): f.reconfigure(errors="backslashreplace")
    only = METRICS if not a.only else tuple(x.strip() for x in a.only.split(",") if x.strip())
    try:
        if set(only) - set(METRICS): raise SetupError(f"unknown count(s) {sorted(set(only) - set(METRICS))}; choose from {', '.join(METRICS)}")
        if a.lean_log and not os.path.isfile(a.lean_log): raise SetupError(f"--lean-log {a.lean_log}: no such file")
        if git("rev-parse", "--is-shallow-repository").strip() != b"false":
            raise SetupError("shallow clone: the ratchet needs full history (git fetch --unshallow origin)")
        if a.mode == "measure":
            print(json.dumps(measure_all(hygiene.rev(a.rev or "HEAD"), only, a.lean_log, not a.no_cache), indent=1))
            return 0
        if a.mode == "seed":
            r = hygiene.rev(a.rev) if a.rev else hygiene.default_base(hygiene.rev("HEAD"))
            print(json.dumps(seed_baseline(r), indent=1))
            return 0
        if a.mode == "update":
            root = git("rev-parse", "--show-toplevel").decode().strip()
            path = os.path.join(root, BASELINE)
            with open(path, "rb") as f: b = parse_baseline(f.read(), "working tree")
            counts = measure_all(hygiene.rev("HEAD"), only, a.lean_log, not a.no_cache)
            for k, c in counts.items():
                old, new = b["metrics"][k], c["value"]
                if old is not None and new is not None and new < old and (k != "python_dead_code" or c["note"] == b["python_dead_code_tool"]):
                    b["metrics"][k] = new; print(f"lowered {k}: {old} -> {new}")
            with open(path, "w") as f: f.write(json.dumps(b, indent=1) + "\n")
            return 0
        head = hygiene.rev(a.head)
        base = hygiene.rev(a.base) if a.base else hygiene.default_base(head)
        print(f"quality: base {base[:12]} head {head[:12]}")
        start = time.monotonic()
        ok, rep = evaluate(base, head, only, a.lean_log, not a.no_cache)
        print("\n".join(rep))
        print(f"quality: {'PASS' if ok else 'FAIL'} in {time.monotonic() - start:.1f}s")
        return 0 if ok else 1
    except (SetupError, hygiene.SetupError, OSError, ValueError, KeyError, TypeError, ImportError,
            subprocess.CalledProcessError) as e:
        print(f"quality: error: {e!s}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
