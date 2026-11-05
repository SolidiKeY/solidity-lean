#!/usr/bin/env python3
"""Self-contained H28 mutation runner over the repository's Lean MCP bridge.

A check is one scratch Lean file in the ignored `.scratch/` directory of this
lane: the imports, then the target module's text (production or one-change
mutant) inlined in place of its import, then an oracle's text.  Production
files are only read.  The file is elaborated by the language server through
`scripts/coord-tools/lean-mcp` (no direct `lean`/`lake` call), with all
diagnostics (errors, warnings and `#print axioms` output) retained.

Two oracles, never conflated:

* proof oracle: the production `Calculus/Taclet.lean` (`Taclet.toStep`,
  `LeanTaclet.toStep`) after a `Rules.lean` mutant, or `CallbackTaclet.toTaclet`
  in a mutated `CallbackRules.lean`.  A mutant is `detected` only if its
  errors are attributed to the toStep/toTaclet proof of an affected
  constructor (other errors may only be the strict replay's declared
  cascade); `equivalent-certified` if the unchanged proofs still pass (its
  premise is `Stmt.step`'s, hence the original's); `invalid-compilation` if the
  mutated module itself does not elaborate; otherwise `error`.  Detection is
  not a semantic claim: it shows the mutant differs from `Stmt.step`.
* semantic oracle: an owned witness proving `¬ Premise.Sound` at an inhabited
  state, linked to the mutated constructor (`source_link`).  `killed` needs the
  normal baseline to pass, the witness to be rejected on the normal table at
  exactly its source link, and the witness to pass on the mutant with only the
  permitted axioms.  Diagnostics alone never kill.

Every unrun or errored check stays visible and is never scored.
"""
import argparse
import concurrent.futures as cf
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time

LANE = "tests/h28-sol/mutation-testing"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RULES = "Solidity/Calculus/Rules.lean"
CALLBACK = "Solidity/Calculus/CallbackRules.lean"
TACLET = "Solidity/Calculus/Taclet.lean"


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def root():
    return Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())


def imports(text):
    return re.findall(r"^import (\S+)\s*$", text, re.M)


def body(text):
    return re.sub(r"^import \S+\s*\n", "", text, flags=re.M)


def module_of(path):
    return str(Path(path).with_suffix("")).replace("/", ".")


def mutate(text, old, new):
    if not old or old == new or text.count(old) != 1:
        raise ValueError("mutation must replace exactly one unique nonempty span")
    return text.replace(old, new, 1)


def assemble(target_path, target_text, oracle_text):
    """Scratch text and the line regions [start, end] of target and oracle."""
    tmod = module_of(target_path)
    imps = []
    for i in imports(target_text) + imports(oracle_text):
        if i != tmod and i not in imps:
            imps.append(i)
    head = "".join("import " + i + "\n" for i in imps)
    tbody, obody = body(target_text), body(oracle_text)
    t0 = head.count("\n") + 1
    t1 = t0 + tbody.count("\n")
    text = head + tbody + ("" if tbody.endswith("\n") else "\n") + obody
    o0 = (head + tbody + ("" if tbody.endswith("\n") else "\n")).count("\n") + 1
    return text, {"target": [t0, t1], "oracle": [o0, text.count("\n") + 1], "imports": imps}


class Bridge:
    """One lean-mcp daemon with its own socket directory and one open file."""

    def __init__(self, repo, index, scratch):
        self.repo, self.index = repo, index
        self.env = dict(os.environ, LEAN_MCP_SOCKDIR=str(scratch / f"sock{index}"),
                        LEAN_LSP_MAX_OPEN_FILES="1", LEAN_MCP_TIMEOUT="3600")
        self.tool = str(repo / "scripts/coord-tools/lean-mcp")

    def diagnostics(self, path):
        cmd = [self.tool, "call", "lean_diagnostic_messages",
               json.dumps({"file_path": str(path), "interactive": False})]
        start = time.monotonic()
        proc = subprocess.run(cmd, cwd=self.repo, env=self.env, capture_output=True, text=True)
        elapsed = time.monotonic() - start
        record = {"command": ["scripts/coord-tools/lean-mcp"] + cmd[1:3] + [{"file_path": "<scratch>", "interactive": False}],
                  "bridge": self.index, "exit": proc.returncode, "elapsed_s": round(elapsed, 3),
                  "stderr": proc.stderr[-2000:]}
        try:
            data = json.loads(proc.stdout)
        except ValueError:
            record["status"] = "bridge-error"
            record["stdout_tail"] = proc.stdout[-2000:]
            return record, None
        # `success` is false whenever an error is reported; only an incomplete
        # or timed-out response is a bridge failure.
        if proc.returncode != 0 or data.get("partial") or data.get("timed_out") or \
                not isinstance(data.get("items"), list):
            record["status"] = "bridge-error"
            record["response"] = {k: data.get(k) for k in ("success", "partial", "timed_out")}
            return record, None
        record["status"] = "complete"
        return record, data["items"]

    def stop(self):
        subprocess.run([self.tool, "stop"], cwd=self.repo, env=self.env, capture_output=True)


def region(items, regions, name):
    a, b = regions[name]
    return [x for x in items if a <= x["line"] <= b]


# ---------------------------------------------------------------- proof oracle

CASCADE = [r"Unknown constant `Solidity\.(?:Taclet|LeanTaclet)\.\w+\.toStep`",
           r"fail to show termination for\s+Solidity\.(?:Taclet|LeanTaclet)\.toStep\b"]


def hand_spans(oracle_text, regions):
    """Line span -> constructor of each hand-written `X.c.toStep` theorem."""
    spans, lines = [], oracle_text.splitlines()
    starts = [(i, m[1]) for i, l in enumerate(lines)
              if (m := re.match(r"theorem ((?:Taclet|LeanTaclet)\.\w+)\.toStep\b", l))]
    decl = [i for i, l in enumerate(lines) if re.match(r"(?:theorem|def|elab|#replay_toStep|end |section|/-)", l)]
    for i, name in starts:
        stop = next((j for j in decl if j > i), len(lines))
        spans.append((regions["oracle"][0] + i, regions["oracle"][0] + stop - 1, name))
    return spans


def attribute(item, spans):
    msg = item["message"]
    m = re.match(r"(?:no proof that `)?Solidity\.((?:Taclet|LeanTaclet)\.\w+)(?:`|: )", msg)
    if m:
        return m[1]
    for a, b, name in spans:
        if a <= item["line"] <= b:
            return name
    return None


def proof_classify(items, regions, affected, oracle_body, kind):
    errors = [x for x in items if x["severity"] == "error"]
    sorry = any("sorryAx" in x["message"] for x in items if x["severity"] != "error")
    if any(regions["target"][0] <= x["line"] <= regions["target"][1] for x in errors):
        return {"outcome": "invalid-compilation", "errors": len(errors)}
    if not errors:
        if sorry:
            return {"outcome": "error", "reason": "sorryAx in a passing proof-oracle check"}
        return {"outcome": "equivalent-certified", "errors": 0}
    primary, cascade, other = [], [], []
    # The closing theorems (`Taclet.toStep` by cases, `Rule.toStep`, ...) can
    # only fail once a row lemma is missing: a declared cascade, never a kill.
    olines = oracle_body.splitlines()
    tail = next((regions["oracle"][0] + i for i, l in enumerate(olines)
                 if l.startswith("/-! ## The rule `Stmt.step` fires")), None)
    if kind == "callback":
        lines = oracle_body.splitlines()
        for x in errors:
            text = lines[x["line"] - regions["oracle"][0]] if 0 <= x["line"] - regions["oracle"][0] < len(lines) else ""
            m = re.match(r"\s*\| \.(\w+) =>", text)
            if m and "CallbackTaclet." + m[1] in affected:
                primary.append(dict(x, constructor="CallbackTaclet." + m[1]))
            else:
                other.append(x)
    else:
        spans = hand_spans(oracle_body, regions)
        for x in errors:
            name = attribute(x, spans)
            if name and ("*" in affected or name in affected):
                primary.append(dict(x, constructor=name))
            elif any(re.search(p, x["message"]) for p in CASCADE) or (tail is not None and x["line"] >= tail):
                cascade.append(x)
            else:
                other.append(dict(x, constructor=name))
    if primary and not other:
        return {"outcome": "detected", "errors": len(errors),
                "attributed": sorted({x.get("constructor", "") for x in primary}),
                "cascade": len(cascade)}
    return {"outcome": "error", "reason": "unattributed proof-oracle errors", "errors": len(errors),
            "unattributed": [{"line": x["line"], "message": x["message"][:300]} for x in other]}


# ------------------------------------------------------------- semantic oracle

def owned(oracle_text):
    ns = re.findall(r"^namespace (H28\.\w+)\s*$", oracle_text, re.M)
    names = re.findall(r"^theorem (\w+)\b", oracle_text, re.M)
    printed = re.findall(r"^#print axioms (\w+)\s*$", oracle_text, re.M)
    if len(ns) != 1 or not names or sorted(printed) != sorted(names) or len(set(names)) != len(names):
        raise ValueError("owned oracle must have one namespace and one #print axioms per theorem")
    if re.search(r"\b(sorry|admit|axiom|native_decide|maxHeartbeats|unsafe)\b", oracle_text):
        raise ValueError("owned oracle uses a forbidden trust shortcut")
    return ns[0], names


def semantic_success(items, regions, oracle_text, require):
    ns, names = owned(oracle_text)
    bad = [x for x in items if x["severity"] in ("error", "warning")]
    if bad:
        return {"ok": False, "reason": "errors/warnings", "diagnostics": [
            {"line": x["line"], "severity": x["severity"], "message": x["message"][:300]} for x in bad[:8]]}
    if any("sorryAx" in x["message"] for x in items):
        return {"ok": False, "reason": "sorryAx"}
    axioms = {}
    for n in names:
        q = ns + "." + n
        hits = [x["message"] for x in region(items, regions, "oracle") if x["message"].startswith("'" + q + "' ")]
        if len(hits) != 1:
            return {"ok": False, "reason": "missing axiom export " + q}
        m = re.fullmatch(re.escape("'" + q + "' depends on axioms: ") + r"\[(.*)\]", hits[0])
        deps = [] if hits[0] == "'" + q + "' does not depend on any axioms" else (m[1].split(", ") if m else None)
        if deps is None or not set(deps) <= ALLOWED_AXIOMS:
            return {"ok": False, "reason": "unexpected axioms " + q}
        axioms[q] = deps
    missing = [r for r in require if r not in names]
    if missing:
        return {"ok": False, "reason": "missing required theorem(s) " + ", ".join(missing)}
    sigs = {x["message"].split(" :", 1)[0]: x["message"] for x in region(items, regions, "oracle")
            if x["severity"] == "info" and re.match(r"@?" + re.escape(ns) + r"\.\w+ :", x["message"])}
    return {"ok": True, "axioms": axioms, "signatures": sigs}


def source_link_rejection(items, regions, oracle_text):
    lines = body(oracle_text).splitlines()
    idx = [i for i, l in enumerate(lines) if re.match(r"theorem source_link\b", l)]
    if len(idx) != 1:
        return {"ok": False, "reason": "no unique source_link"}
    link = regions["oracle"][0] + idx[0]
    errors = [x for x in items if x["severity"] == "error"]
    first = errors[0] if errors else None
    if not first or first["line"] != link or "Taclet" not in first["message"] or \
            not re.search(r"mismatch", first["message"], re.I):
        return {"ok": False, "reason": "rejection not attributed to source_link",
                "errors": [{"line": x["line"], "message": x["message"][:300]} for x in errors[:5]], "link_line": link}
    if any(regions["target"][0] <= x["line"] <= regions["target"][1] for x in errors):
        return {"ok": False, "reason": "normal target failed"}
    return {"ok": True, "line": link, "first_error": first["message"][:600], "errors": len(errors)}


# ------------------------------------------------------------------- driver

def check(repo, scratch, bridge, name, target, target_text, oracle_text):
    text, regions = assemble(target, target_text, oracle_text)
    path = scratch / ("H28Run_" + re.sub(r"[^A-Za-z0-9]", "_", name) + ".lean")
    path.write_text(text)
    record, items = bridge.diagnostics(path)
    record.update(name=name, scratch_sha256=sha(text), regions=regions)
    path.unlink()
    return record, items


def run(args):
    repo = root()
    manifest_path = (repo / args.manifest).resolve()
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != 3 or manifest.get("state") != "frozen":
        raise SystemExit("frozen schema-3 manifest required")
    rel = manifest_path.relative_to(repo)
    dirty = subprocess.run(["git", "status", "--porcelain", "--", str(rel), LANE + "/oracles",
                            LANE + "/tools"] + list(manifest["production_inputs"]), cwd=repo,
                           capture_output=True, text=True).stdout.strip()
    if dirty and not args.allow_dirty:
        raise SystemExit("manifest, oracles, tools and production inputs must be committed:\n" + dirty)
    for p, h in manifest["production_inputs"].items():
        if sha((repo / p).read_bytes()) != h:
            raise SystemExit("production input changed: " + p)
    texts = {p: (repo / p).read_text() for p in (RULES, CALLBACK, TACLET)}
    if sha(texts[TACLET]) != manifest["oracle_sha256"][TACLET]:
        raise SystemExit("proof oracle changed: " + TACLET)
    out = Path(args.output).resolve()
    (out / "checks").mkdir(parents=True, exist_ok=True)
    scratch = repo / LANE / ".scratch"
    scratch.mkdir(exist_ok=True)

    jobs = []  # (key, target, target_text, oracle_text, finisher)
    taclet_body = texts[TACLET]
    for b in manifest["proof_baselines"]:
        jobs.append(("baseline." + b["id"], b["target"], texts[b["target"]],
                     taclet_body if b["target"] == RULES else "", ("baseline", b)))
    for m in manifest["mutants"]:
        mt = mutate(texts[m["target"]], m["old"], m["new"])
        oracle = taclet_body if m["target"] == RULES else ""
        jobs.append(("proof." + m["id"], m["target"], mt, oracle, ("proof", m)))
    for c in manifest.get("semantic_cases", []):
        mt = mutate(texts[c["target"]], c["old"], c["new"])
        for phase, ttext, ofile in (("normal-oracle", texts[c["target"]], c.get("oracle")),
                                    ("normal-witness", texts[c["target"]], c.get("witness")),
                                    ("mutant-witness", mt, c.get("witness")),
                                    ("mutant-oracle", mt, c.get("oracle"))):
            if ofile:
                otext = (repo / ofile).read_text()
                if sha(otext) != c[("oracle" if phase.endswith("oracle") else "witness") + "_sha256"]:
                    raise SystemExit("oracle hash mismatch: " + ofile)
                jobs.append((f"semantic.{c['id']}.{phase}", c["target"], ttext, otext, (phase, c)))
    if args.only:
        jobs = [j for j in jobs if any(re.fullmatch(p, j[0]) for p in args.only)]
    done = {p.stem for p in (out / "checks").glob("*.json")} if args.resume else set()
    jobs = [j for j in jobs if j[0] not in done]
    print(f"{len(jobs)} checks to run", flush=True)

    bridges = [Bridge(repo, i, scratch) for i in range(args.jobs)]
    free = list(bridges)
    lock = threading.Lock()

    def work(job):
        key, target, ttext, otext, (phase, entry) = job
        with lock:
            bridge = free.pop()
        try:
            record, items = check(repo, scratch, bridge, key, target, ttext, otext)
        finally:
            with lock:
                free.append(bridge)
        record["phase"], record["entry"] = phase, entry["id"]
        if "old" in entry:
            original = texts[target]
            record["diff"] = "".join(difflib.unified_diff(
                original.splitlines(True), mutate(original, entry["old"], entry["new"]).splitlines(True),
                fromfile="a/" + target, tofile="b/" + target, n=1))
            record["mutant_sha256"] = sha(mutate(original, entry["old"], entry["new"]))
        if items is None:
            record["result"] = {"outcome": "error", "reason": "bridge"}
        else:
            record["diagnostics"] = items
            obody = body(otext) if otext else body(ttext)
            regs = record["regions"]
            if target == CALLBACK and phase in ("baseline", "proof"):
                # the oracle (toTaclet) lives in the target module itself
                start = next(i for i, l in enumerate(body(ttext).splitlines())
                             if l.startswith("theorem CallbackTaclet.toTaclet"))
                regs = dict(regs, oracle=[regs["target"][0] + start, regs["target"][1]],
                            target=[regs["target"][0], regs["target"][0] + start - 1])
                obody = "\n".join(body(ttext).splitlines()[start:])
            record["regions_classified"] = regs
            if phase == "baseline":
                errs = [x for x in items if x["severity"] in ("error", "warning")]
                record["result"] = {"outcome": "pass" if not errs else "fail", "problems": len(errs)}
            elif phase == "proof":
                record["result"] = proof_classify(items, regs, entry["affected"], obody,
                                                  "callback" if target == CALLBACK else "rules")
            elif phase in ("normal-oracle", "mutant-witness"):
                record["result"] = semantic_success(items, regs, otext,
                                                    ["checked_kill"] if phase == "mutant-witness" and entry["kind"] not in ("equivalent-control",) else ["source_link"])
            elif phase in ("normal-witness", "mutant-witness") and entry["kind"] == "equivalent-control":
                record["result"] = semantic_success(items, regs, otext, ["source_link_all", "equivalence_all"])
            elif phase == "normal-witness":
                record["result"] = source_link_rejection(items, regs, otext)
            else:  # mutant-oracle: recorded, not decisive
                errs = [x for x in items if x["severity"] == "error"]
                record["result"] = {"outcome": "recorded", "errors": len(errs)}
        (out / "checks" / (key + ".json")).write_text(json.dumps(record, indent=1, ensure_ascii=False) + "\n")
        print(key, json.dumps({k: v for k, v in record["result"].items() if k in ("outcome", "ok", "reason")}),
              record["elapsed_s"], flush=True)

    try:
        with cf.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            list(pool.map(work, jobs))
    finally:
        for b in bridges:
            b.stop()
    summary = summarize(manifest, out)
    summary.update(manifest=str(rel), manifest_sha256=sha(manifest_path.read_bytes()),
                   head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip())
    (out / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k not in ("mutants", "semantic")}, indent=1))


def load(out, key):
    p = out / "checks" / (key + ".json")
    return json.loads(p.read_text()) if p.exists() else None


def summarize(manifest, out):
    out = Path(out)
    baselines = {b["id"]: (load(out, "baseline." + b["id"]) or {}).get("result", {}).get("outcome", "unrun")
                 for b in manifest["proof_baselines"]}
    base_ok = all(v == "pass" for v in baselines.values())
    mutants, counts = {}, {}
    for m in manifest["mutants"]:
        r = load(out, "proof." + m["id"])
        o = r["result"]["outcome"] if r else "unrun"
        if o in ("detected", "equivalent-certified") and not base_ok:
            o = "error"  # an oracle without its passing baseline decides nothing
        mutants[m["id"]] = {"family": m["family"], "outcome": o, "elapsed_s": r and r["elapsed_s"]}
        counts[o] = counts.get(o, 0) + 1
    fam = {}
    for v in mutants.values():
        f = fam.setdefault(v["family"], {})
        f[v["outcome"]] = f.get(v["outcome"], 0) + 1
    semantic, scounts = {}, {}
    for c in manifest.get("semantic_cases", []):
        rs = {p: load(out, f"semantic.{c['id']}.{p}") for p in
              ("normal-oracle", "normal-witness", "mutant-witness", "mutant-oracle")}
        ok = lambda p: rs[p] is not None and rs[p]["result"].get("ok") is True
        if c["kind"] == "equivalent-control":
            o = "equivalent" if ok("normal-oracle") and ok("mutant-witness") else "unrun-or-error"
        elif any(rs[p] is None for p in ("normal-oracle", "normal-witness", "mutant-witness")):
            o = "unrun"
        elif ok("normal-oracle") and ok("normal-witness") and ok("mutant-witness"):
            o = "killed"
        elif ok("normal-oracle") and ok("normal-witness"):
            o = "surviving"
        else:
            o = "error"
        semantic[c["id"]] = {"family": c["family"], "kind": c["kind"], "outcome": o}
        scounts[o] = scounts.get(o, 0) + 1
    scored = [v for v in mutants.values() if v["outcome"] in ("detected", "equivalent-certified")]
    det = sum(v["outcome"] == "detected" for v in scored)
    sem_scored = [v for v in semantic.values() if v["kind"] in ("mutant", "negative-control")
                  and v["outcome"] in ("killed", "surviving")]
    controls = {}
    for m in manifest["mutants"]:
        if m.get("expect") and m["expect"] != "recorded":
            controls[m["id"]] = {"expect": m["expect"], "actual": mutants[m["id"]]["outcome"]}
    for c in manifest.get("semantic_cases", []):
        if c.get("expect"):
            controls[c["id"]] = {"expect": c["expect"], "actual": semantic[c["id"]]["outcome"]}
        elif c["kind"] == "known-kill":
            controls[c["id"]] = {"expect": "killed", "actual": semantic[c["id"]]["outcome"]}
        elif c["kind"] == "equivalent-control":
            controls[c["id"]] = {"expect": "equivalent", "actual": semantic[c["id"]]["outcome"]}
    return {
        "controls": controls,
        "controls_pass": all(v["expect"] == v["actual"] for v in controls.values()),
        "proof_baselines": baselines,
        "proof_oracle": {"counts": counts, "by_family": fam,
                         "score": {"detected": det, "denominator_non_equivalent_run": det,
                                   "equivalent_certified_excluded": len(scored) - det,
                                   "unscored_invalid_error_unrun": len(mutants) - len(scored)}},
        "semantic": semantic,
        "semantic_score": {"killed": sum(v["outcome"] == "killed" for v in sem_scored),
                           "denominator": len(sem_scored), "counts": scounts},
        "runner_cases_complete": all(v["outcome"] != "unrun" for v in mutants.values()) and
                                 all(v["outcome"] != "unrun" for v in semantic.values()),
        "mutants": mutants,
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("manifest")
    r.add_argument("output")
    r.add_argument("--jobs", type=int, default=2)
    r.add_argument("--only", nargs="*")
    r.add_argument("--resume", action="store_true")
    r.add_argument("--allow-dirty", action="store_true", help="development only; never for recorded runs")
    s = sub.add_parser("summarize")
    s.add_argument("manifest")
    s.add_argument("output")
    a = ap.parse_args()
    if a.cmd == "run":
        run(a)
    else:
        print(json.dumps(summarize(json.loads(Path(a.manifest).read_text()), a.output), indent=1))
