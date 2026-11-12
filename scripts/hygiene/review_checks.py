#!/usr/bin/env python3
"""Review checks: findings the landing review kept making, found without a model.

Rules (tracked Git content of base and head; the working tree is not read):
  coverage  the Solidity.* modules CI builds and the modules the axiom audit sees may not shrink.
            Built: the import closure of every library a workflow names in `lake build A B …`
            (capitalized words: library roots A.lean), YAML comments ignored. Audited: the import closure of
            scripts/AxiomAudit.lean. A Solidity.* module covered at base that still exists at head
            must be covered at head; deleting a module is not a loss.
  tests     a test file that exists at base (renames followed) may not gain todo/skip/xfail markers
            (counted per marker, net, per file):
            `test.todo`, `it.skip`, `{todo: …}`, `skip: true`, `pytest.mark.skip`, `unittest.skip`,
            `skipTest(` (not behind an `if` on the same line: a platform guard), `expectedFailure`…
            Test files: *.test.{js,mjs,cjs,ts}, test_*.py, *_test.py. New files are not checked:
            a new test weakens no existing one.

A deliberate change passes when a commit of base..head carries the trailer
`Review-Check: <rule> <reason>` naming the rule (coverage or tests).

Base: as scripts/hygiene/check.py (--base REV, else $HYGIENE_BASE, else merge-base(head,
origin/master); on master, head's first parent).

Usage: review_checks.py [--base REV] [--head REV]   exit 0 pass, 1 policy failure, 2 setup error
"""
import argparse, os, re, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check import SetupError, default_base, git, rev  # noqa: E402

AUDIT = "scripts/AxiomAudit.lean"
IMPORT = re.compile(r"^(?:(?:public|meta|private)\s+)*import\s+(?:all\s+)?(.*)$")
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")
BUILD = re.compile(r"lake build ([^\n|&;>]*)")
TEST_FILE = re.compile(r"(^|/)(test_[^/]*\.py|[^/]*_test\.py|[^/]*\.test\.(js|mjs|cjs|ts))$")
SOFT = re.compile(r"\b(?:test|it|describe)\.(?:todo|skip)\b|[{,]\s*todo\s*:|\bskip\s*:\s*true\b"
                  r"|pytest\.mark\.(?:skip|xfail)|unittest\.skip|\bskipTest\(|expectedFailure")


def blobs(r, paths):
    """{path: text or None} of `paths` at revision r, read in one cat-file call."""
    paths = list(paths)
    if not paths: return {}
    data = git("cat-file", "--batch", inp="".join(f"{r}:{p}\n" for p in paths).encode())
    out, i = {}, 0
    for p in paths:
        nl = data.index(b"\n", i); hdr = data[i:nl].split()
        if hdr[-1] == b"missing": out[p] = None; i = nl + 1; continue
        n = int(hdr[2]); out[p] = data[nl + 1:nl + 1 + n].decode("utf-8", "replace"); i = nl + 2 + n
    return out


def imports(text):
    """Module names of the import header: `import A B`, modifiers, indented continuation lines.
    It ends at the first other non-blank, non-comment line."""
    out, block, inside = [], False, False
    for line in text.split("\n"):
        s = re.sub(r"--.*", "", line).strip()
        if block:
            block = "-/" not in s; continue
        if not s: continue
        if s.startswith("/-"):
            block = "-/" not in s[2:]; continue
        m = IMPORT.match(s)
        if m: rest = m.group(1); inside = True
        elif inside and line[:1].isspace() and NAME.fullmatch(s.split()[0]): rest = s
        else: break
        names = rest.split()
        if not all(NAME.fullmatch(n) for n in names): break
        out += names
    return out


def closure(roots, src):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        p = m.replace(".", "/") + ".lean"
        if m in seen or src.get(p) is None: continue
        seen.add(m); todo += imports(src[p])
    return seen


def coverage(r):
    """(modules CI builds, modules the axiom audit imports, Solidity.* modules present) at r."""
    files = [f for f in git("ls-tree", "-r", "--name-only", r).decode().split("\n") if f]
    lean = [f for f in files if f.endswith(".lean") and ("/" not in f or f.startswith("Solidity/"))]
    wf = [f for f in files if f.startswith(".github/workflows/") and f.endswith((".yml", ".yaml"))]
    src = blobs(r, lean + wf + ([AUDIT] if AUDIT in files else []))
    yaml = {f: re.sub(r"(^|\s)#.*", "", src[f] or "", flags=re.M) for f in wf}
    built = {w for f in wf for args in BUILD.findall(yaml[f]) for w in args.split()
             if re.fullmatch(r"[A-Z][A-Za-z0-9_]*", w)}
    present = {f[:-5].replace("/", ".") for f in lean if f.startswith("Solidity/")}
    return closure(built, src), closure(imports(src.get(AUDIT) or ""), src), present


def check_coverage(base, head):
    (b_built, b_audit, _), (h_built, h_audit, present) = coverage(base), coverage(head)
    bad = []
    for what, b, h in (("the CI build", b_built, h_built), ("the axiom audit", b_audit, h_audit)):
        lost = sorted((b & present) - h)
        if lost:
            bad.append(f"coverage: {len(lost)} Solidity module(s) no longer reached by {what}, e.g. "
                       + ", ".join(lost[:3]))
    return bad


def markers(text):
    """Number of todo/skip/xfail markers in `text` (a `skipTest(` on a line starting with `if` is a guard)."""
    n = 0
    for line in (text or "").split("\n"):
        guard = re.match(r"\s*if\b", line)
        n += sum(1 for m in SOFT.finditer(line) if not (guard and m.group().startswith("skipTest")))
    return n


def check_tests(base, head):
    pairs = []
    for line in git("diff", "--name-status", "--diff-filter=MR", "-M", base, head).decode().split("\n"):
        if not line: continue
        st, *paths = line.split("\t")
        if TEST_FILE.search(paths[-1]): pairs.append((paths[0], paths[-1]))
    old = blobs(base, [o for o, _ in pairs]); new = blobs(head, [n for _, n in pairs])
    bad = []
    for o, n in sorted(pairs, key=lambda x: x[1]):
        d = markers(new[n]) - markers(old[o])
        if d > 0: bad.append(f"tests: {n} gains {d} todo/skip/xfail marker(s)")
    return bad


def waived(base, head):
    msgs = git("log", "--format=%B%x00", f"{base}..{head}").decode("utf-8", "replace")
    return {m.group(1) for m in re.finditer(r"^Review-Check:[ \t]*(coverage|tests)[ \t]+\S", msgs, re.M)}


def run(base, head):
    """(ok, report lines)."""
    w = waived(base, head)
    rep, bad = [], []
    for rule, fn in (("coverage", check_coverage), ("tests", check_tests)):
        found = fn(base, head)
        if found and rule in w: rep.append(f"waived {rule} (Review-Check trailer): " + "; ".join(found))
        else: bad += found
        if not found: rep.append(f"ok {rule}")
    if bad:
        bad.append("A deliberate change needs a commit trailer `Review-Check: <coverage|tests> <reason>`.")
    return not bad, bad + rep


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base"); ap.add_argument("--head", default="HEAD")
    a = ap.parse_args(argv)
    for f in (sys.stdout, sys.stderr): f.reconfigure(errors="backslashreplace")
    try:
        head = rev(a.head)
        base = rev(a.base) if a.base else default_base(head)
        ok, rep = run(base, head)
    except SetupError as e:
        print(f"review-checks: setup error: {e}", file=sys.stderr); return 2
    print(f"review-checks {base[:12]}..{head[:12]}: {'PASS' if ok else 'FAIL'}")
    for line in rep: print("  " + line)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
