#!/usr/bin/env python3
"""Frozen-base Views inventory; lexical counts are not replacement coverage.

Usage: python3 docs/audits/shrink/tv-yul/inventory.py [--check]
Reads Git objects at BASE, so uncommitted work and later master cannot relabel
this denominator. No Lean, external packages, or generated library edits.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

BASE = "381328f608032dd19c405373c2b265e83a969850"
HERE = Path(__file__).resolve().parent


def git(*args):
    return subprocess.check_output(["git", *args], text=True)


def strip_comments(text):
    # Preserve newlines/positions; handle Lean nested block and line comments.
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        ch = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
        elif string:
            if ch == "\\":
                out.extend("  ")
                i += 2
                continue
            if ch == '"':
                string = False
            out.append("\n" if ch == "\n" else " ")
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                out.extend(" " * (len(text)-i))
                break
            out.extend(" " * (end-i))
            i = end
            continue
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
            continue
        elif ch == '"':
            string = True
            out.append(" ")
        else:
            out.append(ch)
        i += 1
    if depth or string:
        raise ValueError("unterminated comment/string")
    return "".join(out)


def measure():
    files = git("ls-tree", "-r", "--name-only", BASE).splitlines()
    lean = {p[:-5].replace("/", "."): p for p in files if p.endswith(".lean")}
    clean, raw = {}, {}

    def source(module):
        if module not in clean:
            raw[module] = git("show", BASE+":"+lean[module])
            clean[module] = strip_comments(raw[module])
        return clean[module]

    views = sorted(m for m in lean if m.startswith("Solidity.Yul.Views."))
    closure, todo = set(), list(views)
    while todo:
        module = todo.pop()
        if module in closure or module not in lean:
            continue
        closure.add(module)
        todo.extend(re.findall(r"^import\s+(\S+)", source(module), re.M))
    rows = []
    for module in views:
        text = source(module)
        headers = re.findall(r"^ *(?:(?:private|protected|noncomputable|unsafe) +)*(def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|axiom)\s+([^\s{(:]+)", text, re.M)
        rows.append({"path": lean[module],
                     "physical_lines": len(raw[module].splitlines()),
                     "lexical_declarations": len(headers),
                     "theorems": [name for kind, name in headers if kind in ("theorem", "lemma")]})
    rows.sort(key=lambda r: (-r["physical_lines"], r["path"]))
    symbols = ("Artifact", "evalStmt", "Stmt", "source_to_model", "model_to_source")
    return {"base": BASE,
            "count_method": "physical lines; lexical declaration headers after nested-comment/string removal; not elaborated declaration counts; modules are not semantic families",
            "views_modules": len(views),
            "views_physical_lines": sum(r["physical_lines"] for r in rows),
            "views_lexical_declarations": sum(r["lexical_declarations"] for r in rows),
            "views_theorem_headers": sum(len(r["theorems"]) for r in rows),
            "local_import_closure_modules": len(closure),
            "execution_modules_in_closure": sorted(m for m in closure if m.startswith(("Solidity.Yul.Compilation.", "Solidity.Yul.Closed")) or m == "Solidity.Yul.Syntax"),
            "direct_execution_symbol_hits": {s: [lean[m] for m in views if re.search(r"\b"+s+r"\b", source(m))] for s in symbols},
            "largest_module_candidates_not_covered_families": rows[:10],
            "coverage_caution": "No equivalence follows from lexical absence or import closure. PhysicalStore imports Views.MemoryImages in the reverse direction, using Backend.Environment.runData rather than Evm.run. Artifact preserves the complete machine except stack; Views exports additional storage/memory/Source guarantees."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = json.dumps(measure(), indent=2)+"\n"
    target = HERE / "inventory.json"
    if args.check:
        if target.read_text() != text:
            raise SystemExit("inventory differs from frozen Git objects")
        print("inventory: PASS (frozen-base lexical counts and import closure)")
    else:
        target.write_text(text)
        print(target)


if __name__ == "__main__":
    main()
