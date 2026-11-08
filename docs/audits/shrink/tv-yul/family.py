#!/usr/bin/env python3
"""Frozen H264 candidate inventory, not a proved replacement or timing result."""
import argparse
import json
import re
import subprocess
from pathlib import Path
from inventory import BASE, strip_comments

HERE = Path(__file__).resolve().parent


def git(*args):
    return subprocess.check_output(["git", *args], text=True)


def measure():
    paths = git("ls-tree", "-r", "--name-only", BASE, "Solidity/Yul/Compilation").splitlines()
    families = []
    for path in paths:
        if not path.endswith("Compilation.lean"):
            continue
        completion = path[:-len("Compilation.lean")] + "Completion.lean"
        if completion not in paths:
            continue
        modules = []
        for file in (path, completion):
            raw = git("show", BASE+":"+file)
            clean = strip_comments(raw)
            declarations = re.findall(r"^ *(?:(?:private|protected|noncomputable|unsafe) +)*(?:def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|axiom)\s+([^\s{(:]+)", clean, re.M)
            namespace = re.search(r"^namespace\s+(\S+)", clean, re.M).group(1)
            statements = []
            for match in re.finditer(r"^ *(?:private +)?(?:theorem|lemma)\s+([^\s{(:]+)", clean, re.M):
                end = clean.find(":=", match.end())
                if end < 0:
                    raise ValueError("missing theorem body: "+file)
                statements.append({"name": namespace+"."+match.group(1),
                                   "line": clean.count("\n", 0, match.start())+1,
                                   "signature": clean[match.start():end].strip()})
            modules.append({"path":file, "physical_lines":len(raw.splitlines()),
                            "lexical_declarations":len(declarations), "theorem_statements":statements})
        families.append({"stem":Path(path).stem[:-len("Compilation")],
                         "physical_lines":sum(m["physical_lines"] for m in modules),
                         "lexical_declarations":sum(m["lexical_declarations"] for m in modules),
                         "modules":modules})
    families.sort(key=lambda x:(-x["physical_lines"], x["stem"]))
    candidate = next(f for f in families if f["stem"] == "ScopedControl")
    return {"base":BASE, "authorization":"H264 A", "status":"candidate; prototype and export preservation unproved",
            "method":"Matching *Compilation.lean/*Completion.lean pairs only; excludes Controls fixtures and shared dependencies. Physical source lines and lexical declarations, not elaborated declaration counts or proof-only spans. Signatures retain original premises.",
            "ranked_pairs":[{k:f[k] for k in ("stem","physical_lines","lexical_declarations")} for f in families],
            "candidate":candidate,
            "caution":"Largest matching pair is not a proved largest covered family until the checker coverage is established. Retained old proofs must count in the after workload; reference output equality is not general semantic completeness."}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args=parser.parse_args()
    text=json.dumps(measure(),indent=2)+"\n"
    path=HERE/"family.json"
    if args.check:
        if path.read_text()!=text:
            raise SystemExit("family inventory differs from frozen source")
        print("family inventory: PASS")
    else:
        path.write_text(text)
        print(path)


if __name__=="__main__":
    main()
