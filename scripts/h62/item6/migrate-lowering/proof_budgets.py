#!/usr/bin/env python3
"""Lexical proof-budget classification, never an elaborated effective-option proof."""
import argparse, collections, hashlib, json, re
from pathlib import Path
from census import uncomment

def code_only(source):
    source=uncomment(source)
    return re.sub(r'"(?:[^"\\]|\\.)*"|«[^»]*»',lambda m:"".join("\n" if c=="\n" else " " for c in m[0]),source)

def classify(source):
    code=code_only(source); uses=[]
    for m in re.finditer(r"(?<![\w.])decide\b",code):
        suffix=code[m.end():]; flags=re.match(r"(?:\s*\+(?:kernel|native|revert)\b)*",suffix)[0]
        engine="native-flag" if "+native" in flags else "kernel-flag" if "+kernel" in flags else "default-candidate"
        uses.append({"line":code.count("\n",0,m.start())+1,"engine":engine,"lexical_context":"term-application-candidate" if suffix.lstrip().startswith("(") else "tactic-or-term-candidate"})
    directives=[]
    for m in re.finditer(r"\bset_option\s+(maxHeartbeats|maxRecDepth|synthInstance.maxHeartbeats|synthInstance.maxSize)\s+([^\s]+)",code):
        directives.append({"line":code.count("\n",0,m.start())+1,"option":m[1],"value_text":m[2],"scope":"lexical; effective command scope not elaborated"})
    features={name:bool(re.search(pattern,code)) for name,pattern in {"rfl":r"\brfl\b","simp":r"\bsimp\b","omega":r"\bomega\b","native_decide":r"\bnative_decide\b","eval_command":r"#eval\b","reduce_command":r"#reduce\b","axiom_print":r"#print\s+axioms\b"}.items()}
    modes=sorted({u["engine"] for u in uses})
    return {"budget_class":"explicit-source-option" if directives else "no-explicit-source-option","explicit_options":directives,"decide_occurrences":uses,"decide_modes":modes,"features":features}

def defaults(toolchain):
    core=toolchain/"src/lean/Lean/CoreM.lean"; prelude=toolchain/"src/lean/Init/Prelude.lean"
    heartbeat=int(re.search(r"register_builtin_option maxHeartbeats\s*:\s*Nat\s*:=\s*\{\s*defValue\s*:=\s*(\d+)",uncomment(core.read_text()))[1])
    depth=int(re.search(r"def defaultMaxRecDepth\s*:=\s*(\d+)",uncomment(prelude.read_text()))[1])
    return {"maxHeartbeats":heartbeat,"maxRecDepth":depth,"source_hashes":{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (core,prelude)},"boundary":"Installed-source defaults; effective elaborated command options remain unvalidated."}

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--root",type=Path,default=Path.cwd());p.add_argument("--artifacts",type=Path,default=Path("/workspace/migrate-lowering-artifacts"));a=p.parse_args()
    census=json.loads((a.artifacts/"evidence/census-base.json").read_text());rows=[]
    for row in census["modules"]:
        path=a.root/row["path"];digest=hashlib.sha256(path.read_bytes()).hexdigest()
        if digest!=row["sha256"]:raise SystemExit("source changed since pinned census: "+str(path))
        rows.append(dict(path=row["path"],module=row["module"],source_sha256=digest,**classify(path.read_text())))
    toolchains={"old":defaults(Path("/workspace/.setup/tools/lean-4.24.0-linux")),"new":defaults(a.artifacts/"toolchains/lean-4.35.0-linux")}
    counts={"files":len(rows),"budget_classes":dict(collections.Counter(r["budget_class"] for r in rows)),"decide_modes_files":{mode:sum(mode in r["decide_modes"] for r in rows) for mode in ("default-candidate","kernel-flag","native-flag")},"native_decide_files":sum(r["features"]["native_decide"] for r in rows)}
    deps=[{"module":m,"owner":"solidity-h62-6-20261106/"+owner,"state":"waiting-owner-input-for-elaborated-API-and-axiom-comparison","basis":"current coordinator H70 disposition; relay is not agreement or validation"} for m,owner in [("Solidity.Syntax.Raw","migrate-syntax"),("Solidity.Hash.CollisionBound","migrate-hash"),("Solidity.Source.Ctor","migrate-source")]]
    result={"base":census["base"],"counts":counts,"toolchain_defaults":toolchains,"source_defaults_equal":all(toolchains["old"][k]==toolchains["new"][k] for k in ("maxHeartbeats","maxRecDepth")),"requested_subset":{"count":224,"manifest_recovered":False,"reconciled":False,"action":"Classify all 661 assigned files; do not invent a 224-file membership."},"owner_dependencies":deps,"rows":rows,"boundary":"Lexical candidate inventory, not tactic elaboration, proof validity, API equality, axiom acceptance or a performance pass. Comments/strings/quoted identifiers excluded; quotations and tactic configurations still need elaborated review."}
    output=a.artifacts/"evidence/proof-budget-classification.json";output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"counts":counts,"source_defaults_equal":result["source_defaults_equal"],"subset_reconciled":False,"output":str(output)},sort_keys=True))
