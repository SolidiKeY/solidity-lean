#!/usr/bin/env python3
"""Conservative V16 constructor/G03/theorem accounting. No proof discharge.
Consumes actual Lean environment metadata, statements, dependencies and axiom
outputs read only. An explicit open row is required for every inventory item.
"""
import argparse, hashlib, json, pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = "2fe1f8932f96be15b00df03ba2cde46f64a87758"
LEDGER = "docs/feature-work/roadmap-g03-ledger.json"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PARENTS = {"Solidity." + n for n in ["Stmt", "Prog", "Val", "Src", "RevPart", "Lifetime.Step", "Lifetime.Trace", "Lifetime.Reachable", "Roadmap.Event", "Roadmap.Outcome", "Source.RExpr", "Source.RStmt"]}
STAGES = ["G48", "G49.01", "G49.02", "G49.03", "G50.01", "G50.02", "G51.01", "G51.02"]
class Invalid(ValueError): pass

def require(test, message):
    if not test: raise Invalid(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def sources(root):
    return {str(p.relative_to(root)):digest(p.read_bytes()) for p in (root/"Solidity/Roadmap/V16").glob("*.lean")}
def current_binding(root=ROOT):
    names=subprocess.check_output(["git","ls-files","-z","--cached","--others","--exclude-standard","*.lean"],cwd=root).decode().split("\0")
    h=hashlib.sha256()
    for name in sorted(set(n for n in names if n)):
        h.update(name.encode()+b"\0"+(root/name).read_bytes()+b"\0")
    files={"ledgerSha256":LEDGER,"extractorSha256":"tests/roadmap-v16/Inventory.lean",
      "runnerSha256":"scripts/roadmap-v16-check.py","accountingSha256":"scripts/roadmap-v16-accounting.py",
      "toolchainSha256":"lean-toolchain","lakefileSha256":"lakefile.toml"}
    return dict(base=BASE,head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(),
      sources=sources(root),leanTreeSha256=h.hexdigest(),**{k:digest((root/v).read_bytes()) for k,v in files.items()})
def raw_inventory(log):
    text=pathlib.Path(log).read_text()
    require(text.rstrip().endswith("exit=0"),"inventory command did not pass")
    def marker(prefix):
        lines=[s[len(prefix):] for s in text.splitlines() if s.startswith(prefix)]
        require(len(lines)==1,"missing/duplicate execution-time binding or actual Lean inventory: "+prefix)
        return json.loads(lines[0])
    before=marker("V16-BINDING-BEFORE ");after=marker("V16-BINDING-AFTER ")
    require(before==after,"source/revision changed during extraction")
    inv=marker("V16-INVENTORY ");inv["binding"]=before
    return inv

def snapshot(log, root=ROOT):
    actual=raw_inventory(log)
    require(actual["binding"]==current_binding(root),"stale execution-time source/revision binding")
    inv={k:v for k,v in actual.items() if k!="binding"}
    inv.update(actual["binding"],rawLogPath=str(pathlib.Path(log).resolve()),rawLogSha256=digest(pathlib.Path(log).read_bytes()))
    return inv

def validate_inventory(inv, root=ROOT):
    current=current_binding(root)
    require({k:inv[k] for k in current}==current,"wrong frozen/current revision, theorem/extractor/ledger source or toolchain")
    require(inv["rawLogSha256"] == digest(pathlib.Path(inv["rawLogPath"]).read_bytes()), "changed raw inventory log")
    actual = raw_inventory(inv["rawLogPath"])
    require(actual["binding"]==current,"stale execution-time source/revision binding")
    require(inv["inductives"] == actual["inductives"], "absent/altered actual constructors")
    require(inv["theorems"] == actual["theorems"], "absent/altered actual statement, dependency or axiom output")
    require(PARENTS <= {r["name"] for r in inv["inductives"]} and len(inv["inductives"]) == len({r["name"] for r in inv["inductives"]}), "absent/duplicate required inductive family")
    require(all(r["constructors"] for r in inv["inductives"]), "empty constructor family")
    names = [t["name"] for t in inv["theorems"]]
    require(names and len(names) == len(set(names)), "absent/duplicate theorem")
    for t in inv["theorems"]:
        require(t["type"] and "typeConstants" in t and "dependencies" in t, "absent actual statement/dependencies")
        require(set(t["axioms"]) <= AXIOMS, "unapproved axiom: "+t["name"])
    return json.loads((root/LEDGER).read_text())

def expected_obligations(inv, ledger):
    rows = {}
    for p in inv["inductives"]:
        for c in p["constructors"]:
            require("constructor:"+c not in rows, "duplicate constructor")
            rows["constructor:"+c] = {"kind":"constructor", "parent":p["name"]}
    for f in ledger["features"]:
        rows["feature:"+f["id"]] = {"kind":"feature", "scope":f["scope"], "owners":f["owners"], "restrictions":f.get("restrictions",[]), "missing":f.get("missing",[])}
    for kind,field in [("combination","combinations"),("symbolCombination","symbolCombinations")]:
        for i,r in enumerate(ledger[field]): rows[f"{kind}:{i}"] = {"kind":kind,"source":r}
    for s in STAGES:
        rows["stage:"+s] = {"kind":"stage","prerequisites":["independent SourceSpec/admission/progress/lowering", "integrated V12-V15 runtime/deployment/rollback", "concrete correspondence and full gates"]}
    return rows

def theorem_obligations(t):
    consts = set(t["typeConstants"])
    flags = []
    if any("PublicCorrectness" in n for n in consts): flags.append("assumed-PublicCorrectness")
    if any(n.endswith("Pass.Dom") for n in consts): flags.append("undischarged-pass-domain")
    if any(n.endswith("Cert") for n in consts): flags.append("actual-certificate-argument-required")
    if any("Frag" in n for n in consts): flags.append("residual-fragment-domain")
    flags.append("generic-or-witness-does-not-discharge-full-profile")
    return flags

def make_report(inv, ledger):
    return {"base":inv["base"],"head":inv["head"],"laneComplete":False,
      "obligations":[dict(id=k,status="open",**v) for k,v in sorted(expected_obligations(inv,ledger).items())],
      "theorems":[dict(t,obligations=theorem_obligations(t)) for t in inv["theorems"]],
      "boundary":"All Solidity inductives in this checked import closure, not a full source profile. Structural accounting only. Scope/exclusions unchanged; no coverage discharged.",
      "openPremises":["Forward/Guard and per-run hash premises", "certificate need computability", "actual init/step/rollback/encoding correspondence", "source and runtime prerequisites", "all required full gates"]}

def validate_report(report, inv, ledger):
    expected = make_report(inv, ledger)
    require(set(report)==set(expected), "unsupported report fields")
    require(report["boundary"]==expected["boundary"], "altered structural-only scope boundary")
    require(report["base"] == inv["base"] and report["head"] == inv["head"], "wrong report revision")
    require(report["laneComplete"] is False, "accounting cannot close G48-G51")
    rows = report["obligations"]; want = expected_obligations(inv,ledger)
    require(len(rows) == len(want) and {r["id"] for r in rows} == set(want), "absent/duplicate constructor, feature, combination or stage")
    for r in rows:
        require(r["status"] == "open", "unproved coverage claim")
        require({k:v for k,v in r.items() if k not in {"id","status"}} == want[r["id"]], "contradictory obligation")
    require(report["theorems"] == expected["theorems"], "missing/altered theorem, premise or trust accounting")
    require(report["openPremises"] == expected["openPremises"], "undischarged premises erased")

def validate_claims(claims, inv):
    thms = {t["name"]:t for t in inv["theorems"]}; seen = set()
    for c in claims:
        require(set(c)=={"id","theorem","kind"}, "unsupported claim fields")
        require(c["id"] not in seen, "contradictory/duplicate claim")
        seen.add(c["id"])
        require(c["theorem"] in thms, "absent actual theorem")
        flags = theorem_obligations(thms[c["theorem"]])
        require(c["kind"] in {"generic","witness"}, "premise-only or unproved full-scope claim: "+",".join(flags))
        if c["kind"]=="witness":
            controls=[".V16.Checks.",".V16.TransactionControls.",".V16.SessionControls.",".V16.SpecificationControls."]
            require(any(p in c["theorem"] for p in controls),"generic theorem is not an audited inhabited control")
            require(not any(f in flags for f in ["assumed-PublicCorrectness","undischarged-pass-domain","actual-certificate-argument-required","residual-fragment-domain"]),"premise-only theorem is not an inhabited certificate witness")
    return True

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean-log",required=True,type=pathlib.Path)
    ap.add_argument("--output",required=True,type=pathlib.Path)
    ap.add_argument("--claims",type=pathlib.Path)
    a=ap.parse_args(); inv=snapshot(a.lean_log); ledger=validate_inventory(inv)
    report=make_report(inv,ledger);validate_report(report,inv,ledger)
    if a.claims: validate_claims(json.loads(a.claims.read_text()),inv)
    a.output.write_text(json.dumps({"inventory":inv,"report":report},sort_keys=True,indent=2)+"\n")
    print(f"PASS: {len(report['obligations'])} explicit OPEN obligations; {len(inv['theorems'])} actual statements/dependencies/axiom sets; laneComplete=false")
if __name__=="__main__":main()
