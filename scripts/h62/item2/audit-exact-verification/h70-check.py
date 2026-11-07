#!/usr/bin/env python3
"""Reproduce/verify H70 independent-source witnesses without claiming full audit."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys

if not __debug__: raise SystemExit("optimized Python refused")
ROOT = Path.cwd()
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PREFIX = "tests/h62/item2/audit-exact-verification/"
SCRIPT = "scripts/h62/item2/audit-exact-verification/"
MODULES = ["Solidity.Calculus.BitArith", "Solidity.Calculus.LinearDecision",
 "Solidity.Calculus.LinearHypotheses", "Solidity.Calculus.LinearSyntax",
 "Solidity.Calculus.VisitedSet", "Solidity.Examples.Tactics.Recovery"]
AUDITS = ["JointWitness", "JointWitnessControls", "BitArithAudit",
 "LinearDecisionAudit", "LinearHypothesesAudit", "RecoveryAudit", "IndependentModuleCensus"]
SOURCE_AUDITS = {"Solidity/Calculus/BitArith.lean":"BitArithAudit",
 "Solidity/Calculus/LinearDecision.lean":"LinearDecisionAudit",
 "Solidity/Calculus/LinearHypotheses.lean":"LinearHypothesesAudit",
 "Solidity/Examples/Tactics/Recovery.lean":"RecoveryAudit"}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--evidence", type=Path, default=Path("/workspace/h62-audit-h70-evidence"))
parser.add_argument("--run", action="store_true")
args = parser.parse_args()
evidence = args.evidence.resolve()
evidence.mkdir(exist_ok=True)
hashfile = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()


def source_plan():
    return subprocess.check_output([sys.executable, SCRIPT+"import-plan.py", *MODULES], text=True,
                                  env={**os.environ,"PYTHONDONTWRITEBYTECODE":"1"})


def snapshots(plan):
    paths = [row+".lean" for row in plan.splitlines()] + [PREFIX+x+".lean" for x in AUDITS]
    paths += [SCRIPT+x for x in ("bounded-check.sh","import-plan.py","h70-check.py","census.py","verify.py")]
    paths += [PREFIX+"VisitedSetAudit.lean", PREFIX+"witness-ledger.json"]
    result = {}
    prior_root = Path("/workspace/h62-audit-evidence")
    for name in ("bounded-audit.receipt.json","bounded-audit.log","bounded-audit.exit","source-census.json"):
        result["prior_evidence:"+name]=hashfile(prior_root/name)
    for rel in paths:
        if rel.startswith("Solidity/"):
            frozen = subprocess.check_output(["git","show",BASE+":"+rel])
            if (ROOT/rel).read_bytes() != frozen: raise ValueError("frozen drift: "+rel)
        result[rel] = hashfile(ROOT/rel)
    return result


def run_phase(name, plan=None, mode="imports"):
    if plan is not None: (evidence/"import-plan.txt").write_text(plan)
    command = ["bash",SCRIPT+"bounded-check.sh",mode]
    result = subprocess.run(command, env={**os.environ,"H62_AUDIT_EVIDENCE":str(evidence)})
    log = (evidence/("bounded-"+mode+".log")).read_bytes()
    (evidence/(name+".log")).write_bytes(log)
    (evidence/(name+".exit")).write_text(str(result.returncode)+"\n")
    if result.returncode != 0 or not log.endswith(("COMPLETED "+mode+"\n").encode()):
        raise RuntimeError("incomplete/failed phase: "+name)
    return dict(command=command, exit=result.returncode, log=name+".log", log_sha256=hashfile(evidence/(name+".log")))


plan = source_plan()
if args.run:
    before_hashes = snapshots(plan)
    phases = {"keysort":run_phase("h70-keysort",mode="keysort")}
    phases["before"] = run_phase("h70-before",plan*5)
    proof_plan = "".join(PREFIX+x+"\n" for x in AUDITS)
    phases["proof"] = run_phase("h70-proof",proof_plan)
    phases["after"] = run_phase("h70-after",plan*5)
    if snapshots(plan) != before_hashes: raise RuntimeError("source changed during checks")
    receipt = dict(schema=1, base=BASE, hashes=before_hashes, phases=phases,
        original_plan=plan, proof_plan=proof_plan,
        archive_sha256="7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d")
    (evidence/"h70-receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")

receipt = json.loads((evidence/"h70-receipt.json").read_text())
if receipt["base"] != BASE or receipt["hashes"] != snapshots(plan): raise ValueError("stale source receipt")
if receipt["archive_sha256"] != hashfile(evidence/"toolchain/lean-4.35.0-linux.tar.zst"):
    raise ValueError("official toolchain archive mismatch")
if set(receipt["phases"])!={"keysort","before","proof","after"}: raise ValueError("missing/unexpected required phase")
proof_plan = "".join(PREFIX+x+"\n" for x in AUDITS)
if receipt["original_plan"]!=plan or receipt["proof_plan"]!=proof_plan: raise ValueError("unexpected stored workload plan")
for name, phase in receipt["phases"].items():
    log = evidence/phase["log"]
    if phase["exit"] != 0 or phase["log_sha256"] != hashfile(log): raise ValueError("invalid phase receipt: "+name)
    if (evidence/(log.stem+".exit")).read_text().strip() != "0": raise ValueError("failed compiler phase")
    mode = "keysort" if name=="keysort" else "imports"
    if phase["command"] != ["bash",SCRIPT+"bounded-check.sh",mode]: raise ValueError("unexpected phase command")
    text = log.read_text()
    expected_workload = (["Solidity/KeySort"] if name=="keysort" else
                         proof_plan.splitlines() if name=="proof" else (plan*5).splitlines())
    checks = re.findall(r"^CHECK (\S+) ",text,re.M)
    passes = re.findall(r"^PASS (\S+) ",text,re.M)
    if checks!=expected_workload or passes!=expected_workload: raise ValueError("missing/unexpected workload: "+name)
    if "Lean (version 4.35.0," not in text or "Lake version 5.0.0-src+eb6cafb" not in text:
        raise ValueError("unexpected runtime version")
    if "LIMITS memory.max=12884901888 memory.swap.max=0 LEAN_NUM_THREADS=1" not in text:
        raise ValueError("missing resource-bound evidence")
    if not log.read_text().endswith("COMPLETED "+mode+"\n"): raise ValueError("missing completion")
proof_log = (evidence/receipt["phases"]["proof"]["log"]).read_text()
if re.search(r": error(?:\(|:)",proof_log): raise ValueError("proof log contains errors")

# The earlier nine VisitedSet witnesses retain their own exact source/log receipt;
# they are not represented as freshly replayed Lean proofs in this H70 run.
prior = subprocess.run([sys.executable,SCRIPT+"verify.py","--evidence","/workspace/h62-audit-evidence"],
    capture_output=True,text=True,env={**os.environ,"PYTHONDONTWRITEBYTECODE":"1"})
if prior.returncode!=0: raise ValueError("prior VisitedSet receipt failed: "+prior.stdout+prior.stderr)

# Fresh frozen-source inventory is computed by the owned scanner, never accepted
# merely because a prior output claims completeness.
from census import generate
source = generate(ROOT)
expected = {r["name_candidate"]:r for r in source["declarations"] if r["file"] in SOURCE_AUDITS}
if len(expected)!=99: raise ValueError("unexpected frozen source membership")
matched = re.findall(r"^JOINT_INPUTS original=(\S+) helper=(\S+) binders=(\d+)$",proof_log,re.M)
frozen = [(original,helper,int(count)) for original,helper,count in matched if original in expected]
if len(frozen)!=99 or {x[0] for x in frozen}!=set(expected): raise ValueError("missing/duplicate frozen source instance")
if len({x[1] for x in frozen})!=99: raise ValueError("duplicate helper")
for original,_,_ in frozen:
    if "FROZEN_EXPR "+original+":" not in proof_log: raise ValueError("missing exact kernel type")
axioms = {}
for name,_,values in re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^]]*)\])",proof_log):
    used={x.strip() for x in values.split(",") if x.strip()}
    if not used<=ALLOWED: raise ValueError("nonstandard axiom: "+name)
    axioms[name]=sorted(used)
for _,helper,_ in frozen:
    if helper not in axioms: raise ValueError("missing helper axiom report: "+helper)
controls={"Solidity.H62.ExactAudit.LinearHypotheses."+n for n in
 ("supported_projection_succeeds","reject_all_projection_control","zero_fuel_has_no_certificate")}
controls|={"Solidity.H62.ExactAudit.Recovery."+n for n in ("invalid_parity_rejected","reject_all_recovery_control")}
if not controls<=set(axioms): raise ValueError("missing local control report")

exports=[]
for line in proof_log.splitlines():
    if line.startswith("MODULE_THEOREMS_JSON "):
        exports.append(json.loads(line.split(" ",1)[1]))
if len(exports)!=6 or {x["module"] for x in exports}!=set(MODULES): raise ValueError("missing/duplicate compiler module census")
source_names={r["name_candidate"] for r in source["declarations"] if r["file"] in
 {m.replace(".","/")+".lean" for m in MODULES}}
entries=[t for m in exports for t in m["theorems"]]
if len({t["name"] for t in entries})!=len(entries): raise ValueError("duplicate compiler theorem")
if not source_names<={t["name"] for t in entries}: raise ValueError("source theorem missing from compiler census")
for entry in entries:
    if not set(entry["axioms"])<=ALLOWED: raise ValueError("nonstandard exported theorem axiom")
    entry["coverage"]=("named_source_h70_witness" if entry["name"] in expected else
                       "named_source_prior_witness" if entry["name"] in source_names else "uncovered_compiler_declaration")
    entry["owner"]="area producer unresolved; no exclusion"
(evidence/"h70-compiler-census.json").write_text(json.dumps(sorted(entries,key=lambda e:e["name"]),indent=2)+"\n")
ledger=[dict(original=original,helper=helper,binders=count,source_id=expected[original]["id"],
 source_signature_sha256=expected[original]["source_signature_sha256"],axioms=axioms[helper]) for original,helper,count in frozen]
(evidence/"h70-witness-ledger.json").write_text(json.dumps(ledger,indent=2)+"\n")

samples={}
for phase in ("before","after"):
    values={};start=None;module=None
    for line in (evidence/receipt["phases"][phase]["log"]).read_text().splitlines():
        if line.startswith("CHECK "):
            _,module,when=line.split();start=float(when)
        if line.startswith("PASS "):
            _,done,when=line.split()
            if done!=module: raise ValueError("timing pair mismatch")
            duration=float(when)-start
            if not math.isfinite(duration) or duration<=0: raise ValueError("invalid timing duration")
            values.setdefault(module,[]).append(duration)
    if any(len(v)!=5 for v in values.values()) or set(values)!=set(plan.splitlines()): raise ValueError("missing timing samples")
    samples[phase]=values
metrics={}
for module in samples["before"]:
    before=statistics.median(samples["before"][module]);after=statistics.median(samples["after"][module])
    metrics[module]=dict(before=before,after=after,delta_percent=(after/before-1)*100)
(evidence/"h70-timing.json").write_text(json.dumps(dict(samples=samples,medians=metrics),indent=2)+"\n")
slow=[m for m,v in metrics.items() if v["delta_percent"]>10]
if slow: raise SystemExit("PERFORMANCE_STOP >10%: "+", ".join(slow))
summary=dict(status="partial",new_named_source_instances=len(frozen),
 named_source_in_compiler_census=len(source_names),compiler_theorems=len(entries),
 uncovered_compiler_declarations=sum(t["coverage"]=="uncovered_compiler_declaration" for t in entries),
 compiler_modules=len(exports),full_assignment_complete=False)
(evidence/"h70-summary.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary))
