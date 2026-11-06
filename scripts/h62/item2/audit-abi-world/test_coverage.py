#!/usr/bin/env python3
"""Exercise proof-accounting rejection paths against copies of real receipts."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument("--evidence", type=Path, required=True)
args = parser.parse_args()
checker = Path(__file__).with_name("coverage.py")

def reject(name, mutate, expected):
    with tempfile.TemporaryDirectory(prefix="coverage-negative-", dir=args.evidence) as directory:
        folder = Path(directory)
        for source in args.evidence.glob("*.json"):
            shutil.copyfile(source, folder/source.name)
        for resource in folder.glob("*-resource.json"):
            obj=json.loads(resource.read_text())
            output=folder/(resource.name.removesuffix("-resource.json")+".json")
            if output.exists() and "stdout_file" in obj:
                obj["stdout_file"]=str(output.resolve())
                resource.write_text(json.dumps(obj))
        mutate(folder)
        run = subprocess.run([sys.executable, "-B", str(checker), "--evidence", str(folder)], text=True, capture_output=True)
        assert run.returncode != 0, f"{name}: accepted invalid input"
        assert expected in run.stderr, (name, run.stderr)
        print(name+": rejected")

def edit(folder, name, mutate):
    path = folder/(name+".json")
    obj = json.loads(path.read_text())
    mutate(obj)
    path.write_text(json.dumps(obj))
    # Keep paired negative fixtures self-consistently hashed to exercise the
    # intended semantic checks. A separate test deliberately omits this binding.
    resource=folder/(name+"-resource.json")
    if resource.exists():
        pair=json.loads(resource.read_text())
        pair["stdout_sha256"]=hashlib.sha256(path.read_bytes()).hexdigest()
        resource.write_text(json.dumps(pair))

def shrink(folder):
    def change(x):
        x["declarations"] = x["declarations"][:46]
        x["count"] = 46
    edit(folder, "census", change)

def stale(folder):
    def change(x):
        for key in ("support_before", "support_after"):
            x["_audit"][key]["tests/h62/item2/audit-abi-world/H62AbiWorld/WitnessSchema.lean"] = "0"*64
    edit(folder, "CodecWitnesses", change)

def trust(folder):
    def change(x):
        x["structuredContent"]["result"]["items"][0]["message"] = "'H62.invalid' depends on axioms: [H62.Unapproved]"
    edit(folder, "CodecWitnesses", change)

def wrong_tool(folder):
    edit(folder, "CodecWitnesses", lambda x: x["_audit"].update(tool="lean_file_outline"))

reject("shrunk census", shrink, "AssertionError")
reject("stale schema", stale, "stale dependency")
reject("unexpected axiom receipt", trust, "H62.Unapproved")
reject("wrong tool receipt", wrong_tool, "AssertionError")

def fidelity_mismatch(folder):
    def change(x):
        for item in x["structuredContent"]["result"]["items"]:
            if item.get("message", "").startswith("FIDELITY "):
                record=json.loads(item["message"][9:]);record["matched"]=False
                item["message"]="FIDELITY "+json.dumps(record)
                return
        raise AssertionError("missing fidelity fixture")
    edit(folder,"Fidelity",change)

def stale_guard(folder):
    edit(folder,"CodecWitnesses-resource",lambda x:x.update(guard_sha256="0"*64))

reject("fidelity mismatch",fidelity_mismatch,"fidelity mismatch")
reject("stale resource guard",stale_guard,"stale resource guard")

def unbound_output(folder):
    path=folder/"CodecWitnesses.json"
    obj=json.loads(path.read_text());obj["_audit"]["elapsed_seconds"]+=1
    path.write_text(json.dumps(obj))

reject("unbound proof output",unbound_output,"proof output digest mismatch")
