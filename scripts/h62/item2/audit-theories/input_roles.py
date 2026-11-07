#!/usr/bin/env python3
"""Reviewed premise-role inventory for the seventeen Bridge/Outcome interfaces.
Consumes a hash-verified historical frozen typed snapshot and checked CURRENT
selected-file certificates. Does not claim whole-census/current-definition
equivalence, witness generated candidates, or add witness counts.
"""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
from census import ROOT,BASE,scan

# Full ordered binder names are deliberate: post-premise binders must not vanish.
# Scope tags interpret existing hypotheses; they do not add or replace premises.
SPECS={}
def add(name,binders,configuration,premises,notes):
    SPECS[name]={"binders":binders.split(),"configuration":configuration.split(),
      "premises":premises,"notes":notes}

for suffix,binders,config in [
 ("obs_len_ref_some","C E st r w h","C E"),
 ("obs_word_ref_some","C P st r w h","C P"),
 ("full_of_push","C E st st' r val h","C E"),
 ("full_of_pushPlace","C E st r q h","C E")]:
    add("Solidity.Storage."+suffix,binders,config,{"h":"per-input-success-equation"},
      "C is configuration data with intrinsic vars_ok/nodup invariants, not a substitute for feasibility. Actual named roots, source/result storage and lookup/push success coexist; callback val is data, not a universally successful-callback premise.")
add("Solidity.Op0.denote_eval","C g s o","C s",{},
    "g is an actual typed global STATE VALUE, not a universal assumption that all states work. Packet gives a successful literal result.")
for suffix,binders,config,props in [
 ("Op1","C g a s o x d hx","C a s",["hx"]),
 ("Op2","C g a b s o x y da db hx hy","C a b s",["hx","hy"]),
 ("Op3","C g a b c s o x y z da db dc hx hy hz","C a b c s",["hx","hy","hz"])]:
    add("Solidity."+suffix+".denote_eval",binders,config,
      {p:"per-input-conditional-bridge-relation" for p in props},
      "Each BridgeO universally quantifies returned v only for THIS selected option x/y/z; it is not a relation for every possible argument. SOME arguments and real successful outputs prevent NONE-only vacuity. All denotations and options share g.H.")
P="Solidity.Theory.Progress."
add(P+"ends_of_notStuck","α r h","α",{"h":"per-result-universal-error-exclusion"},
    "The forall w premise excludes every stuck message for one correlated r, not for every result. A real .ok result satisfies the whole premise at once.")
add(P+"Ends.notStuck","α r h w","α",{"h":"per-result-ending-classification"},
    "The explicit w binder AFTER h is still an input. Result r, its Ends proof and w coexist; no individual-inhabitance shortcut.")
add(P+"ns_iff_ends","E Γ α m","E Γ α",{},
    "No frozen logical premise. Witness additionally supplies universal NS plus a real successful populated-local input; those are support, not new assumptions on the original theorem.")
add(P+"NS.ends","E Γ α m h x","E Γ α",{"h":"global-all-input-law-for-fixed-computation"},
    "NS m quantifies EVERY compatible state/local input and stuck message for fixed m. Its universal proof and actual populated-local x are packaged together. NS alone does not supply x or an admitted call.")
add(P+"not_ends_stuck","α w","α",{},
    "Only ordinary type/string inputs. The conclusion is negative; no contradictory input premise exists. Joint witness remains ordinary, not a new H69 impossibility disposition.")
add(P+"coreEnds","α r","α",{},
    "A result value, not a premise structure. A real successful .ok value is selected; exhaustive classification alone is not compiler totality.")
for suffix,binders in [("Prog.run_ends","C Γ Γ' σ P"),
 ("Prog.runF_ends","C Γ Γ' n P σ"),("Stmt.runF_ends","C Γ Γ' n s σ")]:
    add(P+suffix,binders,"C Γ Γ'",{},
      "Program/statement and state are intrinsically compatible data; explicit fuel where present is also data. A real bool declaration .ok run strengthens feasibility; no halt classification is substituted for compiler admission or target-gas success.")

def annotate(row,spec):
    binders=row["elaborated"]["binders"]
    assert [b["name"]for b in binders]==spec["binders"],"Full ordered binder census mismatch"
    props={b["name"]for b in binders if b["is_prop"]}
    assert props==set(spec["premises"]),"Logical premise role omitted or invented"
    config=set(spec["configuration"])
    assert config<=set(spec["binders"]) and not config&props,"Invalid configuration roles"
    roles=[]
    for i,b in enumerate(binders):
        role=spec["premises"].get(b["name"],
          "configuration-or-intrinsic-structure-data" if b["name"]in config else "correlated-per-input-data")
        if b["name"]=="g":role="per-input-global-state-value"
        roles.append(dict(b,index=i,role=role))
    return {"theorem":row["source_name"],"file":row["file"],"source_header":row["source_header"],
      "historical_frozen_elaborated_type_sha256":row["elaborated_type_sha256"],
      "binders":roles,"interpretation":spec["notes"],
      "documented_producing_lane":row["documented_producing_lane"],
      "owner_status":"Live route unconfirmed; informational under H82, not exact-file permission wait."}

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--proof-evidence",type=Path,required=True)
    ap.add_argument("--historical-evidence",type=Path,required=True)
    a=ap.parse_args();out=a.out.resolve();proof=a.proof_evidence.resolve();historical=a.historical_evidence.resolve()
    if any(p.is_relative_to(ROOT)for p in (out,proof,historical)):raise SystemExit("Use off-Git evidence paths")
    out.mkdir(parents=True,exist_ok=True)
    source=historical/"verified-census.json"
    manifest=dict((line.split("  ",1)[1],line.split("  ",1)[0])for line in (historical/"SHA256SUMS").read_text().splitlines())
    assert digest(source)==manifest["verified-census.json"],"Historical typed snapshot hash mismatch"
    old=json.loads(source.read_text());assert old["base"]==BASE
    cmd=[sys.executable,str(ROOT/"scripts/h62/item2/audit-theories/verify_subset.py"),"--evidence",str(proof),"--report",str(out/"role-subset-receipt.json"),
      "--module","Solidity/Theory/Bridge/Denote.lean","--module","Solidity/Theory/Progress/Outcome.lean"]
    run=subprocess.run(cmd,capture_output=True,text=True);assert run.returncode==0,(run.stdout,run.stderr)
    current=json.loads((out/"role-subset-receipt.json").read_text())
    certs={r["source_name"]:r["certificate"] for r in current["declarations"]}
    assert set(certs)==set(SPECS) and current["joint_explicit_statements"]==17
    originals={r["source_name"]:r for r in old["declarations"]}
    records=[]
    for name,spec in SPECS.items():
        row=originals[name]
        actual={r["source_name"]:r["source_header"]for r in scan((ROOT/row["file"]).read_text(),row["file"])}
        assert actual[name]==row["source_header"],name
        report=annotate(row,spec);report["current_joint_certificate"]=certs[name];records.append(report)
    out.mkdir(parents=True,exist_ok=True)
    payload={"frozen_assignment_base":BASE,"current_head":current["current_head"],
      "historical_typed_snapshot_sha256":digest(source),"historical_signature_boundary":"Historical original types + unchanged current source and fresh current joint certificates; no whole-tree definition-equivalence claim.",
      "declarations":records,"reviewed_role_records":17,"explicit_original_records_outside_this_role_snapshot":483,
      "new_joint_witnesses_added_by_inventory":0,"generated_candidates_dispositioned":0,"full_assignment_acceptance":False,
      "validation":{"subset_command":cmd,"exit":run.returncode,"decisive":run.stdout.strip()}}
    (out/"input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("INPUT_ROLES_PASS "+json.dumps({"reviewed_role_records":17,"new_joint_witnesses":0,"full_assignment_acceptance":False}))

if __name__=="__main__":main()
