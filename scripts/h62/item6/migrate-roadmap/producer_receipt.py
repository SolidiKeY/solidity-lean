#!/usr/bin/env python3
"""Publish an exact blocked producer receipt; no Lean, edits or network sends.
The partial producer head is fixed to the previously reviewed checkpoint.
"""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PRODUCER="767c5fda402f24b01c89507e8613e9fde415f022"
REL="Solidity/Roadmap/Contracts.lean"
THEOREM="Solidity.Roadmap.PublicCorrectness.transfer"
SOURCE_SHA256="96cfaa05721c2e8cbf40716bec351d5077f227c97a469337ec6b1e614c33bf79"
SOURCE_BLOB="b7cbc5cc7531bdaa8d4e061587c02d29608cc183"
PARENT=Path("/workspace/migrate-roadmap-evidence")
def sha(data):return hashlib.sha256(data).hexdigest()
def blob(data):return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
def git(*args):return subprocess.check_output(["git",*args],cwd=ROOT)
def validate_source(current,published,pinned):
    if current!=published or published!=pinned:raise ValueError("Contracts source differs from the reviewed unchanged producer/base")
    if sha(current)!=SOURCE_SHA256 or blob(current)!=SOURCE_BLOB:raise ValueError("Contracts exact source identity mismatch")
    lines=current.decode().splitlines()
    guard="#guard_msgs in #print axioms "+THEOREM
    indexes=[i for i,line in enumerate(lines) if line==guard]
    if len(indexes)!=1 or lines[indexes[0]-1]!="/-- info: '"+THEOREM+"' does not depend on any axioms -/":raise ValueError("original empty-axiom guard changed")
    return indexes[0]+1

def validate_h71(relay):
    if relay["current_import_closure_blocker"]!="B-MIGRATION-ROADMAP-CONTRACTS" or relay["file"]!=REL or relay["theorem"]!=THEOREM:raise ValueError("wrong current reported blocker")
    if relay["expected_axioms"]!=[]:raise ValueError("H71 cannot change original trust policy")
    if set(relay["observed_axioms_as_reported"])!={"propext","Classical.choice","Quot.sound"}:raise ValueError("secondary reported footprint changed")
    if relay["independently_reproduced_by_mrs"] is not False or relay["raw_bytes_verified_locally"] is not False:raise ValueError("secondary relay must not become independent evidence")
    clearance=relay["hash_clearance"]
    if clearance["status"]!="cleared_for_isolated_consumer_check_as_relayed" or clearance["current_reported_import_blocker"] is not False:raise ValueError("obsolete Hash import wait must not be repeated")
    if clearance["full_migration_gate_complete"] is not False or clearance["original_file_edit_authority"] is not False:raise ValueError("isolated clearance is not a full gate or write authority")
    if any(value is not False for value in relay["permissions"].values()):raise ValueError("routing grants no original edit/application/certificate permission")
def main():
    h71=sys.argv[1:]==["--h71"]
    out=PARENT/"h71-contracts-producer" if h71 else (Path(sys.argv[1]) if len(sys.argv)==2 else PARENT/"h70-contracts-producer")
    expected=PARENT/("h71-contracts-producer" if h71 else "h70-contracts-producer")
    if out.resolve()!=expected:raise ValueError("dedicated receipt evidence path required")
    subprocess.run(["git","merge-base","--is-ancestor",BASE,PRODUCER],cwd=ROOT,check=True)
    subprocess.run(["git","merge-base","--is-ancestor",PRODUCER,"HEAD"],cwd=ROOT,check=True)
    current=(ROOT/REL).read_bytes();published=git("show",PRODUCER+":"+REL);pinned=git("show",BASE+":"+REL)
    guard_line=validate_source(current,published,pinned)
    diff=git("diff",BASE,PRODUCER,"--",REL)
    if diff:raise ValueError("this partial receipt must not masquerade as a Contracts migration patch")
    patch=git("format-patch","--stdout",BASE+".."+PRODUCER)
    prior_patch=PARENT/"h70/original.patch"
    if prior_patch.read_bytes()!=patch:raise ValueError("reviewed partial producer patch mismatch")
    tickets_path=ROOT/"tests/h62/item6/migrate-roadmap/contracts-owner-tickets.json"
    tickets=json.loads(tickets_path.read_text())
    for ticket in tickets["tickets"]:
        if ticket["file"]!=REL or ticket["theorem"]!=THEOREM or ticket["expected_axioms"]!=[]:raise ValueError("ticket target/trust-policy mismatch")
        if set(ticket["observed_axioms_as_reported"])!={"propext","Classical.choice","Quot.sound"}:raise ValueError("unexpected reported footprint")
    rows=json.loads((PARENT/"old-api.json").read_text())
    old=next(row for row in rows if row["name"]==THEOREM)
    if not old["is_theorem"] or old["theorem_axioms"]!=[]:raise ValueError("old local baseline footprint mismatch")
    old_result=PARENT/"h62-roadmap-old-api-1793975052419846724/result.json"
    old_run=json.loads(old_result.read_text())
    if old_run["exit"]!=0 or old_run["guard"] is not None or old_run["inputs_after"][REL]!=SOURCE_SHA256:raise ValueError("old local baseline provenance mismatch")
    out.mkdir(parents=True,exist_ok=True)
    destination=out/"reviewed-partial-producer.patch"
    if destination.exists() and destination.read_bytes()!=patch:raise ValueError("unexpected existing producer patch; preserve it")
    destination.write_bytes(patch)
    receipt=dict(schema=1,status="blocked_partial_producer_not_ready_for_4_35_consumers",owner="solidity-h62-6-20261106/migrate-roadmap",branch=git("branch","--show-current").decode().strip(),repository=str(ROOT),base=BASE,
        reviewed_partial_producer_head=PRODUCER,
        source=dict(path=REL,sha256=SOURCE_SHA256,git_blob=SOURCE_BLOB,identical_at_base_producer_and_worktree=True,proof_line=1016,axiom_guard_line=guard_line),
        partial_patch=dict(path=str(destination),sha256=sha(patch),bytes=len(patch),from_base=BASE,to_head=PRODUCER,kind="Reviewed partial tooling/evidence patch; NOT a Contracts migration resolution"),
        contracts_source_diff=dict(bytes=len(diff),sha256=sha(diff)),contracts_migration_resolution_patch=None,
        theorem=THEOREM,expected_axioms=[],old_local_axioms=old["theorem_axioms"],old_local_result=str(old_result),old_type_debug=old["type_debug"],
        consumer_reports=tickets["tickets"],ticket_transport=tickets["transport"],normalized_ticket_copy_sha256=sha(tickets_path.read_bytes()),
        new_local_gate="NOT RUN: existing Lean performance STOP preserved; requester logs are remote paths, not locally verified logs",
        gate_boundary="Original empty-axiom guard is binding. Consumer-reported propext/Classical.choice/Quot.sound is a trust-guard failure, not permission to update guard/pins. No ready v4.35 Contracts resolution is published.",
        consumers_waiting=[t["requester"] for t in tickets["tickets"]],
        required_owner_disposition="Retain blocked until an exact-base reviewed resolution preserves the frozen statement, empty expected axiom footprint and original budgets, and current STOPs are resolved. Coordinate with migration-root-gate/live producer/G49 owner; no duplicate H55 work.",
        preserved_stops=dict(performance="B-PERF-INSPECTION: supplemental inspection wall+48.568879%,sampledRSS+156.378946%; no full-directory timing conclusion",ownership="No proof/guard/pin edit permission from routing; Evm proposal still unapplied"),
        publication="Local saved receipt/committed handoff only; no remote push, merge, PR, external message or default-branch publication",
        added_axioms=0,added_sorry=0,raised_proof_budgets=0)
    if h71:
        relay_path=ROOT/"tests/h62/item6/migrate-roadmap/contracts-mrs-h71-relay.json"
        relay=json.loads(relay_path.read_text());validate_h71(relay)
        receipt["h71_mrs_secondary_relay"]=relay
        receipt["normalized_h71_relay_sha256"]=sha(relay_path.read_bytes())
        receipt["current_reported_import_closure_blocker"]="B-MIGRATION-ROADMAP-CONTRACTS"
        receipt["hash_dependency_gate_boundary"]=relay["hash_clearance"]
        receipt["independent_mrs_reproduction_count"]=0
        receipt["primary_consumer_reports"]=2
        receipt["secondary_mrs_relays"]=1
        receipt["consumers_waiting"].append(relay["requester"])
    (out/"producer-receipt.json").write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(json.dumps(dict(head=PRODUCER,base=BASE,file_sha256=SOURCE_SHA256,file_git_blob=SOURCE_BLOB,patch_sha256=sha(patch),gate="BLOCKED; original empty-axiom guard retained",receipt=str(out/"producer-receipt.json"))))
if __name__=="__main__":main()
