"""Explicit coordinator dispositions; no original statement/model changes."""
import hashlib,json
from pathlib import Path
DECISIONS_FILE=Path(__file__).resolve().parent/"handoff/COORDINATOR-ANSWERS-20261107.json"
DECISIONS=json.loads(DECISIONS_FILE.read_text())
DECISIONS_SHA256=hashlib.sha256(DECISIONS_FILE.read_bytes()).hexdigest()
HISTORY_POLICY={"question":"Q-FROZEN-REBASE","status":"resolved-history-based-original-audit",
 "frozen_base":"c6f550e281a7e5affa9a99bc2cdaed556dec00e4","decision_sha256":DECISIONS_SHA256,
 "boundary":"Audit original statements in original history; rebased coverage separate. No versioned pairs or statement changes by auditor."}
ACCEPTED={"Solidity.Theory.Mutability.ContractWorld.World.enter_static":{
 "module":"PayableWitnesses","helper":"payable_static_inputs_impossible",
 "question":"Q-STATIC-VALUE","decision_sha256":DECISIONS_SHA256,
 "status":"H69-intentional-impossibility-certificate-present",
 "reason":"Intentional H69 separation boundary: static calls with nonzero value are excluded on purpose because the EVM forbids them. Frozen Context.Mode makes the joint hypotheses impossible.",
 "operational_refusal_coverage":False}}

def accepted_fields(name):
    item=ACCEPTED[name]
    return {"status":item["status"],"accepted_H69":True,"scope_decision":item["question"],
      "decision_sha256":item["decision_sha256"],"intentional_reason":item["reason"],
      "operational_refusal_coverage":False}
