#!/usr/bin/env python3
"""Scoped actual calculus/compiler interface accounting; no coverage closure."""
import copy, importlib.util, json, pathlib, sys, unittest
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("heap", ROOT / "scripts/roadmap-v16-heap-audit.py")
h = importlib.util.module_from_spec(spec); spec.loader.exec_module(h); core = h.core
PUB = "099bfbe185731c354b12a40f28ccf5d98534c779"
PRE = "Solidity.Roadmap.V16."
PROPS = {
 "calculus_compiler_source": ["input", "diamond"],
 "calculus_compiler_diamond": ["input", "diamond"],
 "calculus_compiler_nonpaying": ["input", "nonpaying", "diamond"],
 "calculus_compiler_box_target": ["input", "box", "target"],
 "callback_compiler_nonpaying": ["input", "nonpaying", "postNoCallback", "diamond"],
 "callback_compiler_box_target": ["input", "postNoCallback", "box", "target"]}
CONTROL_NAMES = """core.fml_diamond core.fml_box core.callback_diamond core.client
core.source_post_and_cell core.wrong_output core.wrong_post core.box_at_actual_target
core.callback_box core.callback_box_at_target core.panic_rejected
memory.fml_diamond memory.callback_diamond memory.client memory.wrong_alias
memory.wrong_frame memory.wrong_allocation memory.wrong_failure
boundaries.payment_alternatives boundaries.rejected_payment_diamond boundaries.wrong_oracle_input
boundaries.post_callback_present boundaries.exhausted_false_diamond boundaries.exhausted_no_checked_input""".split()
REQUIRED = {PRE + "CalculusControls." + n for n in CONTROL_NAMES}
NAMES = {PRE + n for n in PROPS}
PRODUCERS = ["Solidity/Evm/Compiler.lean", "Solidity/Calculus/CallbackHolds.lean",
 "Solidity/Calculus/Logic.lean", "Solidity/Semantics/RunFrame.lean", "Solidity/Roadmap/Contracts.lean"]
LINKS = {"core.client": "callback_compiler_nonpaying", "memory.client": "callback_compiler_nonpaying",
 "core.callback_box_at_target": "callback_compiler_box_target", "core.box_at_actual_target": "calculus_compiler_box_target",
 "core.wrong_post": "calculus_compiler_nonpaying", "boundaries.payment_alternatives": "calculus_compiler_diamond",
 "boundaries.rejected_payment_diamond": "calculus_compiler_source", "boundaries.exhausted_no_checked_input": "calculus_compiler_source"}

def validate(nodes, policy, report):
 core.require(policy["revision"] == PUB, "wrong checked producer revision")
 core.require(set(policy["theorems"]) == NAMES, "absent/extra headline")
 core.require(set(policy["controls"]) == REQUIRED, "absent semantic control")
 for name in NAMES:
  core.require(name in nodes and h.contract(nodes[name]) == policy["theorems"][name], "changed actual theorem statement/premises")
  core.require([x["name"] for x in nodes[name]["premises"] if x["isProp"]] == PROPS[name.removeprefix(PRE)], "new assumption or erased input/guard")
 for name in REQUIRED:
  core.require(name in nodes and h.contract(nodes[name]) == policy["controls"][name], "changed actual inhabited/rejection control")
  core.require(not nodes[name]["premises"], "premise-only or polymorphic claimed closed control")
 reached = h.closure(nodes, NAMES | REQUIRED)
 core.require(set(policy["axiomPins"]) == set(reached) == set(policy["dependencyPins"]), "missing dependency/axiom pin")
 for name in reached:
  core.require(sorted(nodes[name]["axioms"]) == policy["axiomPins"][name], "actual axiom drift")
  core.require(sorted(set(nodes[name]["dependencies"])) == policy["dependencyPins"][name], "actual dependency drift")
 for name, consumer in LINKS.items():
  deps = {d for n in h.closure(nodes, [PRE + "CalculusControls." + name]) for d in nodes[n]["dependencies"]}
  core.require(PRE + consumer in deps, "client does not exercise NEW consumer")
 core.require(set(policy["producerHashes"]) == set(PRODUCERS), "missing producer signature source")
 import subprocess
 for path in PRODUCERS:
  published = subprocess.check_output(["git", "show", PUB + ":" + path], cwd=ROOT)
  core.require(core.digest(published) == policy["producerHashes"][path] == core.digest((ROOT / path).read_bytes()), "wrong/changed actual producer body")
 obligations = report["obligations"]
 core.require(not report["laneComplete"] and all(x["status"] == "open" for x in obligations), "scoped consumer falsely closes full coverage")
 ids = sorted(x["id"] for x in obligations)
 core.require(core.digest(json.dumps(ids, separators=(",", ":")).encode()) == policy["obligationIdsSha256"] and len(ids) == 2290, "dropped/changed inherited obligations")
 return reached

class CorruptionControls(unittest.TestCase):
 def test_live(self): validate(NODES, POLICY, REPORT)
 def test_negative_corruptions(self):
  mutations = [
   ("revision", lambda n,p,r:p.update(revision="0"*40)),
   ("missing headline", lambda n,p,r:n.pop(PRE+"calculus_compiler_source")),
   ("desired source", lambda n,p,r:n[PRE+"calculus_compiler_source"]["premises"].append(dict(name="source",isProp=True))),
   ("desired target", lambda n,p,r:n[PRE+"calculus_compiler_diamond"]["premises"].append(dict(name="target",isProp=True))),
   ("notExhausted", lambda n,p,r:n[PRE+"calculus_compiler_source"]["premises"].append(dict(name="notExhausted",isProp=True))),
   ("drop callback guard", lambda n,p,r:n[PRE+"callback_compiler_nonpaying"]["premises"].pop(-2)),
   ("erase refusal", lambda n,p,r:n[PRE+"calculus_compiler_diamond"].update(type="successful target only")),
   ("erase Rep", lambda n,p,r:n[PRE+"calculus_compiler_nonpaying"].update(type="True")),
   ("missing control", lambda n,p,r:p["controls"].pop(next(iter(REQUIRED)))),
   ("premise-only", lambda n,p,r:n[PRE+"CalculusControls.memory.client"]["premises"].append(dict(name="input",isProp=True))),
   ("polymorphic control", lambda n,p,r:n[PRE+"CalculusControls.memory.client"]["premises"].append(dict(name="alpha",isProp=False))),
   ("unapproved axiom", lambda n,p,r:n[PRE+"calculus_compiler_diamond"]["axioms"].append("sorryAx")),
   ("allowed axiom drift", lambda n,p,r:p["axiomPins"].update({PRE+"calculus_compiler_diamond":[]})),
   ("hidden oracle", lambda n,p,r:n[PRE+"CalculusControls.memory.client"]["dependencies"].append("Solidity.Roadmap.PublicCorrectness")),
   ("missing pin", lambda n,p,r:p["dependencyPins"].pop(next(iter(p["dependencyPins"])))),
   ("wrong body", lambda n,p,r:p["producerHashes"].update({PRODUCERS[0]:"0"*64})),
   ("coverage closure", lambda n,p,r:r["obligations"][0].update(status="closed")),
   ("dropped obligation", lambda n,p,r:r["obligations"].pop()),
   ("lane completion", lambda n,p,r:r.update(laneComplete=True))]
  for label, mutate in mutations:
   with self.subTest(label=label):
    n,p,r=copy.deepcopy(NODES),copy.deepcopy(POLICY),copy.deepcopy(REPORT)
    mutate(n,p,r)
    with self.assertRaises(core.Invalid):validate(n,p,r)

if __name__ == "__main__":
 meta = core.snapshot(pathlib.Path(sys.argv[1])); NODES = h.merged([meta])
 # H44: payload is regenerated outside Git; its exact historical bytes are pinned.
 policy_path = pathlib.Path(sys.argv[4]).resolve()
 import hashlib
 manifest = json.loads((ROOT / "tests/h55/g49-final-theorem/staging-manifest.json").read_text())
 policy_bytes = policy_path.read_bytes()
 core.require(hashlib.sha256(policy_bytes).hexdigest() == manifest["files"]["tests/roadmap-v16/parallel-premises.json"], "changed off-Git premise payload")
 POLICY = json.loads(policy_bytes)
 data = json.loads(pathlib.Path(sys.argv[2]).read_text()); core.validate_inventory(data["inventory"])
 REPORT = data["report"]; core.validate_report(REPORT,data["inventory"],core.validate_inventory(data["inventory"]))
 reached = validate(NODES,POLICY,REPORT)
 result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(CorruptionControls))
 if not result.wasSuccessful():raise SystemExit(1)
 pathlib.Path(sys.argv[3]).write_text(json.dumps(dict(head=meta["head"],revision=PUB,headlineTheorems=sorted(NAMES),closedControls=sorted(REQUIRED),scopedDependencies=len(reached),negativeCorruptions=19,obligationsOpen=len(REPORT["obligations"]),laneComplete=False),indent=2)+"\n")
 print("PASS 6 actual contracts,24 closed controls,19 negative corruptions;2290 OPEN")
