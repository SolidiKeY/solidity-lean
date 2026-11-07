"""Guard regression: source/private/inherited candidates must not become kernel coverage."""
import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-bytecode-selection"))
import census
import linkage_manifest as link


class SourceClassificationTests(unittest.TestCase):
    def classify(self, text):
        return link.classify_source("Fixture.lean", text, census)

    def test_private_identity_never_guessed_and_comments_strings_ignored(self):
        text = '\nnamespace N\n/- private theorem fake : False := x -/\ndef msg := "private def fake := 1"\nprivate def helper := 1\nprivate theorem valid : True := True.intro\nend N\n'
        result = self.classify(text)
        self.assertEqual([r["candidate_user_name"] for r in result["private_declarations"]], ["N.helper", "N.valid"])
        self.assertTrue(all(r["observed_kernel_name"] is None for r in result["private_declarations"]))
        self.assertEqual([r["name_token_line"] for r in result["private_declarations"]], [5, 6])

    def test_multiline_parent_arguments_and_unicode_fields_retained(self):
        text = "namespace N\nstructure Child (a : Nat)\n    extends Parent (fun x => (x, a)), Other a where\n  α : Nat\n  «named field» : True\n  final : ∀ x : Nat,\n    x = x\nend N\n"
        row = self.classify(text)["structures"][0]
        self.assertEqual([p["expression"] for p in row["parents"]], ["Parent (fun x => (x, a))", "Other a"])
        self.assertEqual([f["name"] for f in row["fields"]], ["α", "«named field»", "final"])
        self.assertFalse(row["kernel_identity_verified"])
        self.assertTrue(all("proof_type" in f["classification"] for f in row["fields"]))

    def test_unsupported_header_and_multiline_field_not_silently_dropped(self):
        text = "structure NoWhere := oldType\nstructure WithField where\n  operation\n    (x : Nat) : Nat\n"
        rows = self.classify(text)["structures"]
        self.assertEqual(len(rows), 2)
        self.assertIn("unsupported", rows[0]["status"])
        self.assertEqual(len(rows[1]["unparsed_body_lines"]), 1)
        self.assertIn("operation", rows[1]["unparsed_body_lines"][0]["source"])

    def test_parent_commas_under_binders_not_split(self):
        self.assertEqual(link.split_parents("Base (fun (a, b) => a), Other { x := (1,2) }"),
                         ["Base (fun (a, b) => a)", "Other { x := (1,2) }"])
        for bad in ["Base,", "Base (x", "Base )"]:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                link.split_parents(bad)

    def records(self, text):
        return self.classify(text)["structures"]

    def test_diamond_canonical_source_field_once_with_both_routes(self):
        rows = self.records("namespace N\nstructure Base where\n  lawful : True\nstructure Left extends Base where\nstructure Right extends Base where\nstructure Join extends Left, Right where\nend N\n")
        join = link.inherited_candidates(rows)[-1]
        self.assertEqual(len(join["source_fields_once"]), 1)
        self.assertEqual(len(join["source_fields_once"][0]["routes"]), 2)
        self.assertEqual(join["kernel_obligations_verified"], 0)
        self.assertIn("not canonical kernel", join["classification"])

    def test_same_field_name_distinct_origins_not_conflated(self):
        rows = self.records("structure First where\n  lawful : True\nstructure Second where\n  lawful : True\nstructure Join extends First, Second where\n")
        join = link.inherited_candidates(rows)[-1]
        self.assertEqual(len(join["source_fields_once"]), 2)
        self.assertEqual({r["source_field"]["name"] for r in join["source_fields_once"]}, {"lawful"})

    def test_ambiguous_external_and_cyclic_parents_stay_open(self):
        rows = self.records("namespace A\nstructure Base where\nend A\nnamespace B\nstructure Base where\nend B\nstructure Child extends Base, External where\nstructure Cycle extends Cycle where\n")
        graph = link.inherited_candidates(rows)
        self.assertEqual(len(graph[-2]["unresolved_parents"]), 2)
        self.assertEqual(len(graph[-2]["unresolved_parents"][0]["source_candidates"]), 2)
        self.assertEqual(len(graph[-1]["cycles"]), 1)
        self.assertTrue(all(r["kernel_obligations_verified"] == 0 for r in graph))


class InspectionManifestTests(unittest.TestCase):
    TEMPLATE = "selected=[MODULES]; fingerprint=FINGERPRINT"
    def inputs(self, package):
        sources = {"Solidity/A.lean": "a" * 64, "Bridge/SolidityBridge/B.lean": "b" * 64}
        bridge = package == "Bridge"
        modules = ["SolidityBridge.B"] if bridge else ["Solidity.A"]
        payload = {"base": link.BASE, "modules": modules,
                   "source_sha256": {path: sha for path, sha in sources.items() if path.startswith("Bridge/" if bridge else "Solidity/")},
                   "inspection_template_sha256": link.sha(self.TEMPLATE.encode())}
        hashes = {"census_tool_sha256": "c" * 64, "generator_tool_sha256": "d" * 64, "emitter_sha256": "e" * 64}
        if bridge:
            payload.update(schema_version=2, package_root="Bridge", member_head=link.MEMBER,
                           module_sources={"SolidityBridge.B": "Bridge/SolidityBridge/B.lean"},
                           execution_status="not run", boundary="Generated only; no Lean execution, kernel inspection, source-to-kernel linkage, witness or acceptance.", **hashes)
        fingerprint = link.sha(json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=bridge).encode())
        source = "import Lean\nimport " + modules[0] + "\n" + self.TEMPLATE.replace("MODULES", "`" + modules[0]).replace("FINGERPRINT", fingerprint)
        pins = dict(payload, manifest_sha256=fingerprint, inspection_sha256=link.sha(source.encode()))
        return sources, hashes, source.encode(), pins

    def validate(self, package, raw, pins, sources, hashes):
        return link.validate_inspection(raw, pins, package, sources, self.TEMPLATE, hashes)

    def test_complete_package_membership_and_correct_bridge_prefix(self):
        for package in ["core", "Bridge"]:
            sources, hashes, raw, pins = self.inputs(package)
            job = self.validate(package, raw, pins, sources, hashes)
            self.assertEqual(len(job), 1)
            self.assertEqual(next(iter(job.values()))["package"], package)
            if package == "Bridge":
                self.assertEqual(next(iter(job)), "Bridge/SolidityBridge/B.lean")

    def test_missing_module_wrong_prefix_and_source_hash_refused(self):
        for package in ["core", "Bridge"]:
            sources, hashes, raw, pins = self.inputs(package)
            for mutation in ["module", "prefix", "hash"]:
                forged = copy.deepcopy(pins)
                if mutation == "module": forged["modules"] = []
                elif mutation == "prefix": forged["modules"][0] = "Bridge." + forged["modules"][0]
                else: forged["source_sha256"][next(iter(forged["source_sha256"]))] = "0" * 64
                with self.subTest(package=package, mutation=mutation), self.assertRaises(ValueError):
                    self.validate(package, raw, forged, sources, hashes)

    def test_mutated_program_even_with_rehashed_bytes_refused(self):
        for package in ["core", "Bridge"]:
            sources, hashes, raw, pins = self.inputs(package)
            raw += b"\n-- extra generated command\n"
            pins["inspection_sha256"] = link.sha(raw)
            with self.assertRaisesRegex(ValueError, "bytes differ"):
                self.validate(package, raw, pins, sources, hashes)

    def test_wrong_tool_false_execution_claim_and_extra_field_refused(self):
        sources, hashes, raw, pins = self.inputs("Bridge")
        for key, value in [("emitter_sha256", "0" * 64), ("execution_status", "pass"), ("unexpected", "pass")]:
            forged = copy.deepcopy(pins)
            forged[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.validate("Bridge", raw, forged, sources, hashes)


if __name__ == "__main__":
    unittest.main()
