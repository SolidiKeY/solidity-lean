"""Mutation controls for scope/evidence acceptance, not EVM execution tests."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("checker", ROOT / "scripts/check-precompile-agreement.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class InventoryControls(unittest.TestCase):
    def setUp(self):
        self.data = json.loads(checker.INVENTORY.read_text())

    def test_complete_source_inventory(self):
        self.assertEqual(checker.validate(self.data), [])

    def test_each_address_omission_rejected(self):
        for i in range(18):
            data = copy.deepcopy(self.data)
            del data["rows"][i]
            self.assertTrue(checker.validate(data), i)

    def test_duplicate_rejected(self):
        self.data["rows"][-1] = self.data["rows"][0]
        self.assertTrue(checker.validate(self.data))

    def test_address_change_rejected(self):
        self.data["rows"][-1]["address"] = 18
        self.assertTrue(checker.validate(self.data))

    def test_hash_change_rejected(self):
        self.data["pins"]["Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean"] = "0" * 64
        self.assertTrue(checker.validate(self.data))

    def test_missing_pin_rejected(self):
        del self.data["pins"]["Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean"]
        self.assertTrue(checker.validate(self.data))

    def test_invented_proof_rejected(self):
        self.data["rows"][3]["proof_status"] = "proved"
        self.data["rows"][3]["proofs"] = ["fake"]
        self.assertTrue(checker.validate(self.data))

    def test_swapped_vendor_definition_rejected(self):
        self.data["rows"][3]["vendor_definition"] = "Ξ_SHA256"
        self.assertTrue(checker.validate(self.data))

    def test_wrong_core_module_rejected(self):
        for replacement in ("does-not-exist.lean", "Solidity/Precompiles/Modexp.lean"):
            self.data["rows"][3]["core_module"] = replacement
            self.assertTrue(checker.validate(self.data))

    def test_missing_vendor_closure_pin_rejected(self):
        del self.data["pins"]["Bridge/vendor/EvmYul/PerformIO.lean"]
        self.assertTrue(checker.validate(self.data))

    def test_changed_classification_rejected(self):
        self.data["rows"][3]["classification"] = "fork-mismatch"
        self.assertTrue(checker.validate(self.data))

    def test_hidden_unsupported_row_rejected(self):
        self.data["rows"][10]["classification"] = "identity-candidate"
        self.assertTrue(checker.validate(self.data))

    def test_every_required_proof_and_fixture_omission_rejected(self):
        for row in self.data["rows"]:
            for field in ("proofs", "fixture_theorems"):
                if not row[field]: continue
                data = copy.deepcopy(self.data)
                target = next(r for r in data["rows"] if r["address"] == row["address"])
                target[field].pop()
                self.assertTrue(checker.validate(data), (row["address"], field))

    def test_success_only_malformed_charge_rejected(self):
        self.data["rows"][5]["charge_model"] = "successful-price-for-every-input"
        self.assertTrue(checker.validate(self.data))

    def test_universal_short_header_domain_rejected(self):
        self.data["rows"][8]["agreement_domain"] = "all-inputs"
        self.assertTrue(checker.validate(self.data))

    def test_crypto_output_promotion_rejected(self):
        self.data["rows"][0]["output_agreement"] = "kernel-arbitrary-bytes"
        self.assertTrue(checker.validate(self.data))

    def test_unsupported_proof_promotion_rejected(self):
        self.data["rows"][10]["proof_status"] = "kernel-matching-row"
        self.assertTrue(checker.validate(self.data))

    def test_valid_point_vector_omission_rejected(self):
        self.data["rows"][9]["core_vector_refs"].pop(0)
        self.assertTrue(checker.validate(self.data))

    def test_missing_transitive_core_pin_rejected(self):
        del self.data["pins"]["Solidity/Keccak.lean"]
        self.assertTrue(checker.validate(self.data))

    def test_vendor_revision_change_rejected(self):
        self.data["vendor_commit"] = "0"*40
        self.assertTrue(checker.validate(self.data))


class EvidenceControls(unittest.TestCase):
    def setUp(self):
        self.data = json.loads(checker.INVENTORY.read_text())
        self.receipt = json.loads((checker.TESTS/"evidence/kernel-receipt.json").read_text())

    def test_complete_receipt(self):
        self.assertEqual(checker.evidence_errors(self.data, self.receipt), [])

    def test_failed_receipt_rejected(self):
        self.receipt["status"] = "fail"
        self.assertTrue(checker.evidence_errors(self.data, self.receipt))

    def test_missing_proof_source_receipt_rejected(self):
        del self.receipt["sources"]["Bridge/SolidityBridge/PrecompileAgreement/Identity.lean"]
        self.assertTrue(checker.evidence_errors(self.data, self.receipt))

    def test_stale_axiom_source_receipt_rejected(self):
        self.receipt["sources"]["Bridge/tests/precompile-agreement/Axioms.lean"] = "0"*64
        self.assertTrue(checker.evidence_errors(self.data, self.receipt))

    def test_omitted_kernel_gate_rejected(self):
        del self.receipt["logs"]["Header-kernel.log"]
        self.assertTrue(checker.evidence_errors(self.data, self.receipt))

    def test_log_swap_rejected_even_with_updated_hash(self):
        log=(checker.TESTS/"evidence/Gas-kernel.log").read_text()
        self.assertTrue(checker.kernel_log_errors("Identity-kernel.log", log))

    def test_kernel_failure_footer_rejected(self):
        log=(checker.TESTS/"evidence/Identity-kernel.log").read_text().replace("EXIT=0", "EXIT=1")
        self.assertTrue(checker.kernel_log_errors("Identity-kernel.log", log))

    def test_late_failure_or_duplicate_kernel_footer_rejected(self):
        log=(checker.TESTS/"evidence/Identity-kernel.log").read_text()
        for extra in ("EXIT=1 SECONDS=1.000 PEAK_RSS=100 MIN_AVAILABLE=9999999999 RESOURCE_STOP=False\n",
                      "EXIT=0 SECONDS=1.000 PEAK_RSS=100 MIN_AVAILABLE=9999999999 RESOURCE_STOP=False\n"):
            self.assertTrue(checker.kernel_log_errors("Identity-kernel.log",log+"\n"+extra))

    def test_wrong_input_working_directory_rejected(self):
        build=(checker.TESTS/"evidence/pinned-input-build.log").read_text()
        wrong=build.replace("CWD="+str(ROOT)+" ","CWD=/tmp/unrelated ").replace("-o "+str(ROOT)+"/.lake/","-o /tmp/unrelated/.lake/")
        self.assertTrue(checker.input_build_errors(self.data,wrong))

    def test_input_build_all_headers_removed_rejected(self):
        import re
        build=(checker.TESTS/"evidence/pinned-input-build.log").read_text()
        stripped=re.sub(r"^\d+/45 SHA256=.*\n", "", build, flags=re.M)
        self.assertEqual(stripped.count("EXIT=0 "),45)
        self.assertTrue(checker.input_build_errors(self.data,stripped))

    def test_input_build_omission_rejected(self):
        import re
        build=(checker.TESTS/"evidence/pinned-input-build.log").read_text()
        blocks=re.split(r"(?=^\d+/45 SHA256=)",build,flags=re.M)
        blocks=[b for b in blocks if b]
        self.assertEqual(len(blocks),45)
        removed=next(i for i,b in enumerate(blocks) if b.splitlines()[0].endswith("Solidity/Precompiles/PointEval.lean"))
        self.assertTrue(checker.input_build_errors(self.data,"".join(blocks[:removed]+blocks[removed+1:])))

    def test_input_build_duplicate_rejected_with_45_successes(self):
        import re
        build=(checker.TESTS/"evidence/pinned-input-build.log").read_text()
        blocks=[b for b in re.split(r"(?=^\d+/45 SHA256=)",build,flags=re.M) if b]
        victim=next(i for i,b in enumerate(blocks) if b.splitlines()[0].endswith("Solidity/Precompiles/PointEval.lean"))
        blocks[victim]=blocks[victim-1]
        duplicated="".join(blocks)
        self.assertEqual(duplicated.count("EXIT=0 "),45)
        self.assertTrue(checker.input_build_errors(self.data,duplicated))



if __name__ == "__main__":
    unittest.main()
