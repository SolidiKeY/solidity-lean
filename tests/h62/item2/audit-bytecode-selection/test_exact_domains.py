"""Guard exact-domain generation against implementation drift and output reuse."""
from pathlib import Path
import sys
import re
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-bytecode-selection"))
import exact_domains as target


class ExactDomainTests(unittest.TestCase):
    def setUp(self):
        self.macro = (ROOT / target.MACRO_PATH).read_text()
        self.fixture = (ROOT / target.FIXTURE_PATH).read_text()

    def test_existing_implementation_reused_byte_exactly_once(self):
        rendered = target.render(self.macro, self.fixture)
        fragment = target.macro_fragment(self.macro)
        self.assertEqual(rendered.count(fragment), 1)
        self.assertEqual(target.sha(fragment.encode()), target.MACRO_SHA256)
        self.assertIn("Only the original conclusion is replaced by True", rendered)
        self.assertEqual(rendered.count("hypotheses_of%"), 106)  # elaborator, one hundred three domains, two refusal probes

    def test_rendered_program_keeps_classifier_refusal_controls(self):
        program=target.render(self.macro,self.fixture)
        self.assertIn("#check hypotheses_of% Solidity.Backend.AbiEntry.HeadGate.program",program)
        self.assertIn("#check hypotheses_of% Eq.symm",program)
        self.assertIn("target is not a theorem",program)
        self.assertIn("universe-polymorphic target needs explicit review",program)

    def test_public_gate_methods_and_certificate_fields_accounted_once(self):
        expected=set()
        for gate in ("HeadGate","WordGate","SingleWordGate","BoolBinding","UnsignedGate","SignedGate","BytesGate"):
            source=(ROOT / ("Solidity/Backend/AbiEntry/"+gate+".lean")).read_text()
            expected.update("Solidity.Backend.AbiEntry."+gate+"."+name
                            for name in re.findall(r"(?m)^theorem (\w+)",source))
            interface=(ROOT / ("Solidity/Backend/AbiEntry/"+gate+"Interface.lean")).read_text()
            expected.update("Solidity.Backend.AbiEntry.Interface."+gate+"Certificate."+name
                            for name in re.findall(r"(?m)^  (\w+) : ∀",interface))
        expected.update("Solidity.Backend.AbiEntry.Interface.TailGuardCertificate."+field for field in ("correct","capacity"))
        expected.update("Solidity.Backend.AbiEntry.Interface.RawTailGuardCertificate."+field for field in ("raw","reference"))
        for gate in ("TailGuard","RawTailGuard","LengthCheck","OffsetChecks","HeadCheck"):
            source=(ROOT/("Solidity/Backend/AbiEntry/"+gate+".lean")).read_text()
            expected.update("Solidity.Backend.AbiEntry."+gate+"."+name for name in re.findall(r"(?m)^theorem (\w+)",source))
        expected.update("Solidity.Backend.AbiEntry.Interface.LengthCheckCertificate."+field for field in ("correct","capacity","lazy_revert"))
        expected.update("Solidity.Backend.AbiEntry.Interface.OffsetChecksCertificate."+field for field in ("tail_correct","region_correct","tail_capacity","region_capacity"))
        expected.update("Solidity.Backend.AbiEntry.Interface.HeadCheckCertificate."+field for field in ("correct","capacity","classified","early_revert"))
        self.assertEqual(set(target.TARGETS.values()),expected)
        self.assertEqual(len(target.TARGETS),len(expected))
        self.assertEqual(len(expected),103)

    def test_macro_drift_and_duplicate_boundaries_are_refused(self):
        for value in (self.macro.replace("explicitDomain info.type", "mkConst ``True"),
                      self.macro + "\nprivate theorem dependentToy", self.macro + "\nnamespace " + target.NAMESPACE + "\n"):
            with self.subTest(source=value[-40:]), self.assertRaises(ValueError):
                target.render(value, self.fixture)

    def test_target_omission_duplication_or_substitution_is_refused(self):
        for value in (self.fixture.replace("theorem word_correspondence_domain", "def word_correspondence_domain"),
                      self.fixture + self.fixture,
                      self.fixture.replace("WordGate.correspondence", "WordGate.selected")):
            with self.subTest(fixture=value[-40:]), self.assertRaises(ValueError):
                target.render(self.macro, value)

    def test_forbidden_proof_mechanisms_are_refused(self):
        for keyword in ("sorry", "admit", "axiom", "native_decide", "unsafe", "implemented_by"):
            with self.subTest(keyword=keyword), self.assertRaises(ValueError):
                target.render(self.macro, self.fixture + "\n" + keyword)

    def test_output_policy_refuses_repository_and_existing_paths(self):
        with self.assertRaises(ValueError):
            target.export(ROOT, ROOT / "generated-not-allowed.lean")
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "proof.lean"
            output.write_text("preserve")
            with self.assertRaises(ValueError): target.export(ROOT, output)
            self.assertEqual(output.read_text(), "preserve")

    def test_symlink_output_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/"real").mkdir();(root/"alias").symlink_to(root/"real", target_is_directory=True)
            with self.assertRaises(ValueError): target.export(ROOT, root/"alias/proof.lean")

    def test_manifest_binds_sources_and_never_claims_acceptance(self):
        sources={p:(ROOT/p).read_bytes() for p in target.PRODUCERS}
        sources[target.MAP]="\n".join("| `"+p+"` | fixture |" for p in target.PRODUCERS).encode()
        with patch.object(target.subprocess, "check_output", side_effect=lambda cmd, cwd: sources[cmd[-1].split(":",1)[1]]):
            program, manifest=target.build(ROOT)
        self.assertEqual(manifest["generated_lean_sha256"], target.sha(program.encode()))
        self.assertFalse(manifest["inspection_accepted"])
        self.assertFalse(manifest["witness_ledger_links_established"])
        self.assertEqual(manifest["targets"], target.TARGETS)
        with patch.object(target, "PRODUCERS", target.PRODUCERS+["Solidity/Backend/AbiEntry/WordValidation.lean"]), patch.object(target.subprocess, "check_output", side_effect=lambda cmd, cwd: sources[cmd[-1].split(":",1)[1]]):
            with self.assertRaisesRegex(ValueError,"outside frozen mapped census"): target.build(ROOT)
        with patch.object(target.subprocess, "check_output", return_value=b"changed producer"):
            with self.assertRaises(ValueError): target.build(ROOT)


if __name__ == "__main__":
    unittest.main()
