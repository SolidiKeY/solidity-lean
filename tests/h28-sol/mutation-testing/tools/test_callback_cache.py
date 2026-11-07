"""Receipt forgery controls; these do not mock or stand in for Lean proofs."""
import copy
import json
import checked
from probe_cases import validate_imports
from pathlib import Path
import subprocess
import tempfile
import unittest
import extend_callback_cache as cache


class CallbackCacheTrustControls(unittest.TestCase):
    def test_changed_working_receipt_cannot_bless_changed_cache(self):
        self.check_forgery(commit_forgery=False)

    def test_committed_forged_receipt_cannot_replace_original_trust_anchor(self):
        self.check_forgery(commit_forgery=True)

    def check_forgery(self, commit_forgery):
        original = Path(__file__).resolve().parents[1] / "evidence/cache-bootstrap/manifest.json"
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            def git(*args):
                subprocess.run(["git", "-c", "user.name=H28 fixture", "-c", "user.email=h28@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args], cwd=repo, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            git("init", "-q")
            receipt = repo / cache.PREFIX / "evidence/cache-bootstrap/manifest.json"
            receipt.parent.mkdir(parents=True)
            receipt.write_bytes(original.read_bytes())
            git("add", "."); git("commit", "-qm", "original receipt fixture")
            forged = json.loads(receipt.read_text())
            artifact = next(iter(forged["artifact_sha256"]))
            forged["artifact_sha256"][artifact] = "0" * 64
            receipt.write_text(json.dumps(forged))
            if commit_forgery:
                git("add", "."); git("commit", "-qm", "forged receipt fixture")
            # Rejection must precede reading or copying any alleged cache.
            with self.assertRaisesRegex(ValueError, "exact committed trust anchor"):
                cache.extend(repo, repo / "alleged-cache", repo / "new-cache", repo / "logs")
            self.assertFalse((repo / "new-cache").exists())
            self.assertFalse((repo / "logs").exists())


class PinnedProducerDiagnosticControls(unittest.TestCase):
    def test_exact_warning_and_fault_variants(self):
        log = Path(__file__).resolve().parents[1] / "evidence/callback-cache-bootstrap/Solidity.Semantics.Callback.log"
        warnings = [m for m in checked.messages(log.read_text()) if m["severity"] == "warning"]
        text = "\n".join(json.dumps(m) for m in warnings)
        cache.cache_success("Solidity.Semantics.Callback", {"kind": "exit", "exit": 0}, text)
        altered = copy.deepcopy(warnings); altered[0]["data"] += " changed"
        error = {"severity": "error", "data": "a real proof failure"}
        for module, code, messages in [
            ("Other.Module", 0, warnings),
            ("Solidity.Semantics.Callback", 0, altered),
            ("Solidity.Semantics.Callback", 0, warnings + warnings),
            ("Solidity.Semantics.Callback", 0, warnings + [error]),
            ("Solidity.Semantics.Callback", 1, warnings),
            ("Solidity.Semantics.Callback", 0, [])]:
            with self.subTest(module=module, code=code, count=len(messages)):
                with self.assertRaises(ValueError):
                    cache.cache_success(module, {"kind": "exit", "exit": code}, "\n".join(json.dumps(m) for m in messages))
        # The owned witness gate must reject even the known producer warning.
        with self.assertRaises(ValueError):
            checked.success({"kind": "exit", "exit": 0}, text)

    def test_callback_import_requires_declared_real_dependency(self):
        base = {"Solidity.Calculus.Rules", "Solidity.Calculus.PremiseSound"}
        extra = "Solidity.Calculus.CallbackHolds"
        validate_imports(base, {"roots": [], "ordered_modules": []})
        validate_imports(base | {extra}, {"roots": [extra], "ordered_modules": [extra]})
        for imports, data in [(base | {extra}, {"roots": [], "ordered_modules": []}),
                              (base | {extra}, {"roots": [extra], "ordered_modules": []}),
                              (base | {"Other.Unreviewed"}, {"roots": [extra], "ordered_modules": [extra]})]:
            with self.assertRaises(ValueError):
                validate_imports(imports, data)
