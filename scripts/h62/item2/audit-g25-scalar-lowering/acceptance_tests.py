#!/usr/bin/env python3
"""Regression: a caller-supplied widened scope cannot earn acceptance credit."""
import json
import tempfile
from pathlib import Path
from unittest.mock import patch
from types import SimpleNamespace
import contextlib, io, sys
import unittest
import census
import collect_evidence


class ScopeAuthorityTests(unittest.TestCase):
    def test_authenticated_main_serializes_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/"tests/h62/item2/audit-g25-scalar-lowering").mkdir(parents=True)
            ownership=root/"ownership.json";ownership.write_text("{}")
            output=root/"evidence"
            scope=dict(new_file_scope=["scripts/h62/item2/audit-g25-scalar-lowering/**"],exclusive_files=[])
            def run(cmd,**kwargs):
                text="scripts/h62/item2/audit-g25-scalar-lowering/collect_evidence.py\n" if cmd[:3]==["git","diff","--name-only"] else ""
                return SimpleNamespace(returncode=0,stdout=text)
            argv=["collect_evidence.py","--repo",str(root),"--ownership",str(ownership),"--output",str(output),"--scope-base","HEAD","--scope-manifest",str(root/"scope.json")]
            with patch.object(sys,"argv",argv),patch("collect_evidence.load_scope",return_value=(scope,"synthetic-authority")),patch("collect_evidence.subprocess.run",side_effect=run),contextlib.redirect_stdout(io.StringIO()):
                collect_evidence.main()
            report=json.loads((output/"acceptance-results.json").read_text())
            self.assertEqual(report["scope_manifest_sha256"],"synthetic-authority")
            self.assertEqual(report["scope_violations"],[])
            self.assertEqual(report["frozen_statement_base"],census.BASE)
            self.assertEqual(len(report["commands"]),15)
            self.assertEqual(len(report["collector_source_sha256"]),64)

    def test_unrecognized_widened_manifest_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/"scope.json"
            p.write_text(json.dumps(dict(write_namespace="live",new_file_scope=["**"],exclusive_files=[])))
            with self.assertRaisesRegex(ValueError,"authority"):
                collect_evidence.load_scope(p)

    def test_wrong_namespace_rejected_even_with_test_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/"scope.json";p.write_text(json.dumps(dict(write_namespace="migration-overlay")))
            with patch.object(collect_evidence,"AUTHENTICATED_SCOPE_SHA256",census.digest(p.read_bytes())):
                with self.assertRaisesRegex(ValueError,"live scope"):
                    collect_evidence.load_scope(p)


if __name__=="__main__":unittest.main()
