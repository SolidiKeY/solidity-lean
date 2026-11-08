"""Guard retained-machine audit integration without executing any verifier."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock

spec=importlib.util.spec_from_file_location("retained",Path(__file__).with_name("retained-transfers.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class Transfers(unittest.TestCase):
    def setUp(self):self.transfers,self.allowed,self.blocked,self.pin=m.policy()

    def test_conditional_external_target_cannot_disappear(self):
        detail=m.classify("100 <reviewed>:\n 100: 75 05 jne 107 <unreviewed>","reviewed",self.transfers,self.allowed)
        self.assertEqual(detail["externalBranches"],["unreviewed"])
        self.assertIn("unreviewed machine transfer",detail["failures"])

    def test_local_branches_and_exact_reviewed_call(self):
        text="100 <reviewed>:\n 100: 75 05 jne 107 <reviewed+0x7>\n 102: e8 00 callq 200 <lean_dec_ref_cold>"
        self.assertEqual(m.classify(text,"reviewed",self.transfers,self.allowed)["failures"],[])

    def test_indirect_and_missing_labels_fail(self):
        for text in ("100 <reviewed>:\n 100: 00 jmpq *%rax","100: 00 jne 200"):
            with self.subTest(text=text):self.assertTrue(m.classify(text,"reviewed",self.transfers,self.allowed)["failures"])

    def test_option_paths_symlinks_and_special_files_refused_before_tools(self):
        with tempfile.TemporaryDirectory() as tmp:
            target=Path(tmp)/"binary";target.write_bytes(b"fixture")
            alias=Path(tmp)/"alias";alias.symlink_to(target)
            fifo=Path(tmp)/"fifo"
            import os
            os.mkfifo(fifo)
            for path in (Path("--plugin=untrusted"),alias,fifo):
                with self.subTest(path=path),mock.patch.object(m,"run") as tools,self.assertRaisesRegex(ValueError,"canonical absolute regular"):
                    m.audit(path,target,target,Path(tmp))
                tools.assert_not_called()

    def test_wrong_binary_refused_before_tools_or_cached_results(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/"binary";p.write_bytes(b"not the retained executable")
            with mock.patch.object(m,"run") as tools,self.assertRaisesRegex(ValueError,"binary pin mismatch"):
                m.audit(p,p,p,Path(tmp))
            tools.assert_not_called()


if __name__=="__main__":unittest.main()
