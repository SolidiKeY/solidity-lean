"""Guard frozen closure omissions and census substitution after authentication."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('original_callback',
    ROOT/'scripts/h62/item1/readonly-bind/check_original_callback.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class FrozenRefusals(unittest.TestCase):
    def test_snapshot_order_exact_bytes(self):
        raw={'Solidity/A.lean':b'import Solidity.B\nimport Init\n',
             'Solidity/B.lean':b'/- import '+m.profile.HELD.encode()+b' -/\n'}
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            order,pins=m.snapshot(raw.__getitem__,'Solidity.A',root)
            self.assertEqual(order,['Solidity/B.lean','Solidity/A.lean'])
            for name,data in raw.items():
                self.assertEqual((root/name).read_bytes(),data)
                self.assertEqual(pins[name]['source_sha256'],m.check.hashlib.sha256(data).hexdigest())

    def test_held_fence_precedes_git_read(self):
        with tempfile.TemporaryDirectory() as tmp:
            def forbidden_read(_):self.fail('held module was read')
            with self.assertRaisesRegex(ValueError,'historically held'):
                m.snapshot(forbidden_read,m.profile.HELD,Path(tmp))

    def test_cycle_foreign_and_missing(self):
        cases=[{'Solidity/A.lean':b'import Solidity.A\n'},
               {'Solidity/A.lean':b'import Foreign.Theory\n'},{}]
        with tempfile.TemporaryDirectory() as tmp:
            for data in cases:
                with self.subTest(data=data),self.assertRaises((ValueError,KeyError)):
                    m.snapshot(data.__getitem__,'Solidity.A',Path(tmp))

    def test_fabricated_original_artifact_refused(self):
        for raw in [b'{}',b'{"base":"'+m.BASE.encode()+b'","theorem_count":792}']:
            with self.assertRaisesRegex(ValueError,'artifact substitution'):
                m.select_interfaces(raw,{})

    def test_post_authentication_substitution_retains_original_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name in ['census.json','lean-toolchain']:
                with self.subTest(path=name):
                    path=Path(tmp)/name;path.write_bytes(b'authenticated')
                    digest=m.check.sha(path);protected={}
                    m.pin_authenticated_file(protected,path,digest)
                    path.write_bytes(b'substituted-after-authentication')
                    with self.assertRaises(ValueError):
                        m.pin_authenticated_file(protected,path,digest)
                    self.assertEqual(protected[str(path)],digest)
                    self.assertNotEqual(protected[str(path)],m.check.sha(path))


if __name__=='__main__':unittest.main()
