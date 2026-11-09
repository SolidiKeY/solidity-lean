"""Guard receipt acceptance of substituted evidence or foreign theorem axioms."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location('encoding_fixture',
    ROOT/'scripts/h62/item1/readonly-bind/check_encoding_fixture.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class EvidenceRefusals(unittest.TestCase):
    def test_substitution(self):
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory)/name for name in
                     ['compiler', 'toolchain', 'staged.lean', 'module.olean', 'Probe.lean', 'axioms.log']]
            for path in paths:
                path.write_bytes(b'original')
            pins = {str(p): m.sha(p) for p in paths}
            m.verify_hashes(pins)
            for path in paths:
                with self.subTest(path=path.name):
                    path.write_bytes(b'substituted')
                    with self.assertRaises(ValueError):
                        m.verify_hashes(pins)
                    path.write_bytes(b'original')

    def test_post_compile_source_substitution(self):
        with tempfile.TemporaryDirectory() as directory:
            original, staged, artifact = [Path(directory)/name for name in
                                          ['original.lean', 'staged.lean', 'module.olean']]
            original.write_bytes(b'compiled source')
            def replacing_compiler(source, obj):
                obj.write_bytes(b'object')
                source.chmod(0o644)
                source.write_bytes(b'replacement')
                original.write_bytes(b'replacement')
            with self.assertRaises(ValueError):
                m.compile_staged(original, staged, artifact, replacing_compiler)

    def test_axiom_refusals(self):
        records = ["'"+m.PREFIX+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]"
                   for n in m.THEOREMS]
        self.assertEqual(len(m.parse_axioms('\n'.join(records))), 4)
        for bad in ['\n'.join(records[:-1]), '\n'.join(records+[records[0]]),
                    '\n'.join(records).replace('propext', 'sorryAx'),
                    '\n'.join(records).replace(m.PREFIX, 'Foreign.')]:
            with self.subTest(log=bad), self.assertRaises(ValueError):
                m.parse_axioms(bad)


if __name__ == '__main__':
    unittest.main()
