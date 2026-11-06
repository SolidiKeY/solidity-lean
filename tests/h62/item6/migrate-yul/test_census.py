import importlib.util, pathlib, unittest
path = pathlib.Path(__file__).resolve().parents[4] / 'scripts/h62/item6/migrate-yul/census.py'
spec = importlib.util.spec_from_file_location('census', path); c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
class Scanner(unittest.TestCase):
    def test_comments_strings_offsets(self):
        s = 'import A\n/- import B /- nested -/ -/\n-- import C\n#eval "import D\\\""\nimport E\n'
        clean = c.scrub(s)
        self.assertEqual(len(clean),len(s)); self.assertEqual(clean.count('\n'),s.count('\n'))
        self.assertEqual(c.re.findall(r'^import (\w+)',clean,c.re.M),['A','E'])
    def test_character_literal(self):
        self.assertIn('def after',c.scrub("def ch := '\"'\ndef after := 1\n"))
    def test_attribute_anonymous_and_bridge(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            r=pathlib.Path(d); (r/'Solidity/Yul').mkdir(parents=True); (r/'Bridge').mkdir()
            (r/'Solidity/Yul/A.lean').write_text('namespace A\n\n@[noinline] def foo := 1\nlocal instance : Inhabited Nat := inferInstance\nexample : True := by trivial\n#guard true\n#guard_msgs in\n#check Nat\n')
            (r/'Bridge/B.lean').write_text('import Solidity.Yul.A\n')
            result=c.census(r)
            ds=result['modules']['Solidity.Yul.A']['lexical_declarations']
            self.assertEqual([(x['kind'],x['name'],x['line']) for x in ds],[('def','foo',3),('instance',None,4),('example',None,5)])
            self.assertEqual([x['kind'] for x in result['modules']['Solidity.Yul.A']['acceptance_commands']],['guard','guard_msgs','check'])
            self.assertEqual(result['external_consumers'],[{'importer':'B','importer_path':'Bridge/B.lean','package':'Bridge','dependency':'Solidity.Yul.A'}])
    def test_source_inventory(self):
        root=pathlib.Path(__file__).resolve().parents[4]
        result=c.census(root)
        self.assertEqual(result['yul_count'],len(list((root/'Solidity/Yul').rglob('*.lean'))))
        for key in ['build_order','keysort_order']:
            pos={n:i for i,n in enumerate(result[key])}
            for n in result[key]:
                for imp in result['modules'][n]['imports']:
                    if imp in pos: self.assertLess(pos[imp],pos[n])
if __name__ == '__main__': unittest.main()
