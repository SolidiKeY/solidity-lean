"""Corrupt actual snapshot records to prove that frozen-interface gates refuse them.
Usage: test_frozen.py OLD_LOG NEW_LOG
"""
import json,pathlib,subprocess,sys,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
old_log,new_log=map(pathlib.Path,sys.argv[1:3]); sys.argv=sys.argv[:1]
class NegativeControls(unittest.TestCase):
    def check_corruption(self,edit):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d)/'new.log'; rows=[]
            for line in new_log.read_text().splitlines():
                if line.startswith('FROZEN_JSON '):
                    row=json.loads(line[12:]); row=edit(row)
                    if row is None: continue
                    line='FROZEN_JSON '+json.dumps(row)
                rows.append(line)
            p.write_text('\n'.join(rows))
            r=subprocess.run([sys.executable,str(ROOT/'scripts/h62/item6/migrate-language/compare-frozen.py'),str(old_log),str(p),str(pathlib.Path(d)/'result.json')],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            self.assertNotEqual(r.returncode,0)
    def test_changed_range_theorem(self):
        def edit(r):
            if r['name']=='Solidity.Language.FixedPoint.Fx.wrapInt_inRange':r['type']='S(0)'
            return r
        self.check_corruption(edit)
    def test_changed_intrinsic_validity_field(self):
        def edit(r):
            if r["name"]=="Solidity.Language.FixedPoint.FxTy.valid":r["type"]="S(0)"
            return r
        self.check_corruption(edit)
    def test_missing_anonymous_instance(self):
        self.check_corruption(lambda r:None if r['name']=='Solidity.Language.FixedPoint.instDecidableEqFx' else r)
    def test_unproved_source_constant(self):
        def edit(r):
            if r['name']=='Solidity.Language.FixedPoint.Fx.wrapInt_inRange':r['axioms'].append('sorryAx')
            return r
        self.check_corruption(edit)
if __name__=='__main__': unittest.main()
