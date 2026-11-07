"""Schema controls only: synthetic inputs are not Lean proof evidence."""
import copy,json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
SEAL=ROOT/'scripts/h62/item6/migrate-evm/seal-api.py'
A='Solidity.Evm.A'; B='Solidity.Evm.B'
ROW={'kind':'theorem','level_params':[],'module':A,'name':A+'.x','type_graph':{'nodes':[['sort','Lean.Level.zero']], 'root':0}}
class SealTests(unittest.TestCase):
    def call(self,rows):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp); raw=p/'input.jsonl'; census=p/'census.json'; out=p/'sealed.json'
            raw.write_text(''.join(json.dumps(x)+'\n' for x in rows))
            census.write_text(json.dumps({'modules':{m:{'assigned':True,'sha256':'0'*64} for m in [A,B]}}))
            result=subprocess.run([sys.executable,str(SEAL),str(raw),str(census),str(out)],text=True,capture_output=True)
            return result.returncode,json.loads(out.read_text()) if out.exists() else None
    def inputs(self):
        b=copy.deepcopy(ROW);b.update(module=B,name=B+'.x');return [copy.deepcopy(ROW),b]
    def test_complete_schema(self):
        code,m=self.call(self.inputs());self.assertEqual(code,0);self.assertEqual(m['assigned_modules'],2);self.assertEqual(m['declarations'],2)
    def test_empty_and_missing_coverage(self):
        for rows in [[],[ROW]]:self.assertNotEqual(self.call(rows)[0],0)
    def test_boolean_is_not_natural(self):
        rows=self.inputs();rows[0]['type_graph']={'nodes':[['bvar',True]],'root':0};self.assertNotEqual(self.call(rows)[0],0)
    def test_forward_edge(self):
        rows=self.inputs();rows[0]['type_graph']={'nodes':[['app',0,0]],'root':0};self.assertNotEqual(self.call(rows)[0],0)
    def test_unreachable(self):
        rows=self.inputs();rows[0]['type_graph']['nodes'].append(['lit','unused']);self.assertNotEqual(self.call(rows)[0],0)
    def test_duplicate_constant(self):
        self.assertNotEqual(self.call([ROW,ROW])[0],0)
    def test_duplicate_node(self):
        rows=self.inputs();rows[0]['type_graph']={'nodes':[['sort','u'],['sort','u'],['app',0,1]],'root':2};self.assertNotEqual(self.call(rows)[0],0)
    def test_unsorted(self):
        self.assertNotEqual(self.call(self.inputs()[::-1])[0],0)
if __name__=='__main__':unittest.main()
