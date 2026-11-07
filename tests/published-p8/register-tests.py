import tempfile,subprocess,shutil,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
MODULES=['Solidity.Lowering.P8.FrozenInterface','Solidity.Lowering.P8b.Frozen','Solidity.Lowering.P8b.P8aInterface','Solidity.Source.FailureResources']
class Registration(unittest.TestCase):
 def run_case(self,source):
  with tempfile.TemporaryDirectory() as d:
   r=Path(d);(r/'scripts').mkdir();shutil.copy(ROOT/'scripts/register-published-p8.py',r/'scripts');(r/'Solidity.lean').write_text(source)
   p=subprocess.run(['python3',str(r/'scripts/register-published-p8.py')],capture_output=True,text=True)
   return p,(r/'Solidity.lean').read_text()
 def test_only_selected_duplicates(self):
  clean='\n'.join('import '+m for m in MODULES)+'\n-- keep\nimport Other.Module\nimport Other.Module\n'
  p,out=self.run_case(clean+'import '+MODULES[0]+'\nimport '+MODULES[-1]+'\n');self.assertEqual(p.returncode,0,p.stderr);self.assertEqual(out,clean)
 def test_idempotent(self):
  source='\n'.join('import '+m for m in MODULES)+'\n';p,out=self.run_case(source);self.assertEqual(p.returncode,0);self.assertEqual(out,source)
 def test_commented_import_not_seen(self):
  source='\n'.join('import '+m for m in MODULES[1:])+'\n/- /- nested -/\nimport '+MODULES[0]+'\n-/\n';p,_=self.run_case(source);self.assertNotEqual(p.returncode,0)
 def test_unknown_root_code(self):
  source='\n'.join('import '+m for m in MODULES)+'\naxiom bad : False\n';p,_=self.run_case(source);self.assertNotEqual(p.returncode,0)
if __name__=='__main__':unittest.main()
