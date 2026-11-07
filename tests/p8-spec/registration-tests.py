import tempfile,shutil,subprocess,unittest
from pathlib import Path
repo=Path(__file__).resolve().parents[2]
modules=['Solidity.Lowering.P8.FrozenInterface','Solidity.Source.FailureResources','Solidity.Lowering.P8.FailureProjection','Solidity.Lowering.P8.SourceRealization']
class Registration(unittest.TestCase):
 def check(self,text,code):
  with tempfile.TemporaryDirectory() as d:
   r=Path(d);(r/'scripts').mkdir();shutil.copy(repo/'scripts/p8-spec-interface.py',r/'scripts')
   for m in modules:
    p=r/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text('')
   (r/'Solidity.lean').write_text(text)
   x=subprocess.run(['python3',str(r/'scripts/p8-spec-interface.py')],capture_output=True,text=True)
   self.assertEqual(x.returncode==0,code,x.stderr)
 def test_registered(self):self.check(''.join('import '+m+'\n' for m in modules),True)
 def test_commented_missing(self):self.check(''.join('import '+m+'\n' for m in modules[:-1])+'/-\n import '+modules[-1]+'\n-/\n',False)
 def test_nested_comment(self):self.check('/- /- nested -/\n import '+modules[0]+'\n-/\n'+''.join('import '+m+'\n' for m in modules),True)
 def test_duplicate(self):self.check(''.join('import '+m+'\n' for m in modules)+' import   '+modules[0]+' -- duplicate\n',False)
 def test_unknown(self):self.check(''.join('import '+m+'\n' for m in modules)+'axiom x : False\n',False)
if __name__=='__main__':unittest.main()
