"""Source-only adversarial acceptance checks; no Lean or proof claims.
Every probe runs the real acceptance CLI on an isolated minimal copy.
"""
import shutil, subprocess, sys, tempfile, unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
SCRIPT=Path('scripts/h62/item4/generic-passes')
LEAF=Path('tests/h62/item4/generic-passes')

class Acceptance(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory(prefix='h62-acceptance-')
        self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name)
        paths=[SCRIPT/'accept.py',SCRIPT/'census.py',LEAF/'Instances.lean',LEAF/'Correspondence.lean']
        paths += [Path('Solidity/Backend/Passes')/('Assignment'+name+suffix+'.lean')
                  for name in ['Addition','Subtraction','Multiplication'] for suffix in ['Pass','Controls']]
        for path in paths:
            (self.root/path).parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/path,self.root/path)
    def run_probe(self):
        return subprocess.run([sys.executable,str(self.root/SCRIPT/'accept.py'),'--lexical-only'],
            text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    def edit(self,path,old,new):
        path=self.root/path; source=path.read_text(); self.assertIn(old,source)
        path.write_text(source.replace(old,new,1))
    def test_original_is_accepted(self):
        result=self.run_probe(); self.assertEqual(result.returncode,0,result.stdout)
    def test_changed_execution_signature_is_refused(self):
        self.edit(LEAF/'Instances.lean','(fuel : Nat)','(fuel : Int)')
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_missing_negative_control_is_refused(self):
        self.edit(LEAF/'Correspondence.lean','theorem addition_short_frame_refused','theorem omitted_short_frame')
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_substituted_alias_type_is_refused(self):
        self.edit(LEAF/'Correspondence.lean',
            'type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial',
            'type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.family')
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_substituted_alias_body_is_refused(self):
        self.edit(LEAF/'Correspondence.lean',
            ':=\n  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial',
            ':=\n  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.family')
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_commented_alias_is_refused(self):
        path=self.root/LEAF/'Correspondence.lean'
        source=path.read_text()
        first=source.index('theorem addition_initial')
        last=source.index('theorem addition_input',first)
        path.write_text(source[:first]+'/- '+source[first:last]+' -/\n'+source[last:])
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_mixed_duplicate_alias_is_refused(self):
        path=self.root/LEAF/'Correspondence.lean'
        path.write_text(path.read_text()+'\ntheorem addition_initial : True := True.intro\n')
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_body_suffix_is_refused(self):
        self.edit(LEAF/'Correspondence.lean',
            ':=\n  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial',
            ':=\n  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial\n  |> fun p => p')
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_comment_masking_substitution_is_refused(self):
        path=self.root/LEAF/'Correspondence.lean'
        source=path.read_text(); first=source.index('theorem addition_initial')
        last=source.index('theorem addition_input',first)
        path.write_text(source[:first]+'/- '+source[first:last]+' -/\n'+
            'theorem addition_initial : True := True.intro\n'+source[last:])
        self.assertNotEqual(self.run_probe().returncode,0)
    def test_duplicate_alias_is_refused(self):
        path=self.root/LEAF/'Correspondence.lean'
        path.write_text(path.read_text()+\
            '\ntheorem addition_initial : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial :=\n  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial\n')
        self.assertNotEqual(self.run_probe().returncode,0)
if __name__=='__main__': unittest.main()
