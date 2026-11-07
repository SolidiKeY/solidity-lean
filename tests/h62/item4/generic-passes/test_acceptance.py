"""Source-only adversarial acceptance checks; no Lean or proof claims.
Every probe runs the real acceptance CLI on an isolated minimal copy.
"""
import json, os, shutil, subprocess, sys, tempfile, unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
SCRIPT=Path('scripts/h62/item4/generic-passes')
LEAF=Path('tests/h62/item4/generic-passes')

class Acceptance(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory(prefix='h62-acceptance-')
        self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name)
        paths=[SCRIPT/'accept.py',SCRIPT/'census.py',SCRIPT/'runtime_paths.py',LEAF/'Instances.lean',LEAF/'Correspondence.lean']
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
    def path_probe(self,overrides,cwd=None):
        env=os.environ.copy()
        for key in ['H62_GENERIC_PASSES_EVIDENCE','H62_GENERIC_PASSES_INPUTS']:
            env.pop(key,None)
        env.update(overrides)
        return subprocess.run([sys.executable,'-B','-c',
            'import sys;sys.path.insert(0,'+repr(str(self.root/SCRIPT))+');import json,runtime_paths as p;print(json.dumps([str(p.EVIDENCE),str(p.INPUTS)]))'],
            cwd=cwd or self.root/SCRIPT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    def test_relocated_checkout_defaults(self):
        result=self.path_probe({}); self.assertEqual(result.returncode,0,result.stdout)
        self.assertEqual(json.loads(result.stdout),[
            str(self.root.parent/'h62-generic-passes-evidence'),
            str(self.root.parent/'h62-coordinator-inputs')])
    def test_overrides_with_spaces(self):
        evidence=self.root/'review evidence'; inputs=self.root/'review inputs'
        result=self.path_probe({'H62_GENERIC_PASSES_EVIDENCE':str(evidence),
            'H62_GENERIC_PASSES_INPUTS':str(inputs)})
        self.assertEqual(result.returncode,0,result.stdout)
        self.assertEqual(json.loads(result.stdout),[str(evidence),str(inputs)])
    def test_relative_overrides_are_stable_across_working_directories(self):
        overrides={'H62_GENERIC_PASSES_EVIDENCE':'relative evidence',
                   'H62_GENERIC_PASSES_INPUTS':'relative inputs'}
        first=self.path_probe(overrides)
        second=self.path_probe(overrides,cwd=self.root)
        self.assertEqual(first.returncode,0,first.stdout)
        self.assertEqual(second.returncode,0,second.stdout)
        self.assertEqual(json.loads(first.stdout),json.loads(second.stdout))
        self.assertEqual(json.loads(first.stdout),[
            str(self.root/'relative evidence'),str(self.root/'relative inputs')])
    def test_changed_official_pin_is_refused(self):
        inputs=self.root/'pin inputs';inputs.mkdir()
        pin={'toolchain':'leanprover/lean4:v4.35.0','asset':'lean-4.35.0-linux.tar.zst',
             'url':'https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst',
             'sha256':'7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'}
        env=os.environ.copy();env['H62_GENERIC_PASSES_INPUTS']=str(inputs)
        env.pop('H62_GENERIC_PASSES_EVIDENCE',None)
        command=[sys.executable,'-B','-c','import runtime_paths as p;p.load_pin()']
        path=inputs/'toolchain-pin.json';path.write_text(json.dumps(pin))
        result=subprocess.run(command,cwd=self.root/SCRIPT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stderr)
        for field in pin:
            with self.subTest(field=field):
                changed=dict(pin);changed[field]='wrong'
                path.write_text(json.dumps(changed))
                result=subprocess.run(command,cwd=self.root/SCRIPT,env=env,capture_output=True,text=True)
                self.assertNotEqual(result.returncode,0)
                self.assertIn('mandated official v4.35.0 release',result.stderr)
    def test_empty_override_refused(self):
        for key in ['H62_GENERIC_PASSES_EVIDENCE','H62_GENERIC_PASSES_INPUTS']:
            with self.subTest(key=key):
                result=self.path_probe({key:' '})
                self.assertNotEqual(result.returncode,0)
                self.assertIn(key+' must not be empty',result.stdout)
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
