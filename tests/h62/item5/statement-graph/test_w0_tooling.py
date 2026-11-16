"""Guard H107 import escapes, allowlist resurrection and false SIGBUS gate passes.

Disposable Git histories and mocked failing commands exercise tooling only.
No fixture elaborates Lean or substitutes for the required checkpoint gate.
"""
import json, os, subprocess, tempfile, unittest, shutil, shlex
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
HELPER=ROOT/'scripts/core-import-closure.mjs'
class WaveZeroTests(unittest.TestCase):
    def node(self,code,cwd=ROOT):
        return subprocess.run(['node','--input-type=module','-e',f"import * as c from {json.dumps(HELPER.as_uri())};\n"+code],cwd=cwd,text=True,capture_output=True)
    def test_transitive_cycle_baseline_and_multiple_new_edges(self):
        p=self.node("""import assert from 'node:assert/strict';
const g=new Map([['A',['B']],['B',['A','X','Y']],['X',['Z']],['Y',[]]]);
assert.deepEqual(c.closureViolations(g,x=>x==='A'||x==='B',new Set(['B → X'])),[['A','B','Y']]);
assert.equal(c.closureViolations(g,x=>x==='A'||x==='B',new Set()).length,2);
assert.equal(c.closureViolations(g,x=>x==='A'||x==='B',new Set(['B → X','B → Y'])).length,0);
""");self.assertEqual(p.returncode,0,p.stderr)
    def test_comments_indentation_and_multi_import(self):
        p=self.node("""import assert from 'node:assert/strict';
assert.deepEqual(c.parseImports(`-- import Solidity.Fake\n/- nested /- import Nope -/ -/\n  public import Solidity.KeySort Solidity.Tools.Escape -- x\nmeta import all Solidity.Other\n`),['Solidity.KeySort','Solidity.Tools.Escape','Solidity.Other']);
assert.throws(()=>c.parseImports(`import\n Solidity.Hidden`));
assert.throws(()=>c.parseImports('import «Hidden»'));
""");self.assertEqual(p.returncode,0,p.stderr)
    def history(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);root=Path(tmp.name);(root/'scripts').mkdir()
        self.git(root,'init','-q');self.git(root,'config','user.email','fixture@example.invalid');self.git(root,'config','user.name','fixture')
        for name in ('core-import-baseline.json','core-import-current-baseline.json'):(root/'scripts'/name).write_bytes((ROOT/'scripts'/name).read_bytes())
        # Freeze initial epochs independently of later production subset cleanup.
        (root/'scripts/core-import-allowlist.json').write_bytes((ROOT/'scripts/core-import-baseline.json').read_bytes())
        current=json.loads((ROOT/'scripts/core-import-current-baseline.json').read_text())
        (root/'scripts/core-import-additions-allowlist.json').write_text(json.dumps([[x['source'],x['target']] for x in current['additions']]))
        self.commit(root);return root
    def git(self,root,*args):return subprocess.run(['git',*args],cwd=root,check=True,capture_output=True,text=True).stdout
    def commit(self,root):self.git(root,'add','-A');self.git(root,'commit','-qm','fixture')
    def test_shrink_is_permanent_across_commits(self):
        root=self.history();p=root/'scripts/core-import-allowlist.json';original=p.read_text();rows=json.loads(original);p.write_text(json.dumps(rows[:-1]));self.commit(root)
        self.assertEqual(self.node('c.loadAllowlist();',root).returncode,0)
        p.write_text(original);self.commit(root);self.assertNotEqual(self.node('c.loadAllowlist();',root).returncode,0)
    def test_delete_recreate_cannot_resurrect(self):
        root=self.history();p=root/'scripts/core-import-allowlist.json';original=p.read_text();p.write_text(json.dumps(json.loads(original)[:-1]));self.commit(root)
        p.unlink();self.commit(root);p.write_text(original);self.commit(root)
        self.assertIn('deletion',self.node('c.loadAllowlist();',root).stderr)
    def test_merge_cannot_restore_removed_allowance(self):
        root=self.history();branch=self.git(root,'branch','--show-current').strip()
        self.git(root,'checkout','-qb','shrink');p=root/'scripts/core-import-allowlist.json';p.write_text(json.dumps(json.loads(p.read_text())[:-1]));self.commit(root)
        self.git(root,'checkout','-q',branch);self.git(root,'merge','--no-ff','-s','ours','shrink','-m','fixture')
        self.git(root,'config','log.diffMerges','first-parent')
        self.assertIn('only shrink',self.node('c.loadAllowlist();',root).stderr)
    def test_tampered_pin_or_new_allowance_refused(self):
        root=self.history();p=root/'scripts/core-import-allowlist.json';rows=json.loads(p.read_text());rows.append(['Solidity.KeySort','Solidity.NewEscape']);p.write_text(json.dumps(rows))
        self.assertNotEqual(self.node('c.loadAllowlist();',root).returncode,0)
        p.write_bytes((ROOT/'scripts/core-import-allowlist.json').read_bytes());(root/'scripts/core-import-baseline.json').write_text('[]')
        self.assertIn('SHA256 mismatch',self.node('c.loadAllowlist();',root).stderr)
    def test_new_component_is_exact_twelve_and_only_shrinks(self):
        root=self.history();self.assertEqual(self.node("if(c.loadAllowlist().size!==107)throw Error('count');",root).returncode,0)
        p=root/'scripts/core-import-additions-allowlist.json';all_=p.read_text();rows=json.loads(all_)
        p.write_text(json.dumps(rows[:-1]));self.commit(root)
        self.assertEqual(self.node("if(c.loadAllowlist().size!==106)throw Error('count');",root).returncode,0)
        p.write_text(all_);self.commit(root);self.assertIn('only shrink',self.node('c.loadAllowlist();',root).stderr)
    def test_original_debt_cannot_be_smuggled_into_additions(self):
        root=self.history();p=root/'scripts/core-import-allowlist.json';old=json.loads(p.read_text());removed=old.pop();p.write_text(json.dumps(old));self.commit(root)
        extra=root/'scripts/core-import-additions-allowlist.json';rows=json.loads(extra.read_text());rows.append(removed);extra.write_text(json.dumps(rows))
        self.assertIn('only shrink',self.node('c.loadAllowlist();',root).stderr)
        extra.write_text(json.dumps(rows[:-1]));snapshot=root/'scripts/core-import-current-baseline.json';snapshot.write_text(snapshot.read_text()+' ')
        self.assertIn('SHA256 mismatch',self.node('c.loadAllowlist();',root).stderr)
    def test_additions_deletion_cannot_reset_initial_epoch(self):
        root=self.history();p=root/'scripts/core-import-additions-allowlist.json';all_=p.read_text();p.write_text(json.dumps(json.loads(all_)[:-1]));self.commit(root)
        p.unlink();self.commit(root);p.write_text(all_);self.commit(root);self.assertIn('deletion',self.node('c.loadAllowlist();',root).stderr)
    def test_touched_merge_pregate_checks_layers_before_any_build(self):
        for bad in (False,True):
            with self.subTest(bad=bad),tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);(root/'scripts/coord-tools').mkdir(parents=True);(root/'bin').mkdir();(root/'Solidity').mkdir()
                (root/'scripts/coord-tools/gate.sh').write_bytes((ROOT/'scripts/coord-tools/gate.sh').read_bytes())
                for name in ('check-layers.mjs','import-fanout.mjs','core-import-closure.mjs','core-import-baseline.json','core-import-current-baseline.json','check-private-paths.sh','check-evidence-files.sh'):
                    (root/'scripts'/name).write_bytes((ROOT/'scripts'/name).read_bytes())
                (root/'scripts/ci').mkdir();(root/'scripts/ci/checks-fast.sh').write_text('#!/usr/bin/env bash\nexit 0\n')
                (root/'scripts/core-import-allowlist.json').write_bytes((ROOT/'scripts/core-import-baseline.json').read_bytes())
                snapshot=json.loads((ROOT/'scripts/core-import-current-baseline.json').read_text())
                (root/'scripts/core-import-additions-allowlist.json').write_text(json.dumps([[x['source'],x['target']] for x in snapshot['additions']]))
                doc='/-! Guard H107 merge pre-gate against new core import escapes. -/\n'
                for name in ('Solidity.lean','SolidityExamples.lean'):(root/name).write_text(doc)
                node=root/'bin/node';node.write_text('#!/usr/bin/env bash\necho layers >> events\nexec '+shlex.quote(shutil.which('node'))+' "$@"\n');node.chmod(0o755)
                lake=root/'bin/lake';lake.write_text('#!/usr/bin/env bash\n echo build >> events\n');lake.chmod(0o755)
                self.git(root,'init','-q');self.git(root,'config','user.email','fixture@example.invalid');self.git(root,'config','user.name','fixture');self.commit(root)
                (root/'Solidity/Theory').mkdir();(root/'Solidity/Tools').mkdir()
                (root/'Solidity/Tools/Escape.lean').write_text(doc)
                (root/'Solidity/Theory/New.lean').write_text(('import Solidity.Tools.Escape\n' if bad else '')+doc)
                env=dict(os.environ,PATH=str(root/'bin')+os.pathsep+os.environ['PATH'],GATE_BASE='HEAD',GATE_LOGS=str(root/'logs'))
                p=subprocess.run(['bash','scripts/coord-tools/gate.sh','touched'],cwd=root,env=env,text=True,capture_output=True)
                self.assertEqual(p.returncode,int(bad),p.stdout+p.stderr)
                self.assertEqual((root/'events').read_text().splitlines(),['layers'] if bad else ['layers','build'])
                self.assertIn('layers',(root/'logs/gates.tsv').read_text())
                if bad:self.assertIn('Solidity.Theory.New → Solidity.Tools.Escape',(root/'logs/1.log').read_text())
    def test_reproducer_refuses_custom_history_before_attribution(self):
        for name in ('GIT_GRAFT_FILE','GIT_SHALLOW_FILE'):
            env=dict(os.environ);env[name]='/tmp/h107-untrusted-history'
            result=subprocess.run(['node','scripts/h62/item5/statement-graph/reproduce_core_baseline.mjs'],cwd=ROOT,env=env,text=True,capture_output=True)
            self.assertEqual(result.returncode,1);self.assertEqual(result.stdout,'');self.assertIn('history refused',result.stderr)
    def retry(self,name,scenario,copy_fail=False):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);command=root/'command';command.write_text("#!/usr/bin/env bash\nn=$(cat count 2>/dev/null || echo 0); n=$((n+1)); echo $n > count\n"+scenario);command.chmod(0o755)
            source=(ROOT/'scripts/coord-tools/gate.sh').read_text();function=source[source.index('run_gate() {'):source.index('build_touched() {')]
            script='set -uo pipefail\nlogs='+str(root)+'; failed=0; index=0\n'+function
            if copy_fail:script+='cp() { return 1; }\n'
            script+=f'run_gate {name} {command}\nexit "$failed"\n'
            p=subprocess.run(['bash','-c',script],cwd=root,text=True,capture_output=True)
            return p,int((root/'count').read_text()),(root/'1.log').read_text(),(root/'gates.tsv').read_text() if (root/'gates.tsv').exists() else ''
    def test_sigbus_retries_once_and_preserves_both_attempts(self):
        p,count,log,tsv=self.retry('library','echo "Lean exited with code 135"; [ "$n" -ge 2 ]\n')
        self.assertEqual((p.returncode,count),(0,2));self.assertIn('RETRY-SIGBUS library',log);self.assertIn('PASS',tsv)
        p,count,log,tsv=self.retry('library','echo "Lean exited with code 135"; exit 1\n')
        self.assertEqual((p.returncode,count),(1,2));self.assertIn('FAIL',tsv)
        p,count,log,_=self.retry('run-lean','echo "Lean exited with code 135"; [ "$n" -ge 2 ]\n')
        self.assertEqual((p.returncode,count),(0,2));self.assertIn('RETRY-SIGBUS run-lean',log)
    def test_other_failures_success_and_nonbuild_are_unchanged(self):
        for name,body,expected in [('library','echo ordinary; exit 1',1),('library','echo "Lean exited with code 135"; exit 0',0),('trust','echo "Lean exited with code 135"; exit 1',1)]:
            p,count,log,_=self.retry(name,body);self.assertEqual((p.returncode,count),(expected,1));self.assertNotIn('RETRY-SIGBUS',log)
    def test_backup_failure_is_failure(self):
        p,count,_,_=self.retry('library','echo "Lean exited with code 135"; exit 1',True)
        self.assertEqual((p.returncode,count),(1,1));self.assertIn('log-preservation',p.stderr)
if __name__=='__main__':unittest.main()
