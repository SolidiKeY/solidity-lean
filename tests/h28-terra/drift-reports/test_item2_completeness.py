"""Guard omitted .sol evidence, incomplete denominators and mutable-checkout leaks."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
TOOL = ROOT / 'scripts/h28-terra/drift-reports/item2_completeness.py'
SPEC = importlib.util.spec_from_file_location('item2_completeness', TOOL)
check = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(check)


def feature(name='f', evidence=None, status='partial', scope='model'):
    return dict(id=name, current=status, scope=scope, localEvidence=evidence or [])


class Completeness(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='full inventory ')
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name) / 'repo'; self.repo.mkdir()
        home = Path(self.tmp.name) / 'home'; home.mkdir()
        self.env = dict(PATH=os.environ['PATH'], HOME=str(home),
                        GIT_CONFIG_NOSYSTEM='1', GIT_AUTHOR_NAME='fixture',
                        GIT_AUTHOR_EMAIL='fixture@example.invalid',
                        GIT_COMMITTER_NAME='fixture', GIT_COMMITTER_EMAIL='fixture@example.invalid',
                        PYTHONDONTWRITEBYTECODE='1')
        self.git('init', '-q')

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], env=self.env).decode().strip()

    def write(self, name, text='fixture'):
        path = self.repo / name; path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def manifest(self, features):
        self.write(check.MANIFEST, json.dumps({'features': features}, ensure_ascii=True))

    def commit(self, features):
        self.manifest(features)
        self.git('add', '-A'); self.git('commit', '-qm', 'fixture')
        return self.git('rev-parse', 'HEAD')

    def invoke(self, base, rc=0, tool=TOOL, env=None):
        proc = subprocess.run([sys.executable, '-B', str(tool), '--repo', str(self.repo), '--base', base],
                              env=env or self.env, capture_output=True, text=True, timeout=15)
        self.assertEqual(proc.returncode, rc, proc.stderr + proc.stdout)
        if rc == 2:
            self.assertEqual(proc.stdout, '')
            return json.loads(proc.stderr)
        self.assertEqual(proc.stderr, '')
        return json.loads(proc.stdout)

    def test_existing_sol_preserves_every_status_scope_and_row(self):
        self.write('tests/A.sol'); self.write('notes.md')
        features = [feature('p', ['tests/A.sol', 'notes.md']),
                    feature('m', ['tests/A.sol'], 'missing', {'area': 'source'}),
                    feature('u', [], 'unsupported', None),
                    feature('excluded', ['not-present.sol'], 'complete')]
        base = self.commit(features); result = self.invoke(base)
        self.assertEqual([(r['id'], r['status'], r['scope']) for r in result['features']],
                         [(f['id'], f['current'], f['scope']) for f in features[:3]])
        self.assertEqual(result['counts'], dict(features=4, qualifyingFeatures=3,
                         evidenceOccurrences=3, existingOccurrences=3, missingOccurrences=0,
                         nonRegularOccurrences=0, frozenOmittedExistingOccurrences=2,
                         frozenAffectedFeatures=2))
        self.assertEqual(result['source']['trackedEntries'], 3)
        for row in result['features']:
            self.assertEqual(row['verdict'], 'owner-review-required-no-status-rewrite')
            self.assertEqual(row['missingEvidence'], [])
        entry = result['features'][0]['evidence'][0]
        self.assertTrue(entry['tracked']); self.assertEqual(entry['entry']['kind'], 'regular')
        self.assertTrue(entry['omittedByFrozenSelection'])

    def test_missing_sol_is_not_hidden_by_untracked_working_file(self):
        base = self.commit([feature(evidence=['Absent.sol'])])
        self.write('Absent.sol', 'untracked working-tree distraction')
        result = self.invoke(base, rc=1)
        self.assertEqual(result['features'][0]['missingEvidence'], ['Absent.sol'])
        self.assertEqual(result['counts']['missingOccurrences'], 1)
        self.assertIsNone(result['features'][0]['evidence'][0]['entry'])
        self.assertEqual(result['counts']['frozenOmittedExistingOccurrences'], 0)

    def test_dirty_manifest_and_deleted_working_file_do_not_change_pin(self):
        path = self.write('Present.sol'); base = self.commit([feature(evidence=['Present.sol'])])
        path.unlink(); self.manifest([feature('different', ['Missing.sol'], 'unsupported', 'other')])
        result = self.invoke(base)
        self.assertEqual(result['features'][0]['id'], 'f')
        self.assertEqual(result['features'][0]['status'], 'partial')
        self.assertEqual(result['features'][0]['missingEvidence'], [])
        self.assertEqual(result['source']['commit'], base)

    def test_duplicate_evidence_occurrences_are_preserved(self):
        self.write('Present.sol')
        refs = ['Present.sol', 'Missing.sol', 'Present.sol', 'Missing.sol']
        base = self.commit([feature(evidence=refs)])
        result = self.invoke(base, rc=1); row = result['features'][0]
        self.assertEqual([r['path'] for r in row['evidence']], refs)
        self.assertEqual([r['index'] for r in row['evidence']], list(range(4)))
        self.assertEqual(row['missingEvidence'], ['Missing.sol', 'Missing.sol'])
        self.assertEqual(row['frozenOmittedExistingEvidence'], ['Present.sol', 'Present.sol'])
        self.assertEqual(result['counts']['evidenceOccurrences'], 4)

    def test_symlink_is_not_regular_evidence_and_target_is_not_followed(self):
        target = Path(self.tmp.name) / 'outside.sol'; target.write_text('outside')
        (self.repo/'Link.sol').symlink_to(target)
        base = self.commit([feature(evidence=['Link.sol'])]); result = self.invoke(base, rc=1)
        row = result['features'][0]
        self.assertEqual(row['missingEvidence'], [])
        self.assertEqual(row['nonRegularEvidence'], ['Link.sol'])
        self.assertEqual(row['evidence'][0]['entry']['kind'], 'symlink')
        self.assertEqual(target.read_text(), 'outside')

    def test_gitlink_is_not_regular_evidence(self):
        first = self.commit([])
        self.manifest([feature(evidence=['Library.sol'])]); self.git('add', check.MANIFEST)
        self.git('update-index', '--add', '--cacheinfo', '160000,' + first + ',Library.sol')
        self.git('commit', '-qm', 'gitlink'); base = self.git('rev-parse', 'HEAD')
        result = self.invoke(base, rc=1)
        self.assertEqual(result['features'][0]['nonRegularEvidence'], ['Library.sol'])
        self.assertEqual(result['features'][0]['evidence'][0]['entry']['kind'], 'gitlink')

    def test_all_suffixes_and_nul_delimited_paths_are_counted(self):
        names = ['tests/contract θ.sol', 'odd\ttab\nname.sol', 'unused.bin', 'rules.key']
        for name in names: self.write(name)
        base = self.commit([feature(evidence=names[:2])]); result = self.invoke(base)
        self.assertEqual(result['source']['trackedEntries'], 5)
        self.assertEqual([r['path'] for r in result['features'][0]['evidence']], names[:2])
        self.assertEqual(result['counts']['frozenOmittedExistingOccurrences'], 2)

    def test_malformed_manifest_rows_and_references_refuse(self):
        valid = feature(evidence=['A.sol'])
        invalid = [None, {}, {'features': {}}, {'features': [None]},
                   {'features': [dict(valid, id='')]}, {'features': [valid, valid]},
                   {'features': [dict(valid, current=None)]},
                   {'features': [dict(valid, localEvidence='A.sol')]},
                   {'features': [dict(valid, localEvidence=[None])]}]
        for path in ('', '/A.sol', '../A.sol', 'a/../A.sol', './A.sol', 'a//A.sol', 'a/\0.sol'):
            invalid.append({'features': [dict(valid, localEvidence=[path])]})
        for manifest in invalid:
            with self.subTest(manifest=manifest), self.assertRaises(ValueError):
                check.analyze(manifest, {})
        # Nonqualifying malformed rows cannot disappear from denominator validation.
        with self.assertRaises(ValueError):
            check.analyze({'features': [dict(valid, current='complete', localEvidence='bad')]}, {})

    def test_duplicate_json_keys_refuse_without_partial_report(self):
        self.write(check.MANIFEST, '{"features": [], "features": []}')
        self.git('add', '-A'); self.git('commit', '-qm', 'duplicate keys')
        result = self.invoke(self.git('rev-parse', 'HEAD'), rc=2)
        self.assertIn('duplicate manifest JSON key', result['error'])

    def test_nonfinite_json_values_refuse_and_finite_scope_is_preserved(self):
        for number in ('NaN', 'Infinity', '-Infinity', '1e999', '-1e999'):
            with self.subTest(number=number):
                self.write(check.MANIFEST, '{"features":[{"id":"f","current":"partial",'
                           '"scope":'+number+'}]}')
                self.git('add', '-A'); self.git('commit', '-qm', 'nonfinite')
                self.assertIn('nonfinite JSON', self.invoke(self.git('rev-parse', 'HEAD'), rc=2)['error'])
        base = self.commit([feature(scope={'finite':0.125})])
        self.assertEqual(self.invoke(base)['features'][0]['scope'], {'finite':0.125})

    def test_excessive_json_nesting_refuses_without_traceback(self):
        self.write(check.MANIFEST, '{"features":[{"id":"f","current":"partial","scope":'+ '['*2000+'0'+']'*2000+'}]}')
        self.git('add', '-A'); self.git('commit', '-qm', 'nested JSON')
        result = self.invoke(self.git('rev-parse', 'HEAD'), rc=2)
        self.assertIn('recursion', result['error'].lower())

    def test_manifest_must_be_present_and_regular(self):
        self.write('seed'); self.git('add', '-A'); self.git('commit', '-qm', 'no manifest')
        self.assertIn('regular tracked blob', self.invoke(self.git('rev-parse', 'HEAD'), rc=2)['error'])
        (self.repo/'docs').mkdir(); (self.repo/check.MANIFEST).symlink_to('../seed')
        self.git('add', '-A'); self.git('commit', '-qm', 'symlink manifest')
        self.assertIn('regular tracked blob', self.invoke(self.git('rev-parse', 'HEAD'), rc=2)['error'])

    def test_base_must_be_full_commit_not_ref_or_blob(self):
        base = self.commit([])
        self.assertIn('full commit SHA', self.invoke('HEAD', rc=2)['error'])
        blob = self.git('rev-parse', base + ':' + check.MANIFEST)
        self.assertIn('commit object', self.invoke(blob, rc=2)['error'])
        self.invoke('f'*40, rc=2)

    def test_replacement_objects_and_git_environment_cannot_relabel_pin(self):
        self.write('Present.sol'); original = self.commit([feature(evidence=['Present.sol'])])
        original_tree = self.git('rev-parse', original + '^{tree}')
        replacement = self.commit([feature('replacement', ['Missing.sol'])])
        self.git('replace', original, replacement)
        env = dict(self.env, GIT_DIR=str(Path(self.tmp.name)/'not-a-repo'),
                   GIT_WORK_TREE=str(Path(self.tmp.name)/'not-a-worktree'))
        result = self.invoke(original, env=env)
        self.assertEqual(result['features'][0]['id'], 'f')
        self.assertEqual(result['source']['tree'], original_tree)
        self.assertEqual(result['counts']['missingOccurrences'], 0)

    def test_changed_frozen_contract_requires_explicit_review(self):
        base = self.commit([])
        script = self.repo/'scripts/h28-terra/drift-reports/item2_completeness.py'
        script.parent.mkdir(parents=True); shutil.copyfile(TOOL, script)
        frozen = self.repo/'tests/h28-terra/drift-reports/accept.py'
        frozen.parent.mkdir(parents=True); frozen.write_bytes(check.FROZEN_ACCEPTANCE.read_bytes()+b'\n# changed\n')
        self.assertIn('frozen acceptance changed', self.invoke(base, rc=2, tool=script)['error'])

    def test_inventory_rejects_duplicate_truncated_or_unsupported_records(self):
        record = b'100644 blob ' + b'a'*40 + b'\tA.sol\0'
        for raw in (record+record, record[:-1], record.replace(b'100644', b'040000')):
            with self.subTest(raw=raw), self.assertRaises(ValueError): check.inventory(raw)

    def test_output_is_byte_deterministic(self):
        self.write('A.sol'); base = self.commit([feature(evidence=['A.sol'])])
        cmd = [sys.executable, '-B', str(TOOL), '--repo', str(self.repo), '--base', base]
        first = subprocess.check_output(cmd, env=self.env)
        second = subprocess.check_output(cmd, env=self.env)
        self.assertEqual(first, second)

    def test_complete_original_pinned_inventory_and_all_feature_occurrences(self):
        result = check.collect(ROOT, check.PINNED_BASE)
        manifest_bytes = subprocess.check_output(['git', '--no-replace-objects', 'show',
                                                 check.PINNED_BASE + ':' + check.MANIFEST], cwd=ROOT)
        manifest = json.loads(manifest_bytes)
        expected_features = [f for f in manifest['features'] if f['current'] in ('partial','missing','unsupported')]
        raw_inventory = subprocess.check_output(['git', '--no-replace-objects', 'ls-tree',
                                                 '-rz', '--full-tree', check.PINNED_BASE], cwd=ROOT)
        formatted = subprocess.check_output(['git', '--no-replace-objects', 'ls-tree', '-rz',
                    '--full-tree', '--format=%(path)%x00%(objectmode)%x00%(objecttype)%x00%(objectname)',
                    check.PINNED_BASE], cwd=ROOT)
        fields = formatted.decode('utf-8', errors='surrogateescape').split('\0')
        self.assertEqual(fields.pop(), '')
        self.assertEqual(len(fields) % 4, 0)
        independent_entries = {fields[i]: (fields[i+1], fields[i+2], fields[i+3])
                               for i in range(0,len(fields),4)}
        self.assertEqual(len(independent_entries),len(fields)//4)
        self.assertEqual(result['source']['trackedEntries'],len(independent_entries))
        self.assertEqual(result['source']['inventorySha256'],hashlib.sha256(raw_inventory).hexdigest())
        self.assertEqual(result['source']['manifestObject'], independent_entries[check.MANIFEST][2])

        self.assertEqual(result['source']['tree'], check.PINNED_TREE)
        self.assertEqual(result['source']['manifestSha256'], '55fafa3420e4548c8161ef72dc423f9db2f041e4d8b929c04b3606d9637ab716')
        self.assertEqual(result['source']['trackedEntries'], 6419)
        self.assertEqual(result['counts'], dict(features=212, qualifyingFeatures=162,
                         evidenceOccurrences=430, existingOccurrences=430, missingOccurrences=0,
                         nonRegularOccurrences=0, frozenOmittedExistingOccurrences=13,
                         frozenAffectedFeatures=13))
        self.assertEqual(len(result['features']), len(expected_features))
        for row, original in zip(result['features'], expected_features):
            self.assertEqual((row['id'],row['status'],row['scope']),
                             (original['id'],original['current'],original.get('scope')))
            self.assertEqual([r['path'] for r in row['evidence']], original.get('localEvidence', []))
            self.assertTrue(all(r['tracked'] and r['entry']['kind']=='regular' for r in row['evidence']))
            for i, reference in enumerate(row['evidence']):
                mode, kind, oid = independent_entries[reference['path']]
                self.assertEqual(kind,'blob')
                self.assertEqual(reference['index'],i)
                self.assertEqual(reference['entry'], {'kind':'regular','mode':mode,'object':oid})

        expected = {'identifiers':'Shadowing', 'overrideDeclarations':'EntryPointsLeft',
                    'functions':'DeclarationMetadata', 'receiveFunction':'EntryPointsLeft',
                    'fallbackFunction':'EntryPointsLeft', 'publicGetters':'EntryPointsLeft',
                    'blocks':'Shadowing', 'whileStatement':'QuantifiedDiamond',
                    'forStatement':'QuantifiedDiamond', 'functionSelector':'DeclarationMetadata',
                    'functionAddress':'DeclarationMetadata', 'panicCodes':'SelfPowerData',
                    'revertPayloads':'SelfPowerData'}
        omitted = {r['id']: r['frozenOmittedExistingEvidence'] for r in result['features']
                   if r['frozenOmittedExistingEvidence']}
        self.assertEqual(omitted, {key:['tests/solc/'+name+'.sol'] for key,name in expected.items()})
        self.assertEqual(len({p for paths in omitted.values() for p in paths}), 5)
        omitted_paths = {path for paths in omitted.values() for path in paths}
        for row in result['features']:
            for reference in row['evidence']:
                self.assertEqual(reference['omittedByFrozenSelection'], reference['path'] in omitted_paths)



if __name__ == '__main__':
    unittest.main(verbosity=2)
