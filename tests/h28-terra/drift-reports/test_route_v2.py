"""Guard last-row owner loss and missed metadata conflicts in opt-in routing v2.

Reuse the frozen v1 lexical cases and full pinned corpus without editing v1.
Every invocation also checks a conflicting inventory against a literal oracle.
"""
import hashlib
import json
import subprocess
import sys
import unittest

import test_route as legacy

ROOT, OWNERS, literal_token = legacy.ROOT, legacy.OWNERS, legacy.literal_token

TOOL = ROOT / 'scripts/h28-terra/drift-reports/route_v2.py'
LEGACY = ROOT / 'scripts/h28-terra/drift-reports/route.py'


def oracle(files, owners):
    output = []
    for file in sorted(files, key=lambda row: row['path']):
        if not file['path'].endswith('.lean'):
            continue
        text = file['path'] + '\n' + file['text']
        matches = sorted({row['id'] for row in owners if literal_token(text, row['id'])})
        hints = [row for key in matches for row in owners if row['id'] == key]
        conflicts = []
        for key in matches:
            records = [json.dumps(row, sort_keys=True) for row in owners if row['id'] == key]
            if len(set(records)) > 1:
                conflicts.append(key)
        result = {'path': file['path'], 'ownerHints': hints,
                  'verdict': 'lexical-conflict-owner-review-required' if conflicts else
                  'lexical-hint-owner-review-required' if matches else 'unassigned-owner-review-required'}
        if conflicts:
            result['conflictingIds'] = conflicts
        output.append(result)
    return output


class RoutingV2(legacy.Routing):
    def run_v2(self, files, owners):
        proc = subprocess.run([sys.executable, '-B', str(TOOL)],
                              input=json.dumps({'files': files, 'ownership': owners}),
                              capture_output=True, text=True, timeout=30)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(proc.stderr, '')
        return json.loads(proc.stdout)

    def invoke(self, files, owners=OWNERS):
        actual = self.run_v2(files, owners)
        self.assertEqual(actual, oracle(files, owners))
        # Exercise all corpus files with earlier, identical and conflicting rows.
        expanded = list(owners) + list(owners) + [dict(row, conflictMarker=True) for row in owners]
        self.assertEqual(self.run_v2(files, expanded), oracle(files, expanded))
        return actual

    def test_conflicting_records_preserve_all_rows_and_order(self):
        owners = [{'id':'P1','owner':'first','metadata':{'n':[1]}},
                  {'id':'V07','owner':'other'}, {'id':'P1','owner':'last'},
                  {'id':'P1','owner':'first','metadata':{'n':[1]}}]
        self.assertEqual(self.invoke([{'path':'A.lean','text':'V07 P1 P1'}], owners), [{
            'path':'A.lean', 'ownerHints':[owners[0],owners[2],owners[3],owners[1]],
            'verdict':'lexical-conflict-owner-review-required', 'conflictingIds':['P1']}])

    def test_identical_records_keep_multiplicity_without_conflict(self):
        owners = [{'id':'P1','owner':'a','metadata':{'a':1,'b':2}},
                  {'owner':'a','metadata':{'b':2,'a':1},'id':'P1'}]
        self.assertEqual(self.invoke([{'path':'A.lean','text':'P1'}], owners), [{
            'path':'A.lean','ownerHints':owners,'verdict':'lexical-hint-owner-review-required'}])

    def test_metadata_and_json_types_are_not_silently_conflated(self):
        for first, second in [(True,1), (False,0), (1,1.0), ('1',1), ([1],[2]), (None,{})]:
            owners = [{'id':'P1','owner':'same','metadata':first},
                      {'id':'P1','owner':'same','metadata':second}]
            self.assertEqual(self.invoke([{'path':'A.lean','text':'P1'}], owners)[0]['conflictingIds'], ['P1'])

    def test_unmatched_conflict_does_not_assign_unrelated_files(self):
        owners = [{'id':'P1','owner':'a'}, {'id':'P1','owner':'b'}]
        self.assertEqual(self.invoke([{'path':'A.lean','text':'P10 P1-tail'}], owners), [{
            'path':'A.lean','ownerHints':[],'verdict':'unassigned-owner-review-required'}])

    def test_multiple_conflicts_sorted_and_duplicate_files_retained(self):
        owners = [{'id':key,'owner':owner} for key in ['V07','P1'] for owner in ['a','b']]
        rows = self.invoke([{'path':'A.lean','text':'V07 P1'}, {'path':'A.lean','text':'P1'}], owners)
        self.assertEqual([row['conflictingIds'] for row in rows], [['P1','V07'],['P1']])
        self.assertEqual([len(row['ownerHints']) for row in rows], [4,2])

    def test_raw_json_numeric_metadata_is_lossless_and_conflicts(self):
        for first, second in [('9007199254740992.0', '9007199254740993.0'),
                              ('1e999', '2e999'), ('1e-999', '2e-999'),
                              ('123456789012345678901234567890', '123456789012345678901234567891'),
                              ('1', '1.0'), ('-0', '0')]:
            payload = ('{"ownership":[{"id":"P1","owner":"a","n":' + first +
                       '},{"id":"P1","owner":"a","n":' + second +
                       '}],"files":[{"path":"A.lean","text":"P1"}]}')
            proc = subprocess.run([sys.executable, '-B', str(TOOL)], input=payload,
                                  text=True, capture_output=True, timeout=30)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            # Inspect exact tokens, not floats decoded by the test process.
            self.assertIn('"n": ' + first + '}', proc.stdout)
            self.assertIn('"n": ' + second + '}', proc.stdout)
            self.assertEqual(json.loads(proc.stdout)[0]['conflictingIds'], ['P1'])
        for invalid in ['NaN', 'Infinity', '-Infinity']:
            proc = subprocess.run([sys.executable, '-B', str(TOOL)],
                                  input='{"ownership":[{"id":"P1","n":' + invalid + '}],"files":[]}',
                                  text=True, capture_output=True, timeout=30)
            self.assertNotEqual(proc.returncode, 0)
            self.assertEqual(proc.stdout, '')

    def test_numeric_routing_fields_are_not_string_tokens(self):
        payloads = [
            '{"ownership":[{"id":1},{"id":"1"}],"files":[{"path":"A.lean","text":"1"}]}',
            '{"ownership":[],"files":[{"path":1,"text":"P1"}]}',
            '{"ownership":[],"files":[{"path":"A.lean","text":1}]}']
        for payload in payloads:
            proc = subprocess.run([sys.executable, '-B', str(TOOL)], input=payload,
                                  text=True, capture_output=True, timeout=30)
            self.assertNotEqual(proc.returncode, 0)
            self.assertEqual(proc.stdout, '')

    def test_unique_id_numeric_migration_retains_exact_tokens(self):
        payload = '{"ownership":[{"id":"P1","n":9007199254740993.0,"z":-0,"e":1e2}],"files":[{"path":"A.lean","text":"P1"}]}'
        current = subprocess.check_output([sys.executable, '-B', str(TOOL)], input=payload.encode()).decode()
        self.assertIn('"n": 9007199254740993.0', current)
        self.assertIn('"z": -0', current)
        self.assertIn('"e": 1e2', current)
        self.assertNotIn('conflictingIds', current)
        old = subprocess.check_output([sys.executable, '-B', str(LEGACY)], input=payload.encode()).decode()
        self.assertNotEqual(current, old)
        self.assertIn('9007199254740992.0', old)

    def test_migration_is_explicit_and_legacy_bytes_remain_frozen(self):
        self.assertEqual(hashlib.sha256(LEGACY.read_bytes()).hexdigest(),
                         'f46f0229988885ffd21047a42ca9ae93727ae4af9bad225b63c71aaa76278f27')
        files = [{'path':'A.lean','text':'P1'}]
        owners = [{'id':'P1','owner':'earlier'},{'id':'P1','owner':'later'}]
        payload = json.dumps({'files':files,'ownership':owners}).encode()
        old = json.loads(subprocess.check_output([sys.executable,'-B',str(LEGACY)],input=payload))
        self.assertEqual(old[0]['ownerHints'], [owners[-1]])
        self.assertEqual(self.invoke(files,owners)[0]['ownerHints'], owners)
        command = [sys.executable,'-B',str(TOOL)]
        self.assertEqual(subprocess.check_output(command,input=payload), subprocess.check_output(command,input=payload))
        unique = json.dumps({'files':files,'ownership':OWNERS}).encode()
        self.assertEqual(subprocess.check_output(command,input=unique),
                         subprocess.check_output([sys.executable,'-B',str(LEGACY)],input=unique))


if __name__ == '__main__':
    unittest.main(verbosity=2)
