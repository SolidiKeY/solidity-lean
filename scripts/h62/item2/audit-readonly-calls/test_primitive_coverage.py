"""Guard dropped original rows, swapped proof modes, and unexecuted coverage credit."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
spec=importlib.util.spec_from_file_location('primitive_coverage',Path(__file__).with_name('primitive_coverage.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class CoverageControls(unittest.TestCase):
    def setUp(self):
        self.rows=m.gate.current.original.load_pinned(Path('/workspace/h62-audit-readonly-calls/effect-rules/accepted/census-updated.json'),m.CANONICAL_SHA)
        self.coverage=json.loads(subprocess.check_output(['git','show',m.COVERAGE_BASE+':'+m.COVERAGE_PATH],cwd=m.gate.ROOT))
        self.pair={mode:{'mode':mode,'source_sha256':'same'} for mode in ['frozen','current']}
        self.types={mode:{'declarations':[{'source_name':r['source_name'],'raw_type_sha256':r['elaborated']['raw_type_sha256']} for r in self.rows['declarations'] if r['source_name'] in m.gate.INTERFACES]} for mode in self.pair}

    def test_exact_eight_changes_preserve_every_other_original_and_entry(self):
        rows,coverage,delta=m.apply(self.rows,self.coverage,self.pair,self.types)
        self.assertEqual(delta['changed_entries'],8);self.assertEqual(len(rows['declarations']),792)
        self.assertEqual(coverage['entries'][:-8],self.coverage['entries'])
        for old,new in zip(self.rows['declarations'],rows['declarations'],strict=True):
            if old['source_name'] not in m.gate.INTERFACES:self.assertEqual(old,new)
        self.assertEqual(delta['after_counts']['pending'],433)

    def test_missing_duplicate_or_changed_type_rejected(self):
        for kind in ['missing','duplicate','changed']:
            types=copy.deepcopy(self.types);rs=types['frozen']['declarations']
            if kind=='missing':rs.pop()
            if kind=='duplicate':rs.append(rs[0])
            if kind=='changed':rs[0]['raw_type_sha256']='wrong'
            with self.assertRaises(ValueError):m.apply(self.rows,self.coverage,self.pair,types)

    def test_mismatched_client_mode_and_baseline_rejected(self):
        for key in ['mode','source_sha256']:
            pair=copy.deepcopy(self.pair);pair['current'][key]='wrong'
            with self.assertRaises(ValueError):m.apply(self.rows,self.coverage,pair,self.types)
        lost=copy.deepcopy(self.rows);lost['declarations'].pop()
        with self.assertRaises(ValueError):m.apply(lost,self.coverage,self.pair,self.types)
        bad=copy.deepcopy(self.coverage);bad['entries'][0]['status']='pending'
        with self.assertRaises(ValueError):m.apply(self.rows,bad,self.pair,self.types)

    def test_receipt_digest_before_parsing(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'receipt.json';p.write_text('not JSON')
            with self.assertRaises(ValueError):m.read_receipt(p,'frozen')

if __name__=='__main__':unittest.main()
