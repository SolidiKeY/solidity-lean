#!/usr/bin/env python3
"""Parser regression and saved census consistency checks; no Lean or census run.
Run: python3 -B docs/audits/direction-tools/reachability/test_reach.py
"""
import collections
import csv
import importlib.util
import json
from pathlib import Path
import subprocess
import unittest

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reach',HERE/'reach.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)


class Parser(unittest.TestCase):
    def test_comments_and_strings_preserve_offsets(self):
        text='/- theorem fake : True := /- nested -/ trivial -/\n"def fake := 3"\n-- def nope := 1\ndef real := 2\n'
        cleaned=r.clean(text)
        self.assertEqual(len(text),len(cleaned));self.assertEqual(text.count('\n'),cleaned.count('\n'))
        self.assertEqual([(x.group(1),x.group(2)) for x in r.DECL.finditer(cleaned)],[('def','real')])

    def test_attributes_modifiers_unicode_and_opaque(self):
        text='@[simp] theorem α : True := trivial\n@[ext]\nprivate theorem β : True := trivial\nopaque hidden : Nat\ninstance : Inhabited Nat := ⟨0⟩\n'
        found=[(m.group(1),m.group(2)) for m in r.DECL.finditer(text)]
        self.assertEqual(found[:3],[('theorem','α'),('theorem','β'),('opaque','hidden')])
        self.assertEqual(found[3][0],'instance');self.assertIsNone(found[3][1])

    def test_generated_candidates_not_confirmed(self):
        self.assertEqual(r.generated('Solidity/Source/Agreement/Example.lean','theorem t : True := trivial'),[])
        self.assertTrue(r.generated('Solidity/Corpus/Test.lean',''))
        self.assertTrue(r.generated('Solidity/X/AxiomPins.lean',''))

    def test_graph_cycle(self):
        self.assertEqual(r.closure({'a':{'b'},'b':{'a','c'}},['a']),{'a','b','c'})


class SavedOutputs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=json.loads((HERE/'reach.json').read_text());cls.summary=json.loads((HERE/'summary.json').read_text())

    def test_all_tracked_lean_files_counted(self):
        paths=subprocess.check_output(['git','-C',str(r.ROOT),'ls-files'],text=True).splitlines()
        paths=[p for p in paths if p.endswith('.lean')]
        self.assertEqual(len(paths),self.report['source_totals']['modules'])
        self.assertEqual(sum(len((r.ROOT/p).read_text().splitlines()) for p in paths),self.report['source_totals']['physical_lines'])

    def test_partitions_and_denominators(self):
        totals=self.report['source_totals']['node_totals']
        for model in ('lexical','implicit_sensitivity'):
            for key,t in totals.items():
                for metric in ('declarations','commands','source_span_lines'):
                    self.assertEqual(t.get(metric,0),sum(v.get(key,{}).get(metric,0) for v in self.report[model].values()))
                for v in self.report[model].values():
                    if key in v:
                        for metric in ('declarations','source_span_lines'):
                            self.assertAlmostEqual(v[key][metric+'_share'],v[key].get(metric,0)/t.get(metric,1))
        self.assertEqual(totals['all']['source_span_lines']+self.report['unassigned_physical_lines'],self.report['source_totals']['physical_lines'])

    def test_unreachable_csv(self):
        with (HERE/'unreachable.csv').open() as f: rows=list(csv.DictReader(f))
        self.assertEqual(sum(int(x['decls']) for x in rows),self.report['implicit_sensitivity']['neither']['all']['declarations'])
        self.assertEqual(sum(int(x['lines']) for x in rows),self.report['implicit_sensitivity']['neither']['all']['source_span_lines'])
        self.assertEqual(len(rows),len({x['module'] for x in rows}))

    def test_duplicates_and_citations(self):
        clusters=[]
        for name in self.summary['duplicate_cluster_files']:
            p=HERE/name;self.assertLess(p.stat().st_size,1_000_000);clusters.extend(json.loads(p.read_text()))
        counts=collections.Counter(c['kind'] for c in clusters)
        self.assertEqual(counts['near_file'],self.summary['duplication']['near_file_clusters'])
        self.assertEqual(counts['same_normalized_statement'],self.summary['duplication']['same_statement_clusters'])
        self.assertTrue(all(c['lines']>0 and len(c['modules'])>1 for c in clusters))
        for p in self.summary['citations']: self.assertTrue((r.ROOT/p).is_file(),p)
        self.assertEqual(len(self.summary['largest_30_clusters']),30)
        for p in HERE.glob('*.json'): self.assertLess(p.stat().st_size,1_000_000)


if __name__=='__main__': unittest.main(verbosity=2)
