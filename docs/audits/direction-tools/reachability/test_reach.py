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
import tarfile
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


class CalibrationParser(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec=importlib.util.spec_from_file_location('calibrate',HERE/'calibrate.py')
        cls.c=importlib.util.module_from_spec(spec);spec.loader.exec_module(cls.c)

    def test_proof_local_ltac_does_not_disconnect_pipeline(self):
        text='Lemma compiler : True.\nProof.\nLtac destruct_m := idtac.\n apply pipeline_preservation.\nQed.\nDefinition after := 0.\n'
        spans=self.c.coq_spans(text)
        self.assertEqual([m.group(2) for m,end in spans],['compiler','after'])
        match,end=spans[0]
        self.assertIn('pipeline_preservation',text[match.start():end])
        self.assertIn('Qed.',text[match.start():end])

    def test_coq_comments_and_template_declarations(self):
        text='(* Lemma fake : True. (* nested *) *)\nNondetfunction select (x: expr) := x.\n'
        cleaned=self.c.coq_clean(text)
        self.assertEqual(len(cleaned),len(text))
        self.assertEqual([(m.group(1),m.group(2)) for m,end in self.c.coq_spans(cleaned)],[('Nondetfunction','select')])


class SavedOutputs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=json.loads((HERE/'reach.json').read_text());cls.summary=json.loads((HERE/'summary.json').read_text())

    def test_pinned_lean_snapshot_counted(self):
        # Integration can add/change Lean modules after this frozen audit.
        # Read the exact report base, not the caller's index or working tree.
        proc=subprocess.Popen(['git','-C',str(r.ROOT),'archive',self.report['base'],'--','*.lean'],stdout=subprocess.PIPE)
        count=lines=0
        with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:
            for member in archive:
                if member.isfile() and member.name.endswith('.lean'):
                    count+=1
                    lines+=len(archive.extractfile(member).read().decode().splitlines())
        proc.stdout.close();self.assertEqual(proc.wait(),0)
        self.assertEqual(count,self.report['source_totals']['modules'])
        self.assertEqual(lines,self.report['source_totals']['physical_lines'])

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
        self.assertNotIn(b'\r', (HERE/'unreachable.csv').read_bytes())
        with (HERE/'unreachable.csv').open() as f: rows=list(csv.DictReader(f))
        self.assertEqual(sum(int(x['decls']) for x in rows),self.report['implicit_sensitivity']['neither']['all']['declarations'])
        self.assertEqual(sum(int(x['lines']) for x in rows),self.report['implicit_sensitivity']['neither']['all']['source_span_lines'])
        self.assertEqual(len(rows),len({x['module'] for x in rows}))

    def test_calibration_accounting(self):
        data=json.loads((HERE/'calibration.json').read_text())
        self.assertEqual(data['solidity_base'],self.report['base'])
        for field,lean_key in [('ratios','solidity_core'),('headline_sensitivity_ratios','solidity_headline_sensitivity')]:
            for row in data[field]:
                section,metric=row['metric'].split('.')
                a=data[lean_key][section][metric];b=data['compcert_program'][section][metric]
                self.assertEqual((row['solidity'],row['compcert']),(a,b))
                self.assertAlmostEqual(row['solidity_over_compcert'],a/b)
                self.assertEqual(row['outlier_over_3x_either_way'],a/b>3 or a/b<1/3)
        for key in ('solidity_core','solidity_headline_sensitivity','compcert_program','compcert_semantic_companion'):
            lexical=data[key]['lexical'];imports=data[key]['import_slice']
            self.assertEqual(lexical['declarations'],lexical['marked_generated_declarations']+lexical['handwritten_or_unmarked_declarations'])
            self.assertEqual(imports['physical_lines'],imports['marked_generated_physical_lines']+imports['handwritten_or_unmarked_physical_lines'])
            self.assertEqual(imports['physical_lines'],imports['vendored_physical_lines']+imports['own_physical_lines'])
            self.assertGreaterEqual(data[key]['within_import_slice_declaration_share'],0)
            self.assertLessEqual(data[key]['within_import_slice_declaration_share'],1)
        self.assertTrue(data['reference']['template_generator']['build_prerequisite_link_verified'])
        self.assertTrue(all(p.endswith('.vp') for p in data['reference']['template_inputs']))
        self.assertEqual(self.summary['reference_class']['ratios'],data['ratios'])

    def test_duplicates_and_citations(self):
        clusters=[]
        for name in self.summary['duplicate_cluster_files']:
            p=HERE/name;self.assertLess(p.stat().st_size,1_000_000);clusters.extend(json.loads(p.read_text()))
        counts=collections.Counter(c['kind'] for c in clusters)
        self.assertEqual(counts['near_file'],self.summary['duplication']['near_file_clusters'])
        self.assertEqual(counts['same_normalized_statement'],self.summary['duplication']['same_statement_clusters'])
        self.assertTrue(all(c['lines']>0 and len(c['modules'])>1 for c in clusters))
        for p in self.summary['citations']:
            if p.startswith('docs/audits/direction-tools/reachability/'):
                self.assertTrue((r.ROOT/p).is_file(),p)
            else:
                r.git('cat-file','-e',self.report['base']+':'+p)
        self.assertEqual(len(self.summary['largest_30_clusters']),30)
        for p in HERE.glob('*.json'): self.assertLess(p.stat().st_size,1_000_000)


if __name__=='__main__': unittest.main(verbosity=2)
