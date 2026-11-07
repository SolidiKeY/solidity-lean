"""Guard receipt substitution and collateral original-audit classification changes."""
import copy
import importlib.util
from pathlib import Path
import unittest

spec=importlib.util.spec_from_file_location('effect_accounting',Path(__file__).with_name('effect_coverage.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class EffectCoverageControls(unittest.TestCase):
    def setUp(self):
        names=[m.gate.SOURCE_PREFIX+n for n in m.gate.RULES]+[f'Other.n{i}' for i in range(782)]
        rows=[{'source_name':name,'signature_sha256':'sig'+name,'witness_status':'pending','elaborated':{'raw_type_sha256':'type'+name}} for name in names]
        rows[10]['witness_status']='joint-witness'
        self.frozen={'base':m.gate.original.BASE,'declarations':rows};self.coverage={'entries':[{'source_name':names[10],'signature_sha256':'sig'+names[10],'status':'joint-witness','proof':'retained'}]}
        self.pair={mode:{'mode':mode,'source_sha256':'same-source'} for mode in ['frozen','current']}
        self.types={mode:{'declarations':[{'source_name':name,'raw_type_sha256':'type'+name} for name in names[:10]]} for mode in ['frozen','current']}

    def test_exact_ten_changes_all_other_rows_and_entries_preserved(self):
        rows,coverage,delta=m.apply(self.frozen,self.coverage,self.pair,self.types)
        self.assertEqual(len(rows['declarations']),792);self.assertEqual(delta['changed_entries'],10)
        self.assertEqual(rows['declarations'][10:],self.frozen['declarations'][10:]);self.assertEqual(coverage['entries'][:1],self.coverage['entries'])
        self.assertEqual(delta['before_counts']['pending']-delta['after_counts']['pending'],10);self.assertFalse(delta['runtime_gate_pass']);self.assertFalse(delta['definition_equivalence_proved'])

    def test_unadmitted_receipt_refused_before_json(self):
        class Bad:
            def read_bytes(self):return b'not-json'
        for mode in ['frozen','current']:
            with self.assertRaisesRegex(ValueError,'SHA256'):m.read_receipt(Bad(),mode)

    def test_mode_or_joint_client_substitution_refused(self):
        bad=copy.deepcopy(self.pair);bad['current']['mode']='frozen'
        with self.assertRaises(ValueError):m.apply(self.frozen,self.coverage,bad,self.types)
        bad=copy.deepcopy(self.pair);bad['current']['source_sha256']='different'
        with self.assertRaises(ValueError):m.apply(self.frozen,self.coverage,bad,self.types)

    def test_missing_duplicate_and_changed_types_refused(self):
        for changed in [self.types['current']['declarations'][:-1],self.types['current']['declarations']+[self.types['current']['declarations'][0]],self.types['current']['declarations'][:-1]+[{'source_name':self.types['current']['declarations'][-1]['source_name'],'raw_type_sha256':'changed'}]]:
            bad=copy.deepcopy(self.types);bad['current']['declarations']=changed
            with self.assertRaises(ValueError):m.apply(self.frozen,self.coverage,self.pair,bad)

    def test_lost_original_duplicate_coverage_or_baseline_drift_refused(self):
        bad=copy.deepcopy(self.frozen);bad['declarations'].pop()
        with self.assertRaises(ValueError):m.apply(bad,self.coverage,self.pair,self.types)
        bad=copy.deepcopy(self.coverage);bad['entries']*=2
        with self.assertRaises(ValueError):m.apply(self.frozen,bad,self.pair,self.types)
        bad=copy.deepcopy(self.coverage);bad['entries'][0]['status']='pending'
        with self.assertRaisesRegex(ValueError,'baseline drift'):m.apply(self.frozen,bad,self.pair,self.types)


if __name__=='__main__':unittest.main()
