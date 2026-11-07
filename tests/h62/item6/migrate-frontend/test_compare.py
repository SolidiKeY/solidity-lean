"""Required threshold and incomplete-build negative controls."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('compare',ROOT/'scripts/h62/item6/migrate-frontend/compare.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)

def measurement(wall=100,rss=100):
    return {'status':'pass','targets':['A'],'settings':{'cpu':[0],'threads':1},'results':[{'module':'A','exit':0,'stop':None}],'wall_seconds':wall,'peak_group_rss_bytes_sampled':rss}

class RegressionControls(unittest.TestCase):
    def test_nonfinite_and_malformed_metrics_are_rejected(self):
        for value in ('Infinity','-Infinity','NaN','not-a-number',None,0,-1):
            for key in ('wall_seconds','peak_group_rss_bytes_sampled'):
                for side in ('old','new'):
                    old,new=measurement(),measurement(90,90)
                    (old if side=='old' else new)[key]=value
                    with self.subTest(value=value,key=key,side=side):
                        self.assertEqual(c.compare(old,new)[1],2)

    def test_duplicate_targets_are_rejected(self):
        old,new=measurement(),measurement(90)
        for x in (old,new):
            x['targets']=['A','A'];x['results']*=2
        self.assertEqual(c.compare(old,new)[1],2)

    def test_failed_short_run_cannot_claim_speedup(self):
        new=measurement(1);new['status']='failed';new['results'][0]['exit']=1
        data,code=c.compare(measurement(),new)
        self.assertEqual(code,2);self.assertIsNone(data['wall_delta_percent'])
    def test_missing_target_cannot_claim_speedup(self):
        new=measurement(1);new['results']=[]
        self.assertEqual(c.compare(measurement(),new)[1],2)
    def test_exactly_ten_percent_escalates_without_gt_stop(self):
        data,code=c.compare(measurement(),measurement(110))
        self.assertEqual(code,1);self.assertEqual(data['status'],'ESCALATE_REGRESSION')
    def test_above_ten_percent_stops(self):
        self.assertEqual(c.compare(measurement(),measurement(110.000001))[1],3)
    def test_smaller_wall_regression_still_escalates(self):
        self.assertEqual(c.compare(measurement(),measurement(100.000001))[1],1)
    def test_memory_regression_still_escalates(self):
        self.assertEqual(c.compare(measurement(),measurement(90,101))[1],1)
    def test_faster_and_smaller_pass_performance_only(self):
        self.assertEqual(c.compare(measurement(),measurement(90,90))[1],0)
    def test_changed_resource_settings_block(self):
        new=measurement(90);new['settings']['cpu']=[1]
        self.assertEqual(c.compare(measurement(),new)[1],2)
    def test_target_order_change_blocks(self):
        new=measurement(90);new['targets']=['B'];new['results'][0]['module']='B'
        self.assertEqual(c.compare(measurement(),new)[1],2)

if __name__=='__main__':unittest.main()
