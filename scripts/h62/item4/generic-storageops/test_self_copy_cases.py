#!/usr/bin/env python3
import copy
import json
import subprocess
import unittest
import self_copy_cases as m
import retained_cycle_cases as retained


class SelfCopyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source=subprocess.check_output(['git','show',m.census.BASE+':'+m.PATH],cwd=m.census.ROOT)

    def test_cases_and_execution_boundary(self):
        report=m.build(self.source);m.validate(report,self.source)
        self.assertEqual([len(r['source_plan']['result_components']) for r in report['cases']],[1,3,2])
        self.assertTrue(all(not r['counts_as_new_verified_proof'] for r in report['cases']))
        self.assertIn('not an Evm.run statement',' '.join(report['cases'][2]['source_plan']['obligations']))

    def test_drift_and_false_acceptance(self):
        for source in [self.source.replace(b'71',b'70',1),self.source.replace(b'\n',b'\r\n')]:
            with self.assertRaises(ValueError):m.build(source)
        original=m.build(self.source)
        for kind in ['case','duplicate','statement','observation','proof']:
            report=copy.deepcopy(original)
            if kind=='case':report['cases'].pop()
            elif kind=='duplicate':report['cases'].append(report['cases'][0])
            elif kind=='statement':report['cases'][0]['statement']='theorem target_self : True'
            elif kind=='observation':report['cases'][1]['source_plan']['result_components'].pop()
            else:report['cases'][0]['counts_as_new_verified_proof']=True
            with self.assertRaises(ValueError):m.validate(report,self.source)

    def test_shared_builder_preserves_retained_packet(self):
        # The refactor must preserve every already reviewed report field, including notes.
        source=subprocess.check_output(['git','show',retained.census.BASE+':'+retained.PATH],cwd=retained.census.ROOT)
        old_script=subprocess.check_output(['git','show','74d895203fe55714cca9ed84a2c9f82eb71389db:scripts/h62/item4/generic-storageops/retained_cycle_cases.py'],cwd=retained.census.ROOT)
        namespace={'__name__':'frozen_retained_packet'}
        exec(compile(old_script,'frozen_retained_packet','exec'),namespace)
        self.assertEqual(retained.build(source),namespace['build'](source))


if __name__ == '__main__':unittest.main()
