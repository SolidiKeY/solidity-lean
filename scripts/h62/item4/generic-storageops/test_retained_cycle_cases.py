#!/usr/bin/env python3
import copy
import subprocess
import unittest
import retained_cycle_cases as m


class RetainedCaseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source=subprocess.check_output(['git','show',m.census.BASE+':'+m.PATH],cwd=m.census.ROOT)

    def test_exact_cases_and_observation_components(self):
        report=m.build(self.source);m.validate(report,self.source)
        self.assertEqual(len(report['cases']),5)
        self.assertEqual([len(r['source_plan']['result_components']) for r in report['cases']],[3,7,3,2,5])
        self.assertTrue(all(not r['counts_as_new_verified_proof'] for r in report['cases']))

    def test_source_and_case_losses_refused(self):
        for source in [self.source.replace(b'79',b'78',1),self.source.replace(b'\n',b'\r\n')]:
            with self.assertRaises(ValueError):m.build(source)
        report=m.build(self.source)
        for mutation in ['drop','duplicate','observation','statement','proof']:
            changed=copy.deepcopy(report)
            if mutation=='drop':changed['cases'].pop()
            elif mutation=='duplicate':changed['cases'].append(changed['cases'][0])
            elif mutation=='observation':changed['cases'][1]['source_plan']['result_components'].pop()
            elif mutation=='statement':changed['cases'][0]['statement']='theorem executions : True'
            else:changed['cases'][0]['counts_as_new_verified_proof']=True
            with self.assertRaises(ValueError):m.validate(changed,self.source)


if __name__ == '__main__':unittest.main()
