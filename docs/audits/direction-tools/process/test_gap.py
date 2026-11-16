#!/usr/bin/env python3
"""Regression checks for preserving unrelated evidence across reuse phases.
Run: python3 docs/audits/direction-tools/process/test_gap.py
Only frozen Git JSON is reused; no corpus measurement or Lean invocation.
"""
import copy
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
sys.dont_write_bytecode=True
from reuse import apply_gap

HERE=pathlib.Path(__file__).resolve().parent
FROZEN='f2a6810245a032fb3ef6a33268f32a8556450430'
PREFIX='docs/audits/direction-tools/process/'

class GapPreservation(unittest.TestCase):
    def test_calibration_only_changes_owned_gap_and_wait(self):
        unrelated={'subject':'unrelated evidence','status':'UNVERIFIABLE','detail':{'keep':True}}
        waits=[{'item':x,'status':'pending'} for x in ('CI logs','closed goal evidence','va3/vu1','unknown producer')]
        summary={'reference_reuse':{},'trends':[],'evidence_gaps':[copy.deepcopy(unrelated)],
                 'waits':copy.deepcopy(waits)+[{'item':'matched process-overhead calibration'}]}
        apply_gap(summary)
        self.assertEqual(summary['waits'],waits)
        self.assertIn(unrelated,summary['evidence_gaps'])
        expected=copy.deepcopy(summary);apply_gap(summary)
        self.assertEqual(summary,expected)

    def test_reuse_keeps_closure_pending_and_records_missing_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=pathlib.Path(tmp)
            raw=subprocess.check_output(['git','show',FROZEN+':'+PREFIX+'summary.json'])
            summary=json.loads(raw)
            custom={'subject':'unrelated future evidence','status':'UNVERIFIABLE'}
            summary['evidence_gaps']=[custom]
            unknown={'item':'unknown producer','status':'unresolved'}
            summary['waits'].append(unknown)
            future_reference={'item':'da-references','status':'pending a different future reference requirement'}
            summary['waits'].append(future_reference)
            (out/'summary.json').write_text(json.dumps(summary))
            cmd=[sys.executable,str(HERE/'reuse.py'),'--out',str(out)]
            subprocess.run(cmd,check=True,capture_output=True)
            after=json.loads((out/'summary.json').read_text())
            items={w['item'] for w in after['waits']}
            self.assertEqual(items,{'CI logs','closed goal evidence','unknown producer','da-references'})
            self.assertIn(custom,after['evidence_gaps'])
            self.assertIn(unknown,after['waits'])
            self.assertIn(future_reference,after['waits'])
            gaps={g['subject']:g for g in after['evidence_gaps']}
            self.assertEqual(gaps['differential/benchmark reuse evidence']['status'],'UNVERIFIABLE')
            self.assertEqual(gaps['differential/benchmark reuse evidence']['source_wait'],next(w for w in summary['waits'] if w['item']=='va3/vu1'))
            self.assertEqual(gaps['reference artifact availability']['status'],'RESOLVED_BY_REUSE')
            self.assertIn('not supplied',after['reference_reuse']['closure_receipt'])
            before={p.name:p.read_bytes() for p in out.glob('*.json')}
            subprocess.run(cmd,check=True,capture_output=True)
            self.assertEqual(before,{p.name:p.read_bytes() for p in out.glob('*.json')})
            # A failed archived-receipt validation must not mutate pending waits.
            failed=subprocess.run([sys.executable,str(HERE/'closure.py'),'--archive-git',str(out/'missing-archive.git'),'--out',str(out)],capture_output=True)
            self.assertNotEqual(failed.returncode,0)
            self.assertEqual(before,{p.name:p.read_bytes() for p in out.glob('*.json')})

if __name__=='__main__':unittest.main()
