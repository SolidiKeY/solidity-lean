#!/usr/bin/env python3
"""H241: reuse merged reference results, without fresh corpus/Lean measurement.
Run after history.py: python3 docs/audits/direction-tools/process/reuse.py --out RESULT_DIR
Reads pinned committed reference artifacts. Adds reference-reuse.json and the
same reference_reuse field to summary.json; repeat runs are idempotent.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess

REFERENCE_REVISION = '645f10caf083550552616229654e29fddd1ad767'
REFERENCE_DIRECTORY = 'docs/audits/direction-tools/references/'

def apply_gap(summary):
    """H151 disposition supplied by coordinator; not a new artifact search."""
    gap={
      'status':'UNVERIFIABLE',
      'subject':'matched process-overhead calibration',
      'authority':'H151 disposition of H241 existing-data lookup',
      'coordinator_state_receipt':'coordinator-20261108T165207Z/receipt.json',
      'receipt_boundary':'Coordinator supplied this pointer and disposition; receipt bytes/hash were not supplied in this VM.',
      'lookup_boundary':'No matching artifact located in relevant process/reference handoffs, recorded reference reuse or bounded archive filename search. This does not prove no artifact exists elsewhere.',
      'matched_ratio':None,'categorical_verdict':None,
      'claim_status':'unproven/inconclusive',
      'fresh_measurement_authorized':False,'full_audit_completion_authorized':False,
      'new_task_or_producer_interface_authorized':False
    }
    summary['evidence_gaps']=[gap]
    summary['status']='partial'
    summary['waits']=[]
    summary['matched_process_overhead_ratio']=None
    summary['matched_process_overhead_verdict']=None
    summary['reference_reuse']['process_overhead_calibration']='UNVERIFIABLE evidence gap under H151; no matched overhead numerator located in the bounded existing-data lookup'
    summary['reference_reuse']['status']='UNVERIFIABLE calibration evidence; audit incomplete, not waiting for an unchanged artifact'
    summary['reference_reuse']['evidence_gap']=gap
    for trend in summary['trends']:
        if trend['signal']=='CompCert infrastructure/source calibration':
            trend['matched_ratio']=None
            trend['verdict']=None
            trend['assessment']='UNVERIFIABLE under H151; matched ratio and justified/redundant/wrong-direction claim remain unproven/inconclusive. Existing exploratory ratios are not matched calibration.'


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=pathlib.Path,required=True)
    args=ap.parse_args()
    inputs={}
    values={}
    for name in ('inventory.json','summary.json','boundaries.json','pins.json'):
        path=REFERENCE_DIRECTORY+name
        raw=subprocess.check_output(['git','show',REFERENCE_REVISION+':'+path])
        inputs[name]={'revision':REFERENCE_REVISION,'path':path,'sha256':hashlib.sha256(raw).hexdigest()}
        values[name]=json.loads(raw)
    compcert=next(row for row in values['inventory.json'] if row['project']=='CompCert')
    summary=json.loads((args.out/'summary.json').read_text())
    measured_ref=summary['reference']
    assert measured_ref['revision']==compcert['commit']==values['pins.json']['CompCert'], 'reference pin drift'
    result={
      'decision':'H241 option A: existing archived receipts and matched calibration only; no new measurement',
      'source_inputs':inputs,
      'source_status':values['summary.json']['status'],
      'compcert_inventory_reused':compcert,
      'comparison_boundary':'Reference inventory includes multiple source languages and uses a different lexical proof-region classifier. Its line total must not replace the process audit .v denominator or turn a partial size calibration into a matched process-overhead verdict.',
      'reference_waits_reused':values['summary.json']['waits'],
      'missing_counterparts_reused':values['boundaries.json']['missing_counterparts'],
      'process_overhead_calibration':'not supplied by these merged artifacts; no overhead numerator in reference inventory',
      'closure_receipt':'not supplied by merged reference artifacts; no kernel claim inferred from source metrics or integration acknowledgement',
      'status':'blocked pending exact archived successful closure receipt and matched process calibration'
    }
    summary['reference_reuse']=result
    apply_gap(summary)
    summary['reproduce_continuation']='Run recorded history.py command, then python3 docs/audits/direction-tools/process/reuse.py --out RESULT_DIR'
    for name,data in [('reference-reuse.json',result),('summary.json',summary)]:
        raw=json.dumps(data,indent=2,sort_keys=True)+'\n'
        assert len(raw.encode())<1_000_000
        (args.out/name).write_text(raw)
    print('H241 reuse: exact reference pin match; source status '+result['source_status']+' preserved; missing process overhead/closure evidence explicit; no new measurement')

if __name__=='__main__':main()
