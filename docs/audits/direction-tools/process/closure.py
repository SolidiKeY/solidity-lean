#!/usr/bin/env python3
"""H241 historical closure reuse; no fresh Lean run or corpus measurement.
After history.py and reuse.py, run:
 python3 docs/audits/direction-tools/process/closure.py --archive-git ARCHIVE.git --out RESULT_DIR
The archive is SolidiKeY/solidity-lean-coord. Only pinned existing blobs are read.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
sys.dont_write_bytecode=True
from history import BASE, blank_lean
from reuse import apply_gap

ARCHIVE_REVISION='a2d55ac49baddb40486aabc66b26957deb2787e4'
ARCHIVE_PREFIX='evidence/plan-e3-feature-citations-1107/e3-feature-citations/e3-feature-citations-evidence/completed-final-retry/full/'
SOURCE='b2968a3b994fa7dd4b62600e48cbb00299d1eab6'
MODULE='Solidity.Calculus.Decide'
HASHES={'HEAD':'57c0cb2624a1683c63c46277ecda14e934cfa9882c04ea9e301c4464ec86ebb7',
'gates.tsv':'abebabb44de6b61d3523dd2bf4f0b4f04dc1729a829c0f75fbfdc1921a5dc836',
'3.log':'47e81bf4dafa3e5125decafa51908ee0c0a1ca43062fcf9f10539f16679cf5be'}

def git(*args):return subprocess.check_output(['git',*args],text=True).strip()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--archive-git',type=pathlib.Path,required=True)
    ap.add_argument('--out',type=pathlib.Path,required=True)
    args=ap.parse_args();receipts={}
    for name,expected in HASHES.items():
        raw=subprocess.check_output(['git','--git-dir='+str(args.archive_git),'show',ARCHIVE_REVISION+':'+ARCHIVE_PREFIX+name])
        assert hashlib.sha256(raw).hexdigest()==expected, 'receipt bytes differ: '+name
        receipts[name]=raw.decode()
    assert receipts['HEAD'].strip()==SOURCE
    assert any(row.split('\t')[:2]==['PASS','run-lean'] and 'bash run-lean.sh' in row for row in receipts['gates.tsv'].splitlines())
    assert 'Build completed successfully' in receipts['3.log']
    assert 'Replayed '+MODULE+'\n' in receipts['3.log']
    assert 'import '+MODULE in git('show',SOURCE+':Solidity.lean').splitlines()
    assert git('rev-parse',BASE+':lean-toolchain')==git('rev-parse',SOURCE+':lean-toolchain')
    for config in ('lakefile.toml','run-lean.sh'):
        assert git('rev-parse',BASE+':'+config)==git('rev-parse',SOURCE+':'+config), 'build configuration drift: '+config
    todo=[MODULE];seen=set();external=set()
    while todo:
        module=todo.pop()
        if module in seen or module in external:continue
        path=module.replace('.','/')+'.lean'
        exists=subprocess.run(['git','cat-file','-e',BASE+':'+path],capture_output=True).returncode==0
        if not exists:
            assert module.startswith(('Lean.','Std.')), 'unresolved non-toolchain import: '+module
            external.add(module);continue
        assert git('rev-parse',BASE+':'+path)==git('rev-parse',SOURCE+':'+path), 'source drift: '+path
        seen.add(module)
        for line in blank_lean(git('show',BASE+':'+path)).splitlines():
            if line.startswith('import '):todo.extend(line.split()[1:])
    summary=json.loads((args.out/'summary.json').read_text())
    hotspots=json.loads((args.out/'hotspots.json').read_text())
    selected=next(row for row in hotspots if row['path']==MODULE.replace('.','/')+'.lean')
    assert selected['base_metrics']['sorry_admit_tokens']==selected['base_metrics']['axiom_declarations']==0
    selected['closed_goal']='closed_by_reused_successful_archived_full_gate'
    selected['kernel_closure_confirmed']=True
    closure={'status':'historical closure confirmed by reused archived validation',
      'archive_repository':'https://github.com/SolidiKeY/solidity-lean-coord',
      'archive_revision':ARCHIVE_REVISION,'archive_prefix':ARCHIVE_PREFIX,
      'source_revision':SOURCE,'audited_revision':BASE,'module':MODULE,
      'local_import_source_blobs_identical':True,'local_import_modules_verified':len(seen),
      'external_imports':sorted(external),'toolchain_blob_identical':True,'build_configuration_blobs_identical':True,
      'boundary':'Successful archived Lake full-gate replay, not a fresh kernel check. Entire local source import graph and toolchain pin match audited base; cached build provenance is inherited from the archived gate. No timing is extrapolated.'}
    selected['closure_evidence']['archived_validation']=closure
    summary['closure_reuse']=closure
    summary['methods']['closure']='Non-goal hotspots N/A. Decide historical closure supported by exact archived successful full-gate bytes, explicit replay line, root inclusion, identical local source-import graph and toolchain pin. No fresh Lean check.'
    summary['waits']=[w for w in summary['waits'] if w['item'] not in ('closed goal evidence','CI logs')]
    summary['limits']=[('No fresh Lean builds or proof timing measurements. Historical closure is reused only with exact archived receipt and source/import identity checks.' if x=='No Lean builds, no proof timings measured, no proof closure claimed.' else x) for x in summary['limits']]
    summary['conclusion']='Registries/documentation dominate churn hotspots. The sole theorem-bearing hotspot has historical closure evidence reused with an identical source/import graph. The matched process-overhead ratio and categorical verdict remain unproven/inconclusive with an UNVERIFIABLE evidence gap under H151; no full audit completion is authorized. Source volume is not labor.'
    for trend in summary['trends']:
        if trend['signal']=='top30 churn composition':
            trend['kernel_closure_confirmed']=1
            trend['source_complete_kernel_unverified_files']=[]
    summary['reference_reuse']['closure_receipt']='resolved separately by pinned archived full-gate reuse; see closure_reuse'
    apply_gap(summary)
    summary['reproduce_continuation']='Run recorded history.py command, then reuse.py --out RESULT_DIR, then closure.py --archive-git ARCHIVE.git --out RESULT_DIR'
    for name,obj in [('summary.json',summary),('hotspots.json',hotspots),('reference-reuse.json',summary['reference_reuse'])]:
        data=json.dumps(obj,indent=2,sort_keys=True)+'\n';assert len(data.encode())<1_000_000
        (args.out/name).write_text(data)
    print('H241 archive reuse PASS: historical Decide closure, exact receipt hashes and local import/toolchain identity; no fresh Lean run')

if __name__=='__main__':main()
