#!/usr/bin/env python3
"""Identity, range, drift and witness-priority fixtures for candidate joins."""
import copy,pathlib,runpy
M=runpy.run_path(str(pathlib.Path(__file__).with_name('map_snapshot_candidates.py')))
def main():
 assert M['verdict'](0,1).startswith('Only stage2')
 assert M['verdict'](1,0).startswith('Imported saved-check')
 assert M['verdict'](0,0).startswith('No historical candidate')
 path='Solidity/Yul/Views/Fixture.lean';n=['str','anonymous','target'];kh=M['keyhash'](n)
 c=dict(path=path,name='target',first_line=1,last_line=2,historical_masked_span_lines=2,physical_span_lines=2,status='native_compile_use_witness',unchanged_at_base=True,native_symbols=['target']);node=dict(selection=[0,4,0,10],range=[0,0,1,8],kind='def');key=dict(name_key=n,constant_kind='def');im=dict(module='M',name='target',name_key_sha256=kh,constant_kind='def');st=dict(path=path,name='target',name_key_sha256=kh,constant_kind='def',seen_as_dependency='1',own_range='[0,0,1,8]')
 def run(imports,stage2,candidate=c):return M['bind']([candidate],{('M','target'):node},imports,stage2,{('M','target'):key},{'M':path})[0][0]
 r=run([im],[st]);assert r['status']=='imported_snapshot_dependency_witness' and r['stage2_correspondences']==['target']
 assert run([],[st])['status']=='stage2_range_correspondence_only'
 bad=dict(st,name_key_sha256='wrong');assert run([],[bad])['status']=='no_observed_snapshot_witness'
 bad=dict(st,own_range='[1,0,1,8]');assert run([],[bad])['status']=='no_observed_snapshot_witness'
 try:run([dict(im,name_key_sha256='wrong')],[])
 except AssertionError:pass
 else:raise AssertionError('Wrong imported native identity accepted')
 drift=dict(c,unchanged_at_base=False,native_symbols=[]);assert run([],[],drift)['status']=='historical_source_drift'
 print('CANDIDATE_JOIN_FIXTURES_PASS structural_identity exact_ranges drift witness_priority')
if __name__=='__main__':main()
