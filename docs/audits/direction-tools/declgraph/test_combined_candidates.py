#!/usr/bin/env python3
"""Native-key corpus deduplication and historical-unit membership fixtures."""
import copy,pathlib,runpy
M=runpy.run_path(str(pathlib.Path(__file__).with_name('combine_candidate_witnesses.py')))
def reject(fn):
 try:fn()
 except AssertionError:return
 raise AssertionError('Invalid combination accepted')
def main():
 im={};st={};a=dict(module='M',name='same printed',name_key_sha256='native-A',constant_kind='def');b=dict(a,name_key_sha256='native-B')
 M['merge_rows'](im,st,[a,b],[]);assert len(im)==2
 M['merge_rows'](im,st,[a],[]);assert len(im)==2
 s=dict(path='P.lean',name='s',name_key_sha256='native-S',own_range='[1,2]',constant_kind='theorem',seen_as_root='0',seen_as_dependency='1')
 M['merge_rows'](im,st,[],[s]);before=copy.deepcopy((im,st))
 reject(lambda:M['merge_rows'](im,st,[dict(a,name_key_sha256='fresh')],[dict(s,seen_as_dependency='0')]))
 assert (im,st)==before
 reject(lambda:M['merge_rows'](im,st,[dict(a,constant_kind='theorem')],[]));assert (im,st)==before
 key=['str','anonymous','chosen'];sha=M['M']['keyhash'](key);module='Solidity.Backend.InternalFlow.Fixture';path='Solidity/Backend/InternalFlow/Fixture.lean'
 candidates=[dict(path=path,unchanged_at_base=True,native_symbols=['chosen']),dict(path=path,unchanged_at_base=False,native_symbols=['never-looked-up'])]
 keys={(module,'chosen'):dict(name_key=key,constant_kind='def')};paths={module:path}
 wanted=dict(module=module,name='chosen',name_key_sha256=sha,constant_kind='def');other=dict(wanted,name='same-family-other',name_key_sha256='other-native-key');imports={(module,sha):wanted,(module,'other-native-key'):other}
 assert M['candidate_imports'](candidates,keys,paths,imports)==[wanted]
 assert M['candidate_imports'](candidates,keys,paths,{(module,'other-native-key'):other})==[]
 reject(lambda:M['candidate_imports'](candidates,keys,paths,{(module,sha):dict(wanted,constant_kind='theorem')}))
 reject(lambda:M['candidate_imports'](candidates,keys,paths,{(module,sha):dict(wanted,name='different-rendering')}))
 source={'Solidity/Corpus/Generated.lean':'generated','Solidity/Examples/Plain.lean':'plain'};paths={'M':'Solidity/Corpus/Generated.lean'}
 g=dict(s,path='Solidity/Corpus/Generated.lean');p=dict(s,path='Solidity/Examples/Plain.lean');pi={};ps={}
 M['merge_rows'](pi,ps,[a,a,b],[g,p]);assert M['combined_provenance'](pi,ps,paths,source)==({'generated_corpus':2},{'generated_corpus':1,'untraced':1})
 print('COMBINED_CANDIDATE_FIXTURES_PASS structural_dedup atomic_conflict exact_candidate_key drift_excluded deduplicated_provenance')
if __name__=='__main__':main()
