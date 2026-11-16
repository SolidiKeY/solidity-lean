#!/usr/bin/env python3
"""Lossless compact binding expansion and validated native-footer projection.
Definition pooling changes serialization only; provenance remains per binding.
"""
import collections,json,pathlib,re,runpy
HERE=pathlib.Path(__file__).resolve().parent
LEGACY=runpy.run_path(str(HERE/'run_snapshot_roots.py'))

def footer(log):
 matches=re.findall(r'COMPACT_ROOTS_PASS (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)',log.read_text());assert len(matches)==1
 return tuple(map(int,matches[0]))

def expanded(path,expected_definitions):
 definitions={};used=set();binding_count=0
 for line in path.open():
  r=json.loads(line);kind=r['record']
  if kind=='definition':
   assert set(r)=={'record','id','name','name_key','constant_kind','refs'}
   id=r['id'];assert isinstance(id,int) and id>=0 and id not in definitions
   assert r['name_key'] is not None and all(x['name_key'] is not None for x in r['refs'])
   definitions[id]={k:v for k,v in r.items() if k not in ('record','id')}
  elif kind=='binding_ref':
   assert set(r)=={'record','definition','command','snapshot','in_stage2','elaborating_module','imported_pointer_modules','is_root','own_range'}
   id=r['definition'];assert id in definitions,'Unknown or forward definition reference'
   used.add(id);binding_count+=1
   yield dict(definitions[id],**{k:v for k,v in r.items() if k not in ('record','definition')},record='binding')
  else:
   assert kind in {'command','check_event','root_event','snapshot_summary','missing_parent'}
   yield r
 assert len(definitions)==expected_definitions and used==set(definitions),'Unused/missing definition records'

class ProjectedFooter:
 def __init__(self,counts):self.counts=counts
 def read_text(self):return 'SNAPSHOT_ROOTS_PASS '+' '.join(map(str,self.counts[:5]))+'\n'

def measure(raw,log,path):
 counts=footer(log)
 result=LEGACY['measure'](raw,ProjectedFooter(counts),path,records=expanded(raw,counts[5]))
 return result,dict(serialized_definitions=counts[5],binding_events=counts[4])
