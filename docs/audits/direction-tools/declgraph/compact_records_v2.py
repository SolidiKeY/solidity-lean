#!/usr/bin/env python3
"""Additive decoder adapter: exact legacy measurement with identity hash memo.
Only decoder-owned JSON objects are supplied to the unchanged measure function.
Neither decoder nor measure mutates name keys. Strong references prevent id reuse;
distinct equal objects are never merged. The memo dies at each file boundary.
No new observation, liveness, necessity or peak-memory claim follows.
"""
if not __debug__: raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import pathlib,runpy,types
HERE=pathlib.Path(__file__).resolve().parent
BASE=runpy.run_path(str(HERE/'compact_records.py'))
LEGACY=BASE['LEGACY']

def cloned_measure():
 original=LEGACY['measure'];keyhash=LEGACY['keyhash'];memo={}
 def retained_hash(key):
  marker=id(key)
  if marker in memo:
   retained,digest=memo[marker];assert retained is key
   return digest
  digest=keyhash(key);memo[marker]=(key,digest)
  return digest
 globals_copy=dict(original.__globals__);globals_copy['keyhash']=retained_hash
 fn=types.FunctionType(original.__code__,globals_copy,original.__name__,original.__defaults__,original.__closure__)
 fn.__kwdefaults__=None if original.__kwdefaults__ is None else dict(original.__kwdefaults__)
 assert fn.__code__ is original.__code__ and original.__globals__['keyhash'] is keyhash
 return fn

def measure(raw,log,path):
 counts=BASE['footer'](log)
 result=cloned_measure()(raw,BASE['ProjectedFooter'](counts),path,records=BASE['expanded'](raw,counts[5]))
 return result,dict(serialized_definitions=counts[5],binding_events=counts[4])
