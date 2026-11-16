#!/usr/bin/env python3
"""Compare a saved dense capture with losslessly expanded compact records."""
import argparse,collections,json,pathlib,runpy
HERE=pathlib.Path(__file__).resolve().parent;C=runpy.run_path(str(HERE/'compact_records.py'));L=runpy.run_path(str(HERE/'run_snapshot_roots.py'))
def canonical(rows):return collections.Counter(json.dumps(r,sort_keys=True,separators=(',',':')) for r in rows)
def main():
 p=argparse.ArgumentParser();p.add_argument('--dense',type=pathlib.Path,required=True);p.add_argument('--dense-log',type=pathlib.Path,required=True);p.add_argument('--compact',type=pathlib.Path,required=True);p.add_argument('--compact-log',type=pathlib.Path,required=True);p.add_argument('--source',required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 counts=C['footer'](a.compact_log);expected=canonical(json.loads(line) for line in a.dense.open());actual=canonical(C['expanded'](a.compact,counts[5]));assert expected==actual,'Expanded records differ'
 del expected,actual
 old=L['measure'](a.dense,a.dense_log,a.source);new,encoding=C['measure'](a.compact,a.compact_log,a.source);assert old==new,'Measurements differ'
 data=dict(source=a.source,expanded_records_equal=True,measurements_equal=True,encoding=encoding,metrics=new[0],boundary='This compares two observations of one source. Equality preserves observations; it does not add semantic roots or certify full dependency coverage.')
 body=json.dumps(data,sort_keys=True,indent=2)+'\n';assert len(body.encode())<1000000
 if a.check:assert a.out.read_text()==body
 else:a.out.write_text(body)
 print('COMPACT_DENSE_EQUIVALENCE_PASS',counts[4],counts[5],'dense_bytes',a.dense.stat().st_size,'compact_bytes',a.compact.stat().st_size)
if __name__=='__main__':main()
