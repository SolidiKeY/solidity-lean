#!/usr/bin/env python3
"""Write pinned Lean source paths after validating an explicit frozen checkout."""
import argparse,json,pathlib,runpy
HERE=pathlib.Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--reference-view',type=pathlib.Path);a=p.parse_args()
 api=runpy.run_path(str(HERE/'audit.py'));src=api['assert_sources'](a.source_root)
 root=a.source_root.resolve();rows=[]
 for p in sorted(src):
  module=None
  if a.reference_view:
   ref=a.reference_view/pathlib.Path(p.removeprefix('vendor/LeanTeX/').removeprefix('Bridge/')).with_suffix('.ilean')
   if ref.is_file():module=json.loads(ref.read_text())['module']
  rows.append(json.dumps(dict(path=str(root/p),module=module)))
 a.out.write_text('\n'.join(rows)+'\n')
 print('PINNED_SOURCE_PATHS_PASS',len(src))
if __name__=='__main__':main()
