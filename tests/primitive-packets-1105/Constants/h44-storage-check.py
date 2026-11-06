#!/usr/bin/env python3
"""Require external evidence bytes and strict sealed-HEAD equality; no exemptions."""
import hashlib,json,os,pathlib,runpy,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[3]
F=pathlib.Path(__file__).resolve().parent
INPUT_ROOT=pathlib.Path(os.environ.get('SOL_NL_VALIDATION_INPUTS',str(ROOT)))
def required_inputs():
 manifest=json.loads((F/'h44-bulk-manifest.json').read_text())
 return [INPUT_ROOT/row['logical_path'] for row in manifest['files']]
def verify(manifest):
 assert manifest['schema']=='sol-numeric-literals-h44-v2'
 for row in manifest['files']:
  relative=pathlib.PurePosixPath(row['logical_path'])
  assert not relative.is_absolute() and '..' not in relative.parts
  path=INPUT_ROOT/relative
  assert path.is_file() and not path.is_symlink(),'required evidence missing '+str(path)
  raw=path.read_bytes()
  assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'evidence digest differs '+str(path)
def main():
 missing=[str(p) for p in required_inputs() if not p.is_file()]
 if missing:raise SystemExit('FAIL: required storage inputs missing: '+', '.join(missing))
 manifest=json.loads((F/'h44-bulk-manifest.json').read_text());verify(manifest)
 validate=runpy.run_path(str(ROOT/'scripts/check-sol-numeric-literals.py'))['validate_committed_inputs']
 validate()
 # Previously exempt evidence must now be rejected like every other untracked input.
 with tempfile.NamedTemporaryFile(prefix='unsealed-',suffix='.json',dir=ROOT/'tests/sol-numeric-literals/evidence') as temporary:
  try:validate()
  except ValueError as error:assert pathlib.Path(temporary.name).name in str(error)
  else:raise AssertionError('unsealed evidence accepted')
 validate()
 print('PASS: all manifest evidence digests and strict sealed HEAD; untracked evidence refused')
if __name__=='__main__':main()
