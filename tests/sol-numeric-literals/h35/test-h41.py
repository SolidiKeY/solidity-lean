#!/usr/bin/env python3
"""Regression for self-consistent replacement of mutable cache evidence."""
import copy,hashlib,json,pathlib,runpy,tempfile
root=pathlib.Path(__file__).resolve().parents[3]
folder=root/'tests/sol-numeric-literals'
ns=runpy.run_path(str(root/'scripts/check-sol-numeric-literals.py'))
real=json.loads((folder/'evidence/h41-cache-handoff.json').read_text())
ns['validate_h41_cache_record'](real)
with tempfile.TemporaryDirectory(prefix='h41-replacement-',dir=folder/'h35') as temporary:
 path=pathlib.Path(temporary);archive=path/'fake.tar.gz';archive.write_bytes(b'not the coordinator-approved cache')
 digest=hashlib.sha256(archive.read_bytes()).hexdigest()
 prepared=json.loads((folder/'evidence/h35-owned-cache-manifest.json').read_text())
 prepared['archive_sha256']=digest
 manifest=path/'prepared.json';manifest.write_text(json.dumps(prepared))
 forged=copy.deepcopy(real);forged.update(archive=str(archive),archive_sha256=digest,prepared_manifest=str(manifest.relative_to(root)))
 try:ns['validate_h41_cache_record'](forged)
 except ValueError as e:assert 'approved archive digest differs' in str(e)
 else:raise AssertionError('self-consistent replacement cache was accepted')
ns['validate_h41_cache_record'](real)
print('H41: authorized preserved pack passes; self-consistent replacement archive and metadata rejected; no real asset changed')
