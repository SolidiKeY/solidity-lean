#!/usr/bin/env python3
"""Prepare only fresh registered private oleans; no Lake traces/maps are invented."""
import hashlib,json,pathlib,re,shutil,subprocess,tempfile,sys
ROOT=pathlib.Path('/workspace/solidity-lean');HERE=ROOT/'tests/h28-sol/non-vacuity'
if len(sys.argv)!=2:raise SystemExit('usage: prepare-cache.py OWNED_SEALED_DIRECTORY')
OUT=pathlib.Path(sys.argv[1]).resolve()
assert OUT.is_relative_to(HERE/'sealed') and OUT.is_dir(),'output outside owned evidence scope'
LIB=HERE/'runtime/build/lib';TOOL=pathlib.Path('/workspace/.setup/tools/lean-4.24.0-linux/lib/lean')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads((OUT/'evidence/kernel-all.json').read_text());log=OUT/'evidence/kernel-all.log'
assert meta['exit']==0 and meta['stop'] is None and meta['limits']==[str(12*1024**3),'0']
assert meta['command']==['lake','env','python3','tests/h28-sol/non-vacuity/kernel.py','--all','--fresh'],'expected exact fresh kernel command'
assert meta['log_sha256']==sha(log) and meta['minimum_vm_available_bytes']>=4*1024**3
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();assert head==meta['git_head']
version_log=OUT/'evidence/keysort.log';version_meta=json.loads((OUT/'evidence/keysort.json').read_text())
assert version_meta['git_head']==head and version_meta['exit']==0 and version_meta['stop'] is None
assert version_meta['command']==['tests/h28-sol/non-vacuity/runtime/keysort']
assert version_meta['log_sha256']==sha(version_log)
versions=version_log.read_text().splitlines()
assert 'version 4.24.0,' in versions[0] and 'commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b' in versions[0]
assert versions[1].startswith('Lake version 5.0.0-src+797c613') and 'KEYSORT_PASS' in version_log.read_text()
registry=json.loads((HERE/'registration.json').read_text())['modules']
steps=[json.loads(line[len('H28_MODULE_PASS '):]) for line in log.read_text().splitlines() if line.startswith('H28_MODULE_PASS ')]
assert len(steps)==len(registry)==26 and {x['module'] for x in steps}=={x['module'] for x in registry}
steps={x['module']:x for x in steps};owned=set(steps)
cache=OUT/'cache';cache.mkdir(exist_ok=False);payload=cache/'payload';payload.mkdir()
modules=[];dependencies={};files={}
for row in registry:
 name=row['module'];record=steps[name];source=ROOT/row['file'];olean=LIB/(name.replace('.','/')+'.olean')
 assert record['source_sha256']==sha(source) and meta['input_sha256'][row['file']]==sha(source)
 assert olean.is_file() and not olean.is_symlink() and olean.resolve().is_relative_to(LIB.resolve())
 assert sha(olean)==record['olean_sha256'] and record['exit']==0 and '-j1' in record['command']
 relative='lib/lean/'+name.replace('.','/')+'.olean';target=payload/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(olean,target)
 files[relative]=sha(target)
 imports=re.findall(r'^import (\S+)',source.read_text(),re.M)
 for dependency in imports:
  if dependency in owned:continue
  suffix=dependency.replace('.','/')+'.olean';choices=[LIB/suffix,ROOT/'.lake/build/lib/lean'/suffix,TOOL/suffix]
  actual=next((x for x in choices if x.is_file()),None);assert actual is not None,dependency
  dependencies[dependency]=dict(path=str(actual.resolve()),sha256=sha(actual),bytes=actual.stat().st_size)
 modules.append(dict(module=name,source=row['file'],source_sha256=sha(source),cache_file=relative,olean_sha256=sha(target),imports=imports,kernel_command=record['command'],kernel_seconds=record['elapsed_seconds'],kernel_fingerprint=record['fingerprint'],artifact_types=['olean'],lake_trace_generated=False))
axioms=json.loads((HERE/'axiom-pins.json').read_text())['theorems'];assert len(axioms)==431 and all(set(x)<={'propext','Classical.choice','Quot.sound'} for x in axioms.values())
manifest=dict(adopted_upstream=json.loads((HERE/'inventory.json').read_text())['published_copy']['upstream'],format='h28-private-kernel-cache-v1',head=head,base='6f3eedf0788ee1f8a3bcf230558c712ecdca04d5',branch=subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip(),repository=str(ROOT),lean=versions[0],lake=versions[1],version_evidence_sha256=sha(version_log),generator_sha256=sha(pathlib.Path(__file__)),kernel_metadata_sha256=sha(OUT/'evidence/kernel-all.json'),kernel_log_sha256=sha(log),reviewed_inputs_sha256=sha(OUT/'reviewed-inputs.json'),axiom_manifest_sha256=sha(HERE/'axiom-pins.json'),modules=modules,direct_baseline_dependency_oleans=dependencies,files=files,boundary='Exactly26 fresh private kernel oleans, not stale .lake/build H28 outputs. No .trace/.ilean or input mappings fabricated. Receiver must verify exact frozen baseline/toolchain and dependency digests before use. Changed baseline requires rechecking. H41 coordinator-pull pack only; worker must not invoke ship-cache.sh. Remote transfer receipt is not fabricated.')
(payload/'cache-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');files['cache-manifest.json']=sha(payload/'cache-manifest.json')
archive=cache/'h28-owned-kernel-cache.tar.zst';pack=['tar','--use-compress-program=zstd -T1 -3 -q','-cf',str(archive),'-C',str(payload),'.'];subprocess.run(pack,check=True,cwd=ROOT)
with tempfile.TemporaryDirectory(dir=cache) as directory:
 subprocess.run(['tar','--zstd','-xf',str(archive),'-C',directory],check=True,cwd=ROOT)
 unpack=pathlib.Path(directory);found={str(x.relative_to(unpack)) for x in unpack.rglob('*') if x.is_file()};assert found==set(files)
 for relative,digest in files.items():assert sha(unpack/relative)==digest
result=dict(status='prepared and locally verified; NOT SHIPPED',remote_receipt=None,head=head,module_count=26,archive=str(archive),archive_bytes=archive.stat().st_size,archive_sha256=sha(archive),manifest=str(payload/'cache-manifest.json'),manifest_sha256=sha(payload/'cache-manifest.json'),pack_command=pack,verification='Extracted archive and verified exact file set plus SHA256 for all26 oleans and manifest',payload_files=files)
(cache/'cache-preparation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='payload_files'}))
