#!/usr/bin/env python3
"""Prepare pinned optional Bridge dependencies without editing tracked interfaces.
Package configs are copied externally, preserving options except serial/cache flags.
"""
import argparse,json,pathlib,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);p.add_argument('--cache',required=True);p.add_argument('--core-config',required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4];bridge=root/'Bridge';e=pathlib.Path(a.evidence).resolve();deps=e/'dependencies';configs=e/'dependency-configs';deps.mkdir(parents=True,exist_ok=True);configs.mkdir(exist_ok=True);cache=pathlib.Path(a.cache)
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.24.0'
assert (bridge/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.24.0'
manifest=json.loads((bridge/'lake-manifest.json').read_text());entries=[];receipts=[]
def run(command):return subprocess.check_output(command,stderr=subprocess.STDOUT,text=True)
def serial_config(text,suffix):
 if suffix=='.toml':
  top,sep,tail=text.partition('[[')
  if re.search(r'^weakLeanArgs\s*=',top,re.M):raise RuntimeError('existing package weakLeanArgs requires explicit merge')
  text='weakLeanArgs = ["--tstack=131072", "-j1"]\n'+text
  return text.replace('enableArtifactCache = true','enableArtifactCache = false')
 lines=text.splitlines();out=[];inserted=False
 for line in lines:
  if re.match(r'^package\s+',line):
   if not line.rstrip().endswith(('where','{')):line=line+' where'
   out.extend([line,'  weakLeanArgs := #["--tstack=131072", "-j1"]']);inserted=True
  else:out.append(line)
 if not inserted:raise RuntimeError('unrecognized Lake package declaration')
 return '\n'.join(out)+'\n'
for entry in manifest['packages']:
 if entry['name'].strip('«»')=='solidity-lean':continue
 if entry['type']!='git':raise RuntimeError('unexpected dependency kind')
 name=entry['name'];rev=entry['rev'];d=deps/name;old=cache/name
 if not d.exists():
  if old.exists():
   assert run(['git','-C',str(old),'rev-parse','HEAD']).strip()==rev
   subprocess.run(['git','-C',str(old),'diff','--quiet','HEAD'],check=True)
   run(['git','-C',str(old),'worktree','add','--detach',str(d),rev])
  else:
   run(['git','init',str(d)]);run(['git','-C',str(d),'remote','add','origin',entry['url']]);run(['git','-C',str(d),'fetch','--depth','1','origin',rev]);run(['git','-C',str(d),'checkout','--detach','FETCH_HEAD'])
 assert run(['git','-C',str(d),'rev-parse','HEAD']).strip()==rev
 subprocess.run(['git','-C',str(d),'diff','--quiet','HEAD'],check=True)
 toolchain=d/'lean-toolchain'
 declared=toolchain.read_text().strip() if toolchain.exists() else None
 # Frozen dependencies may declare an older release candidate. They are built
 # by the explicit root v4.24 binary; no dependency toolchain is installed.
 if declared and 'v4.35' in declared:raise RuntimeError('unexpected migration dependency: '+name)
 # Reuse only exact-pinned external library build artifacts; configs stay private.
 if (old/'.lake/build').exists() and not (d/'.lake/build').exists():
  (d/'.lake').mkdir(exist_ok=True);(d/'.lake/build').symlink_to(old/'.lake/build',target_is_directory=True)
 config=d/entry.get('configFile','lakefile.lean');out=configs/(name+config.suffix);out.write_text(serial_config(config.read_text(),config.suffix))
 entries.append(dict(name=name,scope=entry.get('scope',''),type='path',dir=str(d),configFile=str(out),manifestFile=str(d/entry.get('manifestFile','lake-manifest.json')),inherited=entry.get('inherited',False)))
 receipts.append(dict(name=name,rev=rev,source=str(d),config=str(out),source_unchanged=True,declared_toolchain=declared,intended_root_toolchain='v4.24.0'))
entries.append(dict(name='«solidity-lean»',type='path',dir=str(root),configFile=str(pathlib.Path(a.core_config).resolve()),manifestFile=str(root/'lake-manifest.json'),inherited=False))
(e/'bridge-overrides.json').write_text(json.dumps(dict(version='1.1.0',packages=entries),indent=2)+'\n')
text=(bridge/'lakefile.toml').read_text().replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = "'+str(e/'bridge-build')+'"\nweakLeanArgs = ["-j1"]')
text=text.replace('enableArtifactCache = true','enableArtifactCache = false');(e/'bridge.lakefile.toml').write_text(text)
(e/'dependency-pins.json').write_text(json.dumps(receipts,indent=2)+'\n')
# Standard ignored runtime package links also make repository attribution paths real.
packages=bridge/'.lake/packages';packages.mkdir(parents=True,exist_ok=True)
# Nested Lake invocations must retain the same private, serial dependency config.
(bridge/'.lake/package-overrides.json').write_text((e/'bridge-overrides.json').read_text())
for receipt in receipts:
 link=packages/receipt['name']
 if not link.exists():link.symlink_to(receipt['source'],target_is_directory=True)
print(json.dumps(dict(dependencies=len(receipts),toolchain='v4.24.0',tracked_source_edits=0,config=str(e/'bridge.lakefile.toml'))))
