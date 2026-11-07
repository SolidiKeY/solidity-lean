#!/usr/bin/env python3
"""Create a fresh off-git source snapshot for comparable migration measurements.
Run under the lane writer lock. Never modifies the source checkout or its cache.
"""
import argparse, hashlib, json, pathlib, subprocess, tarfile
BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
p=argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('--output',required=True)
p.add_argument('--toolchain',choices=['old','new'],required=True);p.add_argument('--pin',required=True)
a=p.parse_args();repo=pathlib.Path(a.repo).resolve();out=pathlib.Path(a.output).resolve()
if out.is_relative_to(repo): p.error("snapshot output must be outside the source checkout")
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
subprocess.run(['git','-C',str(repo),'merge-base','--is-ancestor',BASE,head],check=True)
pin=json.loads(pathlib.Path(a.pin).read_text())
assert pin['toolchain']=='leanprover/lean4:v4.35.0'
assert pin['sha256']=='7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'
out.mkdir(parents=True,exist_ok=False)
proc=subprocess.Popen(['git','-C',str(repo),'archive',BASE],stdout=subprocess.PIPE)
with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:archive.extractall(out,filter='data')
assert proc.wait()==0
config=out/'lakefile.toml';original=config.read_bytes()
# Package-level arguments cover executables and vendor libraries as well.
text=original.decode().replace('enableArtifactCache = true','enableArtifactCache = false\nmoreLeanArgs = ["--tstack=131072", "-j1", "-M10000"]')
assert text!=original.decode();config.write_text(text)
if a.toolchain=='new':(out/'lean-toolchain').write_text(pin['toolchain']+'\n')
manifest={'base':BASE,'preparing_head':head,'snapshot':str(out),'toolchain':(out/'lean-toolchain').read_text().strip(),
    'original_lakefile_sha256':hashlib.sha256(original).hexdigest(),
    'private_lakefile_sha256':hashlib.sha256(config.read_bytes()).hexdigest(),
    'cache':'fresh .lake absent; enableArtifactCache=false; build with --no-cache',
    'config_changes':'private testing only: cache disabled; --tstack=131072 -j1 -M10000; no heartbeat or recursion-budget change'}
(out.parent/(out.name+'-manifest.json')).write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest))
