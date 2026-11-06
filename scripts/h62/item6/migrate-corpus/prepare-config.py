#!/usr/bin/env python3
"""Recreate private TOML and Lake command wrapper; never overwrite other content."""
import argparse,json,pathlib,shlex,subprocess
p=argparse.ArgumentParser();p.add_argument("mode",choices=["old","new"]);p.add_argument("official",type=pathlib.Path);p.add_argument("evidence",type=pathlib.Path);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4];e=a.evidence.resolve();e.mkdir(parents=True,exist_ok=True)
s=subprocess.check_output(["git","show","c6f550e281a7e5affa9a99bc2cdaed556dec00e4:lakefile.toml"],cwd=root,text=True)
s=s.replace('enableArtifactCache = true','enableArtifactCache = false').replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
s=s.replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = '+json.dumps(str(e/("build-"+a.mode))))
config=root/(".h62-migrate-corpus-"+a.mode+".toml")
def create(path,text):
    if path.exists():assert path.read_text()==text,f"preserve unexpected content: {path}"
    else:path.write_text(text)
create(config,s)
d=e/("commands-"+a.mode);d.mkdir(exist_ok=True);wrapper=d/"lake"
create(wrapper,'#!/bin/sh\nexec '+shlex.quote(str(a.official.resolve()/"bin/lake"))+' -f '+shlex.quote(str(config))+' "$@"\n');wrapper.chmod(0o755)
print(config)
