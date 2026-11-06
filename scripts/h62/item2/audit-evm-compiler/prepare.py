#!/usr/bin/env python3
"""Generate an external, serial, cache-free build configuration."""
import argparse,pathlib
p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);a=p.parse_args();root=pathlib.Path(__file__).resolve().parents[4];evidence=pathlib.Path(a.evidence).resolve();evidence.mkdir(parents=True,exist_ok=True)
s=(root/'lakefile.toml').read_text();s=s.replace('version = "0.1.0"','version = "0.1.0"\nsrcDir = "'+str(root)+'"\nbuildDir = "'+str(evidence/'build')+'"');s=s.replace('enableArtifactCache = true','enableArtifactCache = false').replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
(evidence/'serial.lakefile.toml').write_text(s);print(evidence/'serial.lakefile.toml')
