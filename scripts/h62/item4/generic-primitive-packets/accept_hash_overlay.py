#!/usr/bin/env python3
"""H70 source-overlay acceptance; never runs Lean or writes original sources."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from census import ROOT, BASE
from check import load_overlay
from stage_hash_overlay import BLOBS, blob


def require(condition,message):
    if not condition:
        raise ValueError(message)


def refused(action):
    try:
        action()
    except ValueError:
        return
    raise ValueError('invalid owner overlay accepted')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('evidence',type=Path)
    args=parser.parse_args()
    source=args.source.resolve()
    fixture=ROOT/'tests/h62/item4/generic-primitive-packets'
    expected=json.loads((fixture/'hash-owner-relay.json').read_text())
    require(json.loads((source/'owner-overlay.json').read_text())==expected,'owner manifest mismatch')
    patch_fixture=json.loads((fixture/'hash-owner-relay.patch.json').read_text())
    require((source/'owner-overlay.patch').read_text()==patch_fixture['patch'],'owner patch mismatch')
    require(hashlib.sha256(patch_fixture['patch'].encode()).hexdigest()==patch_fixture['sha256'],'serialized patch checksum mismatch')
    require(len(load_overlay(source))==2,'lost owner overlay file')
    for relative,(before,after) in BLOBS.items():
        original=(ROOT/relative).read_bytes()
        require(original==subprocess.check_output(['git','show',f'{BASE}:{relative}'],cwd=ROOT),'original modified')
        require(blob(original)==before and blob((source/relative).read_bytes())==after,'full owner blob mismatch')
    stage=ROOT/'scripts/h62/item4/generic-primitive-packets/stage_hash_overlay.py'
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    with tempfile.TemporaryDirectory(prefix='overlay-acceptance-',dir=args.evidence) as scratch:
        scratch=Path(scratch); reproduced=scratch/'source'
        r=subprocess.run([sys.executable,str(stage),str(reproduced)],capture_output=True,text=True,env=env)
        require(r.returncode==0,r.stderr)
        for relative in BLOBS:
            require((reproduced/relative).read_bytes()==(source/relative).read_bytes(),'non-deterministic source overlay')
        require((reproduced/'owner-overlay.patch').read_bytes()==(source/'owner-overlay.patch').read_bytes(),'non-deterministic patch')
        sentinel=scratch/'sentinel'; sentinel.write_text('UNCHANGED')
        trap=scratch/'existing'; (trap/'Solidity/Hash').mkdir(parents=True)
        (trap/'Solidity/Hash/CollisionBound.lean').symlink_to(sentinel)
        r=subprocess.run([sys.executable,'-O',str(stage),str(trap)],capture_output=True,text=True,env=env)
        require(r.returncode!=0 and sentinel.read_text()=='UNCHANGED','symlink/reused staging destination accepted')
        manifest=reproduced/'owner-overlay.json'; data=json.loads(manifest.read_text())
        data['files'][0]['owner_post_blob']='0'*40
        manifest.write_text(json.dumps(data))
        refused(lambda:load_overlay(reproduced))
    print('EXACT_OWNER_OVERLAY_ACCEPTANCE_PASS: full blobs, deterministic reproduction, unchanged originals, optimized symlink refusal, tampered-manifest refusal')


if __name__=='__main__':
    main()
