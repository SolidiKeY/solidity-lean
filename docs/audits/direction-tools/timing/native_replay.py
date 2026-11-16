#!/usr/bin/env python3
"""Recompute a native profile from raw samples and exact recorded ELF binaries.
No Lean/network/perf calls. --out must be a new external directory.
python3 .../native_replay.py --profile EXTERNAL/native-profile.json \
  --samples EXTERNAL/native-samples.json --out /external/NEW [--compare]
"""
import argparse,collections,hashlib,json,pathlib,types
from native_profile import symbolize
HERE=pathlib.Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--profile',type=pathlib.Path,required=True);ap.add_argument('--samples',type=pathlib.Path,required=True);ap.add_argument('--out',type=pathlib.Path,required=True);ap.add_argument('--compare',action='store_true');args=ap.parse_args()
    recorded=json.loads(args.profile.read_text());raw=json.loads(args.samples.read_text());assert raw['head']==recorded['head']
    for binary in recorded['profile']['symbolized_binaries']:
        digest=hashlib.sha256()
        with open(binary['path'],'rb') as handle:
            for block in iter(lambda:handle.read(1024*1024),b''):digest.update(block)
        assert digest.hexdigest()==binary['sha256'],'ELF content changed: '+binary['path']
    obj=types.SimpleNamespace(maps=raw['maps'],counts=collections.Counter(dict(raw['ip_counts'])),lost=raw['lost_samples'],events={i:None for i in range(raw['sampled_threads'])})
    result=symbolize(obj)
    if args.compare: assert result==recorded['profile'],'native symbol/count replay differs'
    out=args.out.resolve()
    for checkout in (HERE.parents[3],pathlib.Path(recorded['check']['cwd']).resolve()):
        if out==checkout or checkout in out.parents:ap.error('--out must be outside checkouts')
    try:out.mkdir(parents=True,exist_ok=False)
    except FileExistsError:ap.error('--out must be a new directory')
    (out/'native-replay.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS: native raw samples reproduce symbol/count profile')
if __name__=='__main__':main()
