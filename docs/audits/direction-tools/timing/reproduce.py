#!/usr/bin/env python3
"""Recompute all findings from archived observations; no Lean or network.
python3 docs/audits/direction-tools/timing/reproduce.py --sample FILE \
  [--extra FILE ...] [--reference FILE ...] --out /external/DIR [--compare]
--compare requires byte-identical committed inventory.json and summary.json.
Measurements and profiler logs must be restored at their recorded VM paths.
"""
import argparse,os,pathlib,subprocess,sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--sample',type=pathlib.Path,required=True)
    ap.add_argument('--extra',type=pathlib.Path,action='append',default=[])
    ap.add_argument('--reference',type=pathlib.Path,action='append',default=[])
    ap.add_argument('--out',type=pathlib.Path,required=True)
    ap.add_argument('--compare',action='store_true')
    ap.add_argument('--native-findings',type=pathlib.Path)
    ap.add_argument('--verdicts',type=pathlib.Path,default=HERE/'verdicts.json')
    args=ap.parse_args(); out=args.out.resolve(); checkout=HERE.parents[3]
    if out==checkout or checkout in out.parents: ap.error('--out must be outside this checkout; never overwrite comparison targets')
    outputs={out/name for name in ('inventory.json','profiles.json','analysis.json','summary.json')}
    if any(path.resolve() in outputs for path in [args.sample,*args.extra,*args.reference]+([args.native_findings] if args.native_findings else [])+([args.verdicts] if args.verdicts.exists() else [])): ap.error('an input would be overwritten by a derived output')
    try: out.mkdir(parents=True,exist_ok=False)
    except FileExistsError: ap.error('--out must be a new directory, preventing symlink/hardlink output aliases')
    def run(script,*argv):
        subprocess.run([sys.executable,str(HERE/script),*map(str,argv)],check=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
    extras=[item for path in args.extra for item in ('--extra',path.resolve())]
    refs=[item for path in args.reference for item in ('--reference',path.resolve())]
    native=['--native-findings',args.native_findings.resolve()] if args.native_findings else []
    verdicts=['--verdicts',args.verdicts.resolve()] if args.verdicts.exists() else []
    run('audit.py','--out',out)
    run('profiles.py','--sample',args.sample.resolve(),*extras,'--out',out)
    run('analyze.py','--inventory',out/'inventory.json','--sample',args.sample.resolve(),*extras,*refs,*native,*verdicts,'--profiles',out/'profiles.json','--repo',HERE.parents[3],'--out',out)
    run('summarize.py','--sample',args.sample.resolve(),'--analysis',out/'analysis.json','--out',out)
    if args.compare:
        for name in ('inventory.json','summary.json'):
            if (HERE/name).read_bytes()!=(out/name).read_bytes(): raise SystemExit('FAIL: findings differ: '+name)
        print('PASS: byte-identical inventory and summary from archived inputs')
if __name__=='__main__': main()
