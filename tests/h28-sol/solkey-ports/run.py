#!/usr/bin/env python3
"""Record one selected acceptance command; success is the real child exit code."""
import hashlib,json,os,pathlib,resource,subprocess,sys,time
name,*cmd=sys.argv[1:]
e=pathlib.Path(os.environ.get('H28_EVIDENCE_DIR',pathlib.Path(__file__).resolve().parent/'evidence'));e.mkdir(parents=True,exist_ok=True)
sources=[pathlib.Path('Solidity/Calculus/SolkeyAgreementH28/Freshness.lean'),
 *pathlib.Path('tests/h28-sol/solkey-ports').glob('*.lean')]
identities={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
start=time.monotonic()
with (e/(name+'.log')).open('w') as log:
    p=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
record=dict(command=cmd,head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=identities,exit=p.returncode,seconds=time.monotonic()-start,
 max_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
 lean_num_threads=os.getenv('LEAN_NUM_THREADS'))
for key in ['memory.max','memory.swap.max','memory.peak','memory.events']:
    f=pathlib.Path('/sys/fs/cgroup')/key
    record[key]=f.read_text().strip() if f.exists() else None
(e/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record));sys.exit(p.returncode)
