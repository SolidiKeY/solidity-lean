#!/usr/bin/env python3
"""Reproduce H44 off-Git source census with exact parser-input binding."""
import argparse, fcntl, json, pathlib, shutil, subprocess
import census
ap=argparse.ArgumentParser();ap.add_argument('--lean',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path,required=True);ap.add_argument('--witnesses',type=pathlib.Path);ap.add_argument('--kernel',type=pathlib.Path);args=ap.parse_args()
args.output.mkdir(parents=True,exist_ok=True)
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
files,unmatched=census.files()
if unmatched:raise SystemExit('unmatched module-map patterns: '+str(unmatched))
filelist=args.output/'files.txt';filelist.write_text(''.join(p+'\n' for p in sorted(files)))
# The serial runner owns the writer lock and continuously monitors its process
# group and cgroup headroom. Never nest a second Lean process or writer lock.
fcntl.flock(lock,fcntl.LOCK_UN)
runner_output=args.output/'parser-run'
cmd=['python3','scripts/h62/item2/audit-yul/check_serial.py','--evidence',str(runner_output),'--lean',str(args.lean),'--run','tests/h62/item2/audit-yul/ParseSignatures.lean','--files',str(filelist)]
result=subprocess.run(cmd)
if result.returncode:raise SystemExit(result.returncode)
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
last=json.loads((runner_output/'commands.jsonl').read_text().splitlines()[-1])
shutil.copyfile(last['log'],args.output/'parser.jsonl')
# Parser diagnostics are visible in the log but JSON records alone are input.
lines=(args.output/'parser.jsonl').read_text().splitlines()
records=[];diagnostics=[]
for line in lines:
 try:
  obj=json.loads(line)
  if isinstance(obj,dict) and 'file' in obj and 'source_text' in obj:
   records.append(line);diagnostics.extend(obj.get('diagnostics',[]))
  else:diagnostics.append(line)
 except json.JSONDecodeError:diagnostics.append(line)
if len(records)!=len(files) or {json.loads(line)['file'] for line in records}!=set(files):raise SystemExit('parser file census mismatch')
(args.output/'parser.jsonl').write_text('\n'.join(records)+'\n')
(args.output/'parser-errors.log').write_text('\n'.join(diagnostics)+'\n')
cmd=['python3','scripts/h62/item2/audit-yul/census.py','--parsed',str(args.output/'parser.jsonl'),'--output',str(args.output/'census')]
if args.witnesses:cmd+=['--witnesses',str(args.witnesses)]
if args.kernel:cmd+=['--kernel',str(args.kernel)]
raise SystemExit(subprocess.run(cmd).returncode)
