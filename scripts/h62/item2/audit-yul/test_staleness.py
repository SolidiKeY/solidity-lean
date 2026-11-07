#!/usr/bin/env python3
"""Negative provenance controls; never modifies a proof or original interface."""
import argparse,copy,hashlib,json,pathlib,subprocess
ap=argparse.ArgumentParser();ap.add_argument('census',type=pathlib.Path);ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
original=json.loads(args.census.read_text());results=[]
for case in ['stale_tool_hash','failed_tool_gate','duplicate_control_record']:
 data=copy.deepcopy(original)
 row=next(r for r in data['declarations'] if r['source_name']=='Solidity.Yul.pow_halve' and r['kind']=='theorem')
 evidence=row['audit_evidence'];snapshot=json.load(open(evidence['control_snapshot']))
 if case=='stale_tool_hash':
  snapshot['proof_tool_sha256']='0'*64;evidence['proof_tool_sha256']='0'*64
 elif case=='failed_tool_gate':snapshot['proof_tool_gate']['exit']=1
 else:snapshot['records'][1]=snapshot['records'][0]
 snapshot_path=args.output/(case+'-snapshot.json');snapshot_path.write_text(json.dumps(snapshot,sort_keys=True)+'\n')
 evidence['control_snapshot']=str(snapshot_path);evidence['control_snapshot_sha256']=hashlib.sha256(snapshot_path.read_bytes()).hexdigest()
 census_path=args.output/(case+'-census.json');census_path.write_text(json.dumps(data,ensure_ascii=False,sort_keys=True)+'\n')
 cmd=['python3','scripts/h62/item2/audit-yul/acceptance.py',str(census_path),'--output',str(args.output/(case+'-result'))]
 result=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (args.output/(case+'.log')).write_text(result.stdout)
 if result.returncode==0:raise SystemExit('invalid provenance accepted: '+case)
 results.append(dict(case=case,command=cmd,exit=result.returncode,expected='reject',outcome='pass'))
(args.output/'results.json').write_text(json.dumps(results,indent=2)+'\n');print('PROVENANCE_NEGATIVE_CONTROLS_PASS: 3 invalid inputs rejected; no proof/source edits')
