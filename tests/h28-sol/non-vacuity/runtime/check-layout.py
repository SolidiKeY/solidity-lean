#!/usr/bin/env python3
"""Matched no-output fresh source check for layout measurement only."""
import json,os,pathlib,subprocess,sys
here=pathlib.Path(__file__).resolve().parents[1]
root=here.parents[2]
assert os.environ.get('LEAN_NUM_THREADS')=='1' and os.environ.get('LEAN_PATH')
env=dict(os.environ,LEAN_PATH=str(here/'runtime/build/lib')+os.pathsep+os.environ['LEAN_PATH'])
file=pathlib.Path(sys.argv[1]).resolve()
assert file.is_relative_to(here/'lean')
command=['lean','-j1','--tstack=131072','--root='+str(here/'lean'),str(file)]
print('MATCHED_LAYOUT_COMMAND '+json.dumps(command),flush=True)
raise SystemExit(subprocess.run(command,cwd=root,env=env).returncode)
