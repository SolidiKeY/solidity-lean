#!/usr/bin/env python3
"""Run per-file MCP diagnostics with one pinned Lean worker; no baseline cache."""
import argparse
import asyncio
import fcntl
import json
import os
from pathlib import Path
import resource
import sys
import subprocess
from verify import available, sha

if not __debug__:
    raise RuntimeError("H62 verification cannot run with Python optimization enabled")
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[4]


async def check(args):
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True,exist_ok=True)
    shim = evidence/'mcp-bin'
    shim.mkdir(exist_ok=True)
    wrapper = shim/'lake'
    wrapper.write_text('#!/bin/sh\nset -eu\nif [ "${1:-}" = serve ]; then\n  exec "$H62_PINNED_LAKE" "$@" -j1 --tstack=131072\nfi\nexec "$H62_PINNED_LAKE" "$@"\n')
    wrapper.chmod(0o755)
    env = dict(os.environ,PATH=str(shim)+os.pathsep+str(args.lean_bin.resolve())+os.pathsep+os.environ['PATH'],
               LEAN_NUM_THREADS='1',LEAN_LSP_MAX_OPEN_FILES='1',LEAN_PROJECT_PATH=str(ROOT),
               H62_PINNED_LAKE=str(args.lean_bin.resolve()/'lake'),
               LEAN_PATH=str(evidence/'build'),H62_GRAPH_OUTPUT_DIR=str(evidence))
    params = StdioServerParameters(command=sys.executable,args=['-m','lean_lsp_mcp','--lean-project-path',str(ROOT)],cwd=str(ROOT),env=env)
    assert available() >= 4*1024**3, '4GiB reserve missing'
    assert not int(next(l for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('SwapTotal:')).split()[1]), 'swap must be disabled'
    pin = json.loads(args.pin.read_text())
    assert sha(args.archive) == pin['sha256'], 'pinned archive checksum mismatch'
    version = subprocess.check_output([str(args.lean_bin.resolve()/'lean'),'--version'],text=True)
    assert pin['toolchain'].split(':')[-1].lstrip('v') in version, 'wrong Lean version'
    resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3))
    records = []
    async with stdio_client(params) as (read,write):
        async with ClientSession(read,write) as session:
            await session.initialize()
            for filename in args.files:
                result = await asyncio.wait_for(session.call_tool('lean_diagnostic_messages',{
                    'file_path':str(ROOT/'tests/h62/item5/statement-graph'/filename),
                    'interactive':False,'timeout_s':60}),timeout=90)
                records.append(dict(file=filename,result=result.model_dump(mode='json')))
                (evidence/'mcp-diagnostics.json').write_text(json.dumps(records,indent=2)+'\n')
                assert not result.isError, records[-1]
                data = result.structuredContent['result']
                assert data['success'] and not data.get('partial',False), data
                assert not [m for m in data.get('items',[]) if m.get('severity') in ('error','warning')], data
    print('H62_MCP_DIAGNOSTICS_PASS')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin',type=Path,required=True)
    parser.add_argument('--pin',type=Path,required=True)
    parser.add_argument('--archive',type=Path,required=True)
    parser.add_argument('--evidence',type=Path,required=True)
    parser.add_argument('--files',nargs='+',choices=('Exporter.lean','Fixture.lean','Pending.lean','Census.lean','EvmCensus.lean','WitnessFixture.lean'),default=['Exporter.lean','Fixture.lean'])
    args = parser.parse_args()
    assert not args.evidence.resolve().is_relative_to(ROOT), 'evidence must be off git'
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX | fcntl.LOCK_NB)
        async def guarded():
            async def monitor():
                while True:
                    if available() < 4*1024**3:
                        raise RuntimeError('4GiB reserve crossed during MCP')
                    await asyncio.sleep(.1)
            checking = asyncio.create_task(check(args))
            watching = asyncio.create_task(monitor())
            try:
                done,_ = await asyncio.wait((checking,watching),timeout=210,return_when=asyncio.FIRST_COMPLETED)
                if not done:
                    raise TimeoutError('MCP exceeded bounded runtime')
                for task in done:
                    await task
            finally:
                checking.cancel()
                watching.cancel()
                await asyncio.gather(checking,watching,return_exceptions=True)
        asyncio.run(guarded())

if __name__=='__main__':
    main()
