import asyncio, os, json
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

async def main():
    server = StdioServerParameters(command='/workspace/solidity-lean/scripts/run-lean-mcp.sh', cwd='/workspace/solidity-lean', env=dict(os.environ))
    async with stdio_client(server) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            for file in ['Solidity/Semantics/ContractWorld.lean', 'Solidity/Semantics/ContractWorldCertificates.lean', 'Solidity/Frontend/WorldImport.lean', 'Solidity/Examples/Tactics/ContractWorldSource.lean']:
                result = await session.call_tool('lean_diagnostic_messages', {'file_path':file,'severity':'error','interactive':False,'timeout_s':90})
                print(json.dumps({'file':file,'result':result.model_dump()},default=str), flush=True)
                if result.isError or not result.structuredContent['result']['success']:
                    raise RuntimeError('failed diagnostics: '+file)
asyncio.run(main())
