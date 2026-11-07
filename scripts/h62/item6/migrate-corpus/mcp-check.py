#!/usr/bin/env python3
"""One-file MCP error diagnostics with the caller's explicit toolchain/cache."""
import asyncio,json,os,pathlib,sys
from mcp import ClientSession,StdioServerParameters
from mcp.client.stdio import stdio_client
async def main():
    root=pathlib.Path(__file__).resolve().parents[4]
    server=StdioServerParameters(command=str(root/"scripts/run-lean-mcp.sh"),cwd=str(root),env=dict(os.environ,LEAN_NUM_THREADS="1",LEAN_LSP_MAX_OPEN_FILES="1"))
    async with stdio_client(server) as (read,write):
        async with ClientSession(read,write) as session:
            await session.initialize()
            definitions={t.name:t for t in (await session.list_tools()).tools}
            tool=definitions["lean_diagnostic_messages"]
            properties=tool.inputSchema.get("properties",{})
            args={"file_path":sys.argv[1],"severity":"error","timeout_s":120}
            if "interactive" in properties:args["interactive"]=False
            result=await session.call_tool(tool.name,args)
            print(result.model_dump_json())
            assert not result.isError
            data=result.structuredContent["result"]
            assert data["success"] and data["partial"] is False and data["timed_out"] is False,data
            assert not data["items"] and not data["failed_dependencies"],data
asyncio.run(main())
