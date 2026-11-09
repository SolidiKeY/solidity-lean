#!/usr/bin/env python3
"""Let the pinned MCP server run its own finally cleanup on bridge SIGTERM.

The bridge currently terminates its immediate stdio server. Python's default
SIGTERM bypasses lean-lsp-mcp's close_shared_client finally block. Translate
only that signal to its existing KeyboardInterrupt shutdown path; child/group
ownership and retirement remain the pinned package's responsibility. This does
not certify closure: callers must still confirm it with their owned supervisor.
"""
import runpy
import signal


def interrupt(_signal, _frame):
    # A repeated TERM must not interrupt the pinned package's finally block.
    # The independent supervisor retains its unchanged SIGKILL/deadline authority.
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    raise KeyboardInterrupt


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, interrupt)
    runpy.run_module("lean_lsp_mcp", run_name="__main__", alter_sys=True)
