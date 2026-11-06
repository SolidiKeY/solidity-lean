#!/usr/bin/env python3
"""Disable leanclient automatic dependency rebuilds for guarded diagnostics.

Lean diagnostics and their errors are unmodified. Missing dependencies remain
errors; this wrapper only prevents an uncontrolled Lake build.
"""
import sys
from leanclient.aio.client import AsyncLeanLSPClient
from lean_lsp_mcp import main

AsyncLeanLSPClient._needs_dependency_rebuild = staticmethod(lambda doc: False)
sys.exit(main())
