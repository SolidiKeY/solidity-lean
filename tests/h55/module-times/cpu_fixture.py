#!/usr/bin/env python3
"""Guard regression: matching child settings conceal a limited CPU ancestor."""
import importlib.util
import json
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("cpu_ancestry", root / "scripts/h55/module-times/cpu_ancestry.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
result = module.local_snapshot(sys.argv[1], sys.argv[2])
print(json.dumps(result, sort_keys=True))
if result.get("ancestor_complete") is not False or not result.get("visible_chain"):
    sys.exit(1)
