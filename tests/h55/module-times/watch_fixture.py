#!/usr/bin/env python3
"""Drive the short synthetic Docker deadline; never emits a timing receipt."""
import importlib.util
import json
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("container_watch", root / "scripts/h55/module-times/container_watch.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
result = module.watch(sys.argv[1], sys.argv[2], .3)
print(json.dumps(result))
if result != {"status": "timeout", "exit_code": 137}:
    sys.exit(1)
