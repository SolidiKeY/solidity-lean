#!/usr/bin/env python3
"""Guard regression: a container runs before its synthetic deadline starts."""
import importlib.util
import json
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("container_watch", root / "scripts/h55/module-times/container_watch.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
result = module.start_and_watch(sys.argv[1], sys.argv[2], 1.5)
print(json.dumps(result))
if result != {"status": "timeout", "exit_code": 137}:
    sys.exit(1)
