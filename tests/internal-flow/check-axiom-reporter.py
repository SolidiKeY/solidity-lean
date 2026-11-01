#!/usr/bin/env python3
"""Metadata-tool module: actual source selftests, no headline proof reports.
All original theorem reports are independently checked by their existing guards.
"""
import json,re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text()
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
assert reports == [], "unexpected proof report in metadata-tool module"
assert 'error:' not in text and 'error(' not in text, "Lean diagnostics contain an error"
print(json.dumps({'status':'pass','reports':0,'metadata_tool_only_not_proof_coverage':True},sort_keys=True))
