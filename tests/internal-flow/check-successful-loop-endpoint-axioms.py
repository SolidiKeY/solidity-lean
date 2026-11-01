#!/usr/bin/env python3
"""Exact kernel axiom sets for the successful allocating-loop consumer."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.SuccessfulLoop.complete_endpoint': ['Classical.choice',
                                                                    'Quot.sound',
                                                                    'propext'],
 'Solidity.Backend.InternalFlow.SuccessfulLoop.endpoint': ['Classical.choice',
                                                           'Quot.sound',
                                                           'propext'],
 'Solidity.Backend.InternalFlow.SuccessfulLoop.negative_controls': ['Classical.choice',
                                                                    'Quot.sound',
                                                                    'propext'],
 'Solidity.Backend.InternalFlow.SuccessfulLoop.next_use': ['Classical.choice',
                                                           'Quot.sound',
                                                           'propext'],
 'Solidity.Backend.InternalFlow.SuccessfulLoop.reached': ['Classical.choice',
                                                          'Quot.sound',
                                                          'propext'],
 'Solidity.Backend.InternalFlow.SuccessfulLoop.success_not_failure': ['Classical.choice',
                                                                      'Quot.sound',
                                                                      'propext']}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "reports": len(reports)}, sort_keys=True))
