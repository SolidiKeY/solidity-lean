#!/usr/bin/env python3
"""Exact extra source-call/loop and retained late-failure kernel axiom sets."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.FragileReturnChecks.late_cost': ['Classical.choice',
                                                                 'Quot.sound',
                                                                 'propext'],
 'Solidity.Backend.InternalFlow.FragileReturnChecks.late_no_skipped_cost': ['Classical.choice',
                                                                            'Quot.sound',
                                                                            'propext'],
 'Solidity.Backend.InternalFlow.FragileReturnChecks.late_source': ['Classical.choice',
                                                                   'Quot.sound',
                                                                   'propext'],
 'Solidity.Backend.InternalFlow.FragileReturnChecks.late_target': ['Classical.choice',
                                                                   'Quot.sound',
                                                                   'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_loop_controls': ['Classical.choice',
                                                                          'Quot.sound',
                                                                          'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_prefix_actual': ['Classical.choice',
                                                                          'Quot.sound',
                                                                          'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_scope_actual': ['Classical.choice',
                                                                         'Quot.sound',
                                                                         'propext']}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "guarded_theorems": len(actual), "actual_axioms": actual}, indent=2))
