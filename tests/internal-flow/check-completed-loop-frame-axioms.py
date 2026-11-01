#!/usr/bin/env python3
"""Exact kernel axiom sets for completed-loop framing and actual writer rejection."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.CompletedLoopChecks.actual_loop': ['Classical.choice',
                                                                   'Quot.sound',
                                                                   'propext'],
 'Solidity.Backend.InternalFlow.CompletedLoopChecks.all_old_contents': ['Classical.choice',
                                                                        'Quot.sound',
                                                                        'propext'],
 'Solidity.Backend.InternalFlow.CompletedLoopChecks.completed_frame': ['Classical.choice',
                                                                       'Quot.sound',
                                                                       'propext'],
 'Solidity.Backend.InternalFlow.CompletedLoopChecks.roots_and_transaction': ['Classical.choice',
                                                                             'Quot.sound',
                                                                             'propext'],
 'Solidity.Backend.InternalFlow.CompletedLoopChecks.writer_guard_refused': ['propext'],
 'Solidity.Backend.InternalFlow.CompletedLoopChecks.writer_not_kept': ['Classical.choice',
                                                                       'Quot.sound',
                                                                       'propext'],
 'Solidity.Backend.InternalFlow.scoped_loop_completed_frame': ['Classical.choice',
                                                               'Quot.sound',
                                                               'propext']}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "reports": len(reports)}, sort_keys=True))
