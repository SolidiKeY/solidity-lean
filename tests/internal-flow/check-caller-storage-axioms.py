#!/usr/bin/env python3
"""Guard actual unmodified builtin reports for the storage-result path and liveness consumers.
Run on the separately checked import query; it does not replace kernel checking
or the unchanged original542-report fixture inventory.
"""
import json
from pathlib import Path
import re
import sys
NAMES = ['Solidity.Backend.InternalFlow.CallerView.storage_alias_drop', 'Solidity.Backend.InternalFlow.CallerView.represented_storage_drop', 'Solidity.Backend.InternalFlow.CallerView.represented_fragile_drop', 'Solidity.Backend.InternalFlow.CallerView.dead_not_fragile', 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.returned_reference', 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.result_view', 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.returned_slot', 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.returned_slot_not_memory_pointer', 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.stale_is_not_live']
PINS = {'Solidity.Backend.InternalFlow.CallerView.storage_alias_drop': ['propext'], 'Solidity.Backend.InternalFlow.CallerView.represented_storage_drop': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerView.represented_fragile_drop': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerView.dead_not_fragile': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.returned_reference': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.result_view': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.returned_slot': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.returned_slot_not_memory_pointer': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult.stale_is_not_live': ['Classical.choice', 'Quot.sound', 'propext']}
PATTERN = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)", text):
        raise ValueError("diagnostic or untrusted axiom in builtin audit")
    reports = [(n, sorted(x.strip() for x in a.split(',') if x.strip()))
               for n, a in re.findall(PATTERN, text)]
    expected = [(n, PINS[n]) for n in NAMES]
    if reports != expected:
        raise ValueError("missing, reordered, duplicate or changed caller-storage axiom report")
    return len(reports)
if __name__ == '__main__':
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'pass', 'actual_builtin_reports': count}))
