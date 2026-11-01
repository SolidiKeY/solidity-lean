#!/usr/bin/env python3
"""Guard actual unmodified builtin reports for the mixed-store alias-frame consumers.
Run on the separately checked import query; it does not replace kernel checking
or the unchanged original542-report fixture inventory.
"""
import json
from pathlib import Path
import re
import sys
NAMES = ['Solidity.Backend.InternalFlow.CallerView.alias_get_set_value', 'Solidity.Backend.InternalFlow.CallerView.storage_assign_environment', 'Solidity.Backend.InternalFlow.CallerView.scalar_assign_storage_alias', 'Solidity.Backend.InternalFlow.CallerView.mixed_store_alias', 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.alias_frame', 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.exact_body_result', 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.final_slot', 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.wrong_element_after_suffix']
PINS = {'Solidity.Backend.InternalFlow.CallerView.alias_get_set_value': ['propext'], 'Solidity.Backend.InternalFlow.CallerView.storage_assign_environment': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerView.scalar_assign_storage_alias': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerView.mixed_store_alias': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.alias_frame': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.exact_body_result': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.final_slot': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix.wrong_element_after_suffix': ['Classical.choice', 'Quot.sound', 'propext']}
PATTERN = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)", text):
        raise ValueError("diagnostic or untrusted axiom in builtin audit")
    reports = [(n, sorted(x.strip() for x in a.split(',') if x.strip()))
               for n, a in re.findall(PATTERN, text)]
    expected = [(n, PINS[n]) for n in NAMES]
    if reports != expected:
        raise ValueError("missing, reordered, duplicate or changed mixed-store-alias axiom report")
    return len(reports)
if __name__ == '__main__':
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'pass', 'actual_builtin_reports': count}))
