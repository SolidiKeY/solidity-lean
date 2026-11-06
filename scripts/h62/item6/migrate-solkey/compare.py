#!/usr/bin/env python3
"""Fail closed on missing runs, changed settings/order, or wall/RSS regression."""
import argparse
from decimal import Decimal
import json
from pathlib import Path


def compare(old, new):
    for label, run in [('old', old), ('new', new)]:
        if any(m['exit'] != 0 or m['stop'] for m in run['modules']):
            raise ValueError(label+' run is incomplete or failed')
        if not run['modules'] or run.get('complete') is not True:
            raise ValueError(label+' run has no complete closure marker')
    if not old.get('tooling_sha256') or old['tooling_sha256'] != new.get('tooling_sha256'):
        raise ValueError('measurement/census tooling differs or is unrecorded')
    if any(run['settings'].get('mode') != 'assigned-closure' for run in [old,new]):
        raise ValueError('clean-build acceptance requires assigned-closure runs')
    if old['settings'] != new['settings']: raise ValueError('resource/cache settings differ')
    if [m['module'] for m in old['modules']] != [m['module'] for m in new['modules']]:
        raise ValueError('module sets/order differ')
    if old['source_identity_sha256'] != new['source_identity_sha256']:
        raise ValueError('source/fixture inputs differ')
    result, deltas = {}, []
    for metric in ['wall_seconds', 'max_child_rss_kib']:
        before, after = Decimal(str(old[metric])), Decimal(str(new[metric]))
        if not before.is_finite() or not after.is_finite() or before <= 0 or after <= 0:
            raise ValueError('invalid measurement: '+metric)
        delta = (after/before-1)*100
        deltas.append(delta)
        result[metric+'_delta_percent'] = float(delta)
    worst = max(deltas)
    result['status'] = 'STOP_GT_10_PERCENT' if worst > 10 else 'ESCALATE_REGRESSION' if worst > 0 else 'NO_REGRESSION'
    return result


def main():
    p = argparse.ArgumentParser()
    p.add_argument('old', type=Path)
    p.add_argument('new', type=Path)
    a = p.parse_args()
    try: result = compare(json.loads(a.old.read_text()), json.loads(a.new.read_text()))
    except (KeyError, ValueError) as e: raise SystemExit(str(e))
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['status'] == 'NO_REGRESSION' else 1)

if __name__ == '__main__': main()
