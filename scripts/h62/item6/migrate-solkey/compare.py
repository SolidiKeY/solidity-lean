#!/usr/bin/env python3
"""Fail closed on missing runs, changed settings/order, or wall/RSS regression."""
import argparse
import json
from pathlib import Path


def compare(old, new):
    for label, run in [('old', old), ('new', new)]:
        if any(m['exit'] != 0 or m['stop'] for m in run['modules']):
            raise ValueError(label+' run is incomplete or failed')
        if not run['modules'] or not run.get('complete', False):
            raise ValueError(label+' run has no complete closure marker')
    if old['settings'] != new['settings']: raise ValueError('resource/cache settings differ')
    if [m['module'] for m in old['modules']] != [m['module'] for m in new['modules']]:
        raise ValueError('module sets/order differ')
    if old['source_identity_sha256'] != new['source_identity_sha256']:
        raise ValueError('source/fixture inputs differ')
    result = {}
    for metric in ['wall_seconds', 'max_child_rss_kib']:
        delta = (new[metric]/old[metric]-1)*100
        result[metric+'_delta_percent'] = delta
    worst = max(result.values())
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
