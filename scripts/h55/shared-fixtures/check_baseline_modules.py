"""Validate pinned original declaration records for each audited module."""
import hashlib
import json
from collections import defaultdict
from pathlib import Path

PINS = Path(__file__).resolve().parents[3] / "tests/h55/shared-fixtures/baseline_modules.json"

def check(rows, group):
    pins = json.loads(PINS.read_text())[group]
    records = defaultdict(list)
    for (module, _), row in rows.items():
        records[module].append(row)
    if set(records) != set(pins):
        raise ValueError("baseline module set differs from pinned inventory")
    for module, entries in records.items():
        payload = json.dumps(sorted(entries, key=lambda row: row["name"]), sort_keys=True,
                             separators=(",", ":"), ensure_ascii=True).encode()
        if {"count": len(entries), "records_sha256": hashlib.sha256(payload).hexdigest()} != pins[module]:
            raise ValueError(f"baseline declarations differ from pin: {module}")
