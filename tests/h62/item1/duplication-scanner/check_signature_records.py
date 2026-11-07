#!/usr/bin/env python3
"""Check the fixed isolated Lean consumer controls; these records are unbound."""
import copy
import hashlib
import json
import sys
from pathlib import Path

PREFIX = "H62_SIGNATURE "
NAMES = ("alphaA", "alphaB", "differentType", "indexedOne", "indexedTwo")
ORIGIN = ["imported", ["str", ["anonymous"], "SignatureFingerprint"]]
EXPECTED_SHA256 = "920fb1bd55f1abbeeffc000811d5c5e989f94c7446f235fd458a10ca61956b5a"
EXPECTED_PATH = Path(__file__).with_name("signature-records.expected.jsonl")

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result

def reject_number(_):
    raise ValueError("non-integer JSON number")

def parse_record(line):
    if not line.startswith(PREFIX):
        raise ValueError("missing record prefix")
    return json.loads(line[len(PREFIX):], object_pairs_hook=unique_object,
                      parse_constant=reject_number, parse_float=reject_number)

def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)

def name_record(name):
    return ["str", ["str", ["str", ["anonymous"], "H62Signature"], "Controls"], name]

def validate(text):
    lines = text.splitlines()
    if len(lines) != len(NAMES) or any(not line.startswith(PREFIX) for line in lines):
        raise ValueError("expected exactly five signature records")
    records = [parse_record(line) for line in lines]
    expected_bytes = EXPECTED_PATH.read_bytes()
    if hashlib.sha256(expected_bytes).hexdigest() != EXPECTED_SHA256:
        raise ValueError("fixture hash mismatch")
    expected_lines = expected_bytes.decode("utf-8").splitlines()
    if len(expected_lines) != len(NAMES):
        raise ValueError("fixture record count")
    expected = [parse_record(line) for line in expected_lines]
    if canonical(records) != canonical(expected):
        raise ValueError("records differ from pinned fixture")
    by_name = {}
    for record in records:
        if not isinstance(record, dict) or set(record) != {
            "declaration", "environment_binding", "format", "lean_version", "origin", "signature"
        }:
            raise ValueError("record fields")
        if (type(record["format"]) is not int or record["format"] != 1 or
            record["lean_version"] != "4.24.0" or
            record["environment_binding"] != "unbound" or record["origin"] != ORIGIN):
            raise ValueError("record provenance")
        matches = [name for name in NAMES if record["declaration"] == name_record(name)]
        if len(matches) != 1 or matches[0] in by_name:
            raise ValueError("record identity")
        signature = record["signature"]
        if not isinstance(signature, list) or len(signature) != 3 or signature[0] != "declaration-type":
            raise ValueError("signature shape")
        by_name[matches[0]] = signature
    if set(by_name) != set(NAMES):
        raise ValueError("missing record")
    if by_name["alphaA"] != by_name["alphaB"]:
        raise ValueError("renamed binders differ")
    if by_name["alphaA"] == by_name["differentType"]:
        raise ValueError("different intrinsic types conflated")
    if by_name["indexedOne"] == by_name["indexedTwo"]:
        raise ValueError("different intrinsic indices conflated")
    return records

def encode(records):
    return "\n".join(PREFIX + json.dumps(record, ensure_ascii=False, separators=(",", ":"))
                     for record in records)

def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: check_signature_records.py CONSUMER_LOG")
    text = Path(sys.argv[1]).read_text(encoding="utf-8")
    records = validate(text)
    mutations = []
    mutations.append(records[:-1])
    mutations.append(records + [records[0]])
    bad = copy.deepcopy(records)
    bad[0]["environment_binding"] = "verified"
    mutations.append(bad)
    bad = copy.deepcopy(records)
    bad[2]["signature"] = copy.deepcopy(bad[0]["signature"])
    mutations.append(bad)
    bad = copy.deepcopy(records)
    bad[4]["signature"] = copy.deepcopy(bad[3]["signature"])
    mutations.append(bad)
    bad = copy.deepcopy(records)
    for record, value in zip(bad, ("A", "A", "B", "C", "D")):
        record["signature"] = ["declaration-type", 0, value]
    mutations.append(bad)
    bad = copy.deepcopy(records)
    bad[0]["format"] = True
    mutations.append(bad)
    bad = copy.deepcopy(records)
    bad.reverse()
    mutations.append(bad)
    for mutation in mutations:
        try:
            validate(encode(mutation))
        except ValueError:
            continue
        raise SystemExit("negative control accepted")
    duplicate = text.replace('"format":1', '"format":1,"format":1', 1)
    nonfinite = text.replace('"format":1', '"format":NaN', 1)
    for invalid in (duplicate, nonfinite):
        try:
            validate(invalid)
        except ValueError:
            continue
        raise SystemExit("invalid JSON control accepted")
    print("PASS: five pinned fixture records; eight mutations and two JSON refusals; environment unbound")

if __name__ == "__main__":
    main()
