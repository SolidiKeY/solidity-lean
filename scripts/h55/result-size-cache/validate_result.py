#!/usr/bin/env python3
"""Validate exactly one marked CLOUDVM-RESULT against the adjacent schema."""
import argparse
import json
from pathlib import Path
import sys

try:
    import jsonschema
except ImportError:
    jsonschema = None

SCHEMA = Path(__file__).with_name("result_schema.json")
START = "CLOUDVM-RESULT"
END = "END-CLOUDVM-RESULT"


class ResultError(ValueError):
    pass


def reject_duplicate(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ResultError("duplicate JSON key " + repr(key))
        result[key] = value
    return result


def reject_constant(value):
    raise ResultError("non-JSON constant " + value)


def validate(text, schema_path=SCHEMA):
    if jsonschema is None:
        raise ResultError("jsonschema dependency unavailable")
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if line == START]
    ends = [i for i, line in enumerate(lines) if line == END]
    if len(starts) != 1 or len(ends) != 1 or starts[0] >= ends[0]:
        raise ResultError("expected exactly one ordered marker pair on separate lines")
    body = "\n".join(lines[starts[0]+1:ends[0]])
    try:
        result = json.loads(body, object_pairs_hook=reject_duplicate, parse_constant=reject_constant)
    except RecursionError as exc:
        raise ResultError("JSON nesting too deep") from exc
    except json.JSONDecodeError as exc:
        raise ResultError(f"JSON line {exc.lineno} column {exc.colno}: {exc.msg}") from exc
    try:
        schema = json.loads(Path(schema_path).read_text(encoding="utf-8"), object_pairs_hook=reject_duplicate, parse_constant=reject_constant)
        jsonschema.Draft202012Validator.check_schema(schema)
    except (OSError, UnicodeError, json.JSONDecodeError, jsonschema.exceptions.SchemaError, RecursionError) as exc:
        raise ResultError("schema unavailable or invalid: " + str(exc)) from exc
    errors = sorted(jsonschema.Draft202012Validator(schema).iter_errors(result), key=lambda e: (list(map(str, e.absolute_path)), e.message))
    if errors:
        error = errors[0]
        path = "$" + "".join(f"[{p}]" if isinstance(p, int) else "." + p for p in error.absolute_path)
        raise ResultError(path + ": " + error.message)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", nargs="?", help="message file; stdin if omitted")
    args = parser.parse_args()
    try:
        text = Path(args.file).read_text(encoding="utf-8") if args.file else sys.stdin.read()
        validate(text)
    except (ResultError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print("CLOUDVM-RESULT invalid: " + str(exc), file=sys.stderr)
        return 1
    print("CLOUDVM-RESULT valid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
