#!/usr/bin/env python3
"""Guard H97 minimal-envelope rejection and versioned legacy-fallback regressions.

Validate one marked report. Schema checks are cached by exact source contents,
so edits or missing schema files cannot reuse stale validation. No host adoption
or owner agreement is established by envelope validation.
"""
import argparse
from functools import lru_cache
import json
import math
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


def finite_float(value):
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ResultError("non-finite JSON number")
    return parsed


def reject_constant(value):
    raise ResultError("non-JSON constant " + value)


@lru_cache(maxsize=8)
def checked_schema(source):
    schema = json.loads(source, object_pairs_hook=reject_duplicate, parse_constant=reject_constant, parse_float=finite_float)
    jsonschema.Draft202012Validator.check_schema(schema)
    root = jsonschema.Draft202012Validator(schema)
    profiles = {}
    definitions = schema.get('$defs', {}) if isinstance(schema, dict) else {}
    if isinstance(definitions, dict) and {'legacy', 'h97'} <= definitions.keys():
        for name in ('legacy', 'h97'):
            profiles[name] = jsonschema.Draft202012Validator({'$defs': definitions, '$ref': '#/$defs/' + name})
    elif isinstance(definitions, dict) and {'legacyRules', 'h97Rules'} <= definitions.keys():
        shared = {key: value for key, value in schema.items() if key != 'anyOf'}
        for name in ('legacy', 'h97'):
            profiles[name] = jsonschema.Draft202012Validator({**shared, '$ref': '#/$defs/' + name + 'Rules'})
    return schema, root, profiles


def validation_errors(root, profiles, schema, result):
    # The complete union decides acceptance; profile selection only improves errors.
    errors = list(root.iter_errors(result))
    if errors and profiles:
        legacy_fields = {'base', 'repository', 'checkpoints', 'artifacts'}
        legacy_first = isinstance(result, dict) and 'schema_version' not in result and legacy_fields <= result.keys()
        for name in (('legacy', 'h97') if legacy_first else ('h97', 'legacy')):
            detailed = list(profiles[name].iter_errors(result))
            if detailed:
                errors = detailed
                break
    return sorted(errors, key=lambda e: (list(map(str, e.absolute_path)), e.message))


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
        result = json.loads(body, object_pairs_hook=reject_duplicate, parse_constant=reject_constant, parse_float=finite_float)
    except RecursionError as exc:
        raise ResultError("JSON nesting too deep") from exc
    except json.JSONDecodeError as exc:
        raise ResultError(f"JSON line {exc.lineno} column {exc.colno}: {exc.msg}") from exc
    except ResultError:
        raise
    except ValueError as exc:
        raise ResultError("JSON value exceeds decoder limits") from exc
    try:
        source = Path(schema_path).read_text(encoding="utf-8")
        schema, root, profiles = checked_schema(source)
    except (OSError, UnicodeError, ValueError, jsonschema.exceptions.SchemaError, RecursionError) as exc:
        raise ResultError("schema unavailable or invalid: " + str(exc)) from exc
    try:
        errors = validation_errors(root, profiles, schema, result)
    except RecursionError as exc:
        raise ResultError("schema validation nesting too deep") from exc
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
