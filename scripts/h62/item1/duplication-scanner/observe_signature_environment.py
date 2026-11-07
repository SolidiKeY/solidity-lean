#!/usr/bin/env python3
"""Compare fixture-local post-import artifact observations, not attestations."""
import argparse
import hashlib
import importlib.util
import json
import os
import stat
import sys
from pathlib import Path

PREFIX = "H62_ENVIRONMENT "
SIG_PREFIX = "H62_SIGNATURE "
MAX_LOG = 16 * 1024 * 1024
MODULE_FIELDS = {"module", "importAll", "isExported", "isMeta", "irPhases",
                 "base", "base_real", "server", "server_present", "server_real",
                 "private", "private_present", "private_real"}
ENV_FIELDS = {"format", "kind", "lean_version", "main_module", "is_module",
              "trust_level", "search_path", "direct_imports", "modules"}
IMPORT_FIELDS = {"module", "importAll", "isExported", "isMeta"}
REQUIRED_EXTRAS = {"lean_command_path", "lake_command_path", "lean_toolchain", "fingerprint_source",
                   "environment_source", "probe_source", "consumer_source", "record_checker",
                   "expected_records", "snapshot_tool", "driver", "fingerprint_olean",
                   "environment_olean", "checkout_head", "checkout_status"}

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result

def reject_number(_):
    raise ValueError("non-integer JSON number")

def json_load(raw):
    return json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object,
                      parse_constant=reject_number, parse_float=reject_number)

def read_log_bytes(path, expected_sha256=None, max_bytes=None):
    """Guard parsed output detached from the successful process's exact bytes.

    An omitted hash is an explicitly unbound offline observation. Live producers
    supply the hash from their in-memory completed step, never a saved packet.
    """
    limit = MAX_LOG if max_bytes is None else max_bytes
    if type(limit) is not int or limit < 1:
        raise ValueError("invalid observation byte limit")
    if expected_sha256 is not None and not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError("nonregular observation log")
    if expected_sha256 is not None and (not isinstance(expected_sha256,str) or
            len(expected_sha256)!=64 or any(c not in "0123456789abcdef" for c in expected_sha256)):
        raise ValueError("invalid expected log SHA256")
    with path.open("rb") as stream:
        raw = stream.read(limit + 1)
    if len(raw) > limit:
        raise ValueError("observation log exceeds byte limit")
    if expected_sha256 is not None and hashlib.sha256(raw).hexdigest()!=expected_sha256:
        raise ValueError("observation log differs from checked process output")
    return raw


def read_log(path, expected_sha256=None):
    raw = read_log_bytes(path, expected_sha256)
    lines = raw.decode("utf-8").splitlines()
    env_lines = [line for line in lines if line.startswith(PREFIX)]
    signature_lines = [line for line in lines if line.startswith(SIG_PREFIX)]
    if len(env_lines) != 1 or len(env_lines) + len(signature_lines) != len(lines):
        raise ValueError("unexpected observation log lines")
    return json_load(env_lines[0][len(PREFIX):].encode()), signature_lines, hashlib.sha256(raw).hexdigest()

def name_parts(value):
    if value == ["anonymous"]:
        return ()
    if not isinstance(value, list) or len(value) != 3 or value[0] != "str" or not isinstance(value[2], str):
        raise ValueError("unsupported module name")
    prefix = name_parts(value[1])
    part = value[2]
    if (not part or part in (".", "..") or "/" in part or "\\" in part or
        any(ord(ch) < 32 or ord(ch) == 127 for ch in part)):
        raise ValueError("unsafe module name component")
    return prefix + (part,)

def validate_import(value, effective=False):
    expected = IMPORT_FIELDS | (MODULE_FIELDS - IMPORT_FIELDS if effective else set())
    if not isinstance(value, dict) or set(value) != expected:
        raise ValueError("malformed import record")
    name = name_parts(value["module"])
    if not name:
        raise ValueError("anonymous module")
    if any(type(value[k]) is not bool for k in ("importAll", "isExported", "isMeta")):
        raise ValueError("malformed import flags")
    if effective and value["irPhases"] not in ("runtime", "comptime", "all"):
        raise ValueError("unknown IR phase")
    return name

def lstat_optional(path):
    try:
        return path.lstat()
    except FileNotFoundError:
        return None

def regular_hash(path, expected_real=None):
    if not path.is_absolute():
        raise ValueError("artifact path must be absolute")
    initial_link = lstat_optional(path)
    if initial_link is None:
        raise ValueError("missing artifact: " + str(path))
    if not (stat.S_ISREG(initial_link.st_mode) or stat.S_ISLNK(initial_link.st_mode)):
        raise ValueError("nonregular artifact: " + str(path))
    real = path.resolve(strict=True)
    if expected_real is not None and str(real) != expected_real:
        raise ValueError("artifact realpath mismatch")
    link_target = os.readlink(path) if stat.S_ISLNK(initial_link.st_mode) else None
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        before = os.fstat(stream.fileno())
        if not stat.S_ISREG(before.st_mode):
            raise ValueError("artifact is not regular")
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
        after = os.fstat(stream.fileno())
    final_link = lstat_optional(path)
    final_stat = path.stat()
    fingerprint = lambda x: (x.st_dev, x.st_ino, x.st_size, x.st_mtime_ns, x.st_ctime_ns)
    if (final_link is None or fingerprint(initial_link) != fingerprint(final_link) or
        fingerprint(before) != fingerprint(after) or fingerprint(after) != fingerprint(final_stat) or
        path.resolve(strict=True) != real):
        raise ValueError("artifact changed during read")
    return {"path": str(path), "realpath": str(real), "symlink": link_target,
            "size": before.st_size, "sha256": digest.hexdigest()}

def optional_hash(path, present, expected_real):
    status = lstat_optional(path)
    if type(present) is not bool or (status is not None) != present:
        raise ValueError("sidecar presence mismatch")
    if not present:
        if expected_real is not None:
            raise ValueError("absent sidecar has realpath")
        return {"path": str(path), "present": False}
    if not isinstance(expected_real, str):
        raise ValueError("missing sidecar realpath")
    return {"present": True, **regular_hash(path, expected_real)}

def root_exists(path):
    info = lstat_optional(path)
    if info is None:
        return False
    try:
        target = path.stat()
    except OSError as exc:
        raise ValueError("unreadable search root") from exc
    if stat.S_ISDIR(target.st_mode):
        return True
    if path.name.endswith(".olean") and stat.S_ISREG(target.st_mode):
        return True
    raise ValueError("nonregular search root")

def capture_environment(environment, extras=None):
    if not isinstance(environment, dict) or set(environment) != ENV_FIELDS:
        raise ValueError("malformed environment record")
    if (type(environment["format"]) is not int or environment["format"] != 1 or
        environment["kind"] != "fixture-local-observation" or
        environment["lean_version"] != "4.24.0" or
        type(environment["is_module"]) is not bool or type(environment["trust_level"]) is not int or
        not 0 <= environment["trust_level"] <= 4294967295):
        raise ValueError("environment header")
    name_parts(environment["main_module"])
    paths = environment["search_path"]
    if not isinstance(paths, list) or not paths or any(not isinstance(p, str) or not Path(p).is_absolute() for p in paths):
        raise ValueError("malformed search path")
    roots = []
    for raw in paths:
        real = Path(raw).resolve(strict=True)
        if not real.is_dir():
            raise ValueError("search path is not a directory")
        if real not in roots:
            roots.append(real)
    direct = environment["direct_imports"]
    modules = environment["modules"]
    if not isinstance(direct, list) or not direct or not isinstance(modules, list) or not modules or len(modules) > 10000:
        raise ValueError("empty or oversized import list")
    direct_names = [validate_import(row) for row in direct]
    names = [validate_import(row, effective=True) for row in modules]
    if (len(set(names)) != len(names) or len(set(direct_names)) != len(direct_names) or
        not set(direct_names).issubset(set(names))):
        raise ValueError("duplicate or missing module")
    artifacts = []
    seen_real = set()
    for row, name in zip(modules, names):
        matching = [root for root in roots
                    if root_exists(root / name[0]) or root_exists(Path(str(root / name[0]) + ".olean"))]
        if len(matching) != 1:
            raise ValueError("missing or shadowed package root")
        expected = Path(str(matching[0].joinpath(*name)) + ".olean")
        base = Path(row["base"]) if isinstance(row["base"], str) else Path()
        if not base.is_absolute() or base.resolve(strict=True) != expected.resolve(strict=True):
            raise ValueError("resolved module path mismatch")
        if not isinstance(row["base_real"], str):
            raise ValueError("missing resolved module realpath")
        base_item = regular_hash(base, row["base_real"])
        if base_item["realpath"] in seen_real:
            raise ValueError("duplicate module artifact")
        seen_real.add(base_item["realpath"])
        if row["server"] != str(base) + ".server" or row["private"] != str(base) + ".private":
            raise ValueError("sidecar path mismatch")
        server = optional_hash(Path(row["server"]), row["server_present"], row["server_real"])
        private = optional_hash(Path(row["private"]), row["private_present"], row["private_real"])
        artifacts.append({"module": row["module"], "base": base_item, "server": server,
                          "private": private,
                          "private_loader_candidate": server["present"] and private["present"]})
    extra_items = {}
    if extras is not None:
        if set(extras) != REQUIRED_EXTRAS:
            raise ValueError("missing or unexpected fixture extra")
        extra_items = {label: regular_hash(path) for label, path in sorted(extras.items())}
        by_module = {name_parts(item["module"]): item["base"] for item in artifacts}
        for label, module in (("fingerprint_olean", ("SignatureFingerprint",)),
                              ("environment_olean", ("SignatureEnvironment",))):
            if module not in by_module or extra_items[label]["realpath"] != by_module[module]["realpath"] or extra_items[label]["sha256"] != by_module[module]["sha256"]:
                raise ValueError("fixture olean does not match observed module")
    return {"kind": "fixture-local-post-import-snapshot-not-attestation",
            "environment": environment, "artifacts": artifacts, "extras": extra_items,
            "extra_path_provenance": "caller-supplied"}

def load_snapshot(path):
    with path.open("rb") as stream:
        raw = stream.read(MAX_LOG + 1)
    if len(raw) > MAX_LOG:
        raise ValueError("snapshot exceeds byte limit")
    return json_load(raw)

def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)

def verify_observation(before, observed, after):
    if not isinstance(observed, dict) or set(observed) != ENV_FIELDS:
        raise ValueError("malformed consumer observation")
    if (not isinstance(before, dict) or set(before) != {"kind", "environment", "artifacts", "extras", "extra_path_provenance"} or
        before.get("kind") != "fixture-local-post-import-snapshot-not-attestation" or
        before.get("extra_path_provenance") != "caller-supplied"):
        raise ValueError("wrong snapshot kind")
    if canonical(before) != canonical(after):
        raise ValueError("before/after artifact snapshots differ")
    extras = before["extras"]
    if not isinstance(extras, dict):
        raise ValueError("malformed snapshot extras")
    paths = None
    if extras:
        if set(extras) != REQUIRED_EXTRAS or any(not isinstance(item, dict) or not isinstance(item.get("path"), str) for item in extras.values()):
            raise ValueError("malformed snapshot extras")
        paths = {label: Path(item["path"]) for label, item in extras.items()}
    current_snapshot = capture_environment(before["environment"], paths)
    if canonical(before) != canonical(current_snapshot):
        raise ValueError("snapshot does not match current artifacts")
    old = dict(before["environment"])
    current = dict(observed)
    old_main = name_parts(old.pop("main_module"))
    current_main = name_parts(current.pop("main_module"))
    if old_main != ("SignatureEnvironmentProbe",) or current_main != ("SignatureObservedConsumer",):
        raise ValueError("unexpected fixture main module")
    if canonical(old) != canonical(current):
        raise ValueError("consumer environment observation differs")
    return {"kind": "fixture-local-observation-not-attestation",
            "environment_binding": "unbound", "extra_path_provenance": "caller-supplied",
            "modules": len(before["artifacts"])}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("capture", "verify"))
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--extra", action="append", default=[], help="fixture input as label=absolute-path")
    args = parser.parse_args()
    try:
        if args.action == "capture" and len(args.paths) == 1:
            environment, signatures, log_hash = read_log(args.paths[0])
            if signatures:
                raise ValueError("probe must not contain signature records")
            extras = {}
            for item in args.extra:
                label, sep, path = item.partition("=")
                if not sep or not label or label in extras or not Path(path).is_absolute():
                    raise ValueError("malformed fixture extra")
                extras[label] = Path(path)
            if set(extras) != REQUIRED_EXTRAS:
                raise ValueError("capture requires every fixture extra")
            result = {"snapshot": capture_environment(environment, extras),
                      "observation_log_sha256": log_hash}
        elif args.action == "verify" and len(args.paths) == 5 and not args.extra:
            before_path, before_log, observed_log, after_log, after_path = args.paths
            before, after = load_snapshot(before_path), load_snapshot(after_path)
            for envelope, log in ((before, before_log), (after, after_log)):
                if not isinstance(envelope, dict) or set(envelope) != {"snapshot", "observation_log_sha256"}:
                    raise ValueError("malformed snapshot envelope")
                env, probe_signatures, log_hash = read_log(log)
                if probe_signatures or envelope["observation_log_sha256"] != log_hash:
                    raise ValueError("probe log hash mismatch")
                if not isinstance(envelope["snapshot"], dict) or canonical(envelope["snapshot"].get("environment")) != canonical(env):
                    raise ValueError("probe log environment mismatch")
                extras = envelope["snapshot"].get("extras")
                if not isinstance(extras, dict) or set(extras) != REQUIRED_EXTRAS:
                    raise ValueError("missing fixture extras")
            observed, signatures, observed_hash = read_log(observed_log)
            repo = Path(__file__).resolve().parents[4]
            source_dir = repo / "tests/h62/item1/duplication-scanner"
            fixed = {"fingerprint_source": source_dir / "SignatureFingerprint.lean",
                     "environment_source": source_dir / "SignatureEnvironment.lean",
                     "probe_source": source_dir / "SignatureEnvironmentProbe.lean",
                     "consumer_source": source_dir / "SignatureObservedConsumer.lean",
                     "record_checker": source_dir / "check_signature_records.py",
                     "expected_records": source_dir / "signature-records.expected.jsonl",
                     "snapshot_tool": Path(__file__).resolve(),
                     "driver": repo / "scripts/h62/item1/duplication-scanner/check_signature_fixture.sh",
                     "lean_toolchain": repo / "lean-toolchain"}
            extras = before["snapshot"]["extras"]
            for label, expected in fixed.items():
                if not isinstance(extras[label], dict) or extras[label].get("realpath") != str(expected.resolve(strict=True)):
                    raise ValueError("fixture extra path mismatch: " + label)
            spec = importlib.util.spec_from_file_location("h62_records", source_dir / "check_signature_records.py")
            checker = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(checker)
            checker.validate("\n".join(signatures))
            result = verify_observation(before["snapshot"], observed, after["snapshot"])
            result["probe_before_sha256"] = before["observation_log_sha256"]
            result["consumer_log_sha256"] = observed_hash
            result["probe_after_sha256"] = after["observation_log_sha256"]
        else:
            parser.error("capture requires one path; verify requires five")
    except (OSError, ValueError, UnicodeError, RecursionError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))

if __name__ == "__main__":
    main()
