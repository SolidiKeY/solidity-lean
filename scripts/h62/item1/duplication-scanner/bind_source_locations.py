#!/usr/bin/env python3
"""Guard namespace guesses, ambiguous ranges and generated aliases in binding.

Only live pinned fixture execution authorizes local source/signature links.
Direct compiler metadata and exact source positions join names to lexical rows;
missing or ambiguous metadata stays unresolved. No general ownership, private
artifact, proof-body equivalence or remote-attestation claim follows.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess

import bind_signature_fixture as binder
import census_fixture_kernel as kernel

PINS = binder.FIXTURES / "source-location-pins.json"
PREFIX = "H62_SOURCE_LOCATIONS "
KINDS = {"theorem": "theorem", "lemma": "theorem", "def": "definition", "abbrev": "definition",
         "opaque": "opaque", "inductive": "inductive", "structure": "inductive", "class": "inductive",
         "axiom": "axiom", "constant": "axiom"}


def source_slice(source, location):
    """Position.line is one-based; column counts Unicode codepoints, not UTF-16."""
    if not isinstance(location, dict) or set(location) != {"start", "end", "range_start", "range_end"}:
        raise ValueError("malformed direct location")
    lines = source.split("\n")
    def point(value):
        if (not isinstance(value, dict) or set(value) != {"line", "column"}
            or type(value["line"]) is not int or type(value["column"]) is not int
            or not 1 <= value["line"] <= len(lines) or value["column"] < 0):
            raise ValueError("invalid source position")
        line = lines[value["line"]-1]
        if value["column"] > len(line):
            raise ValueError("source column outside line")
        return (value["line"], value["column"])
    start, end = point(location["start"]), point(location["end"])
    whole_start, whole_end = point(location["range_start"]), point(location["range_end"])
    if not whole_start <= start < end <= whole_end:
        raise ValueError("invalid source range nesting")
    first, last = start[0]-1, end[0]-1
    if first == last:
        return lines[first][start[1]:end[1]]
    return "\n".join([lines[first][start[1]:], *lines[first+1:last], lines[last][:end[1]]])


def join_locations(source, lexical, census, locations, expected_module=kernel.MODULE):
    """Structural join, not independent authentication of a saved census."""
    if (not isinstance(locations, dict) or set(locations) != {"format", "module", "rows"}
        or type(locations["format"]) is not int or locations["format"] != 1
        or locations["module"] != expected_module or not isinstance(locations["rows"], list)):
        raise ValueError("location census header")
    known = {kernel.name_key(row["declaration"]): row for row in kernel.validate(census, expected_module)["rows"]}
    reported = {}
    for row in locations["rows"]:
        if not isinstance(row, dict) or set(row) != {"declaration", "selection"}:
            raise ValueError("location row fields")
        key = kernel.name_key(row["declaration"])
        if key in reported:
            raise ValueError("duplicate location declaration")
        reported[key] = row
    if set(reported) != set(known):
        raise ValueError("location/kernel constant coverage mismatch")
    index = {}
    for key, row in reported.items():
        if row["selection"] is None:
            continue
        fragment = source_slice(source, row["selection"])
        # Direct generated aliases may point to a parent name. Do not attach those.
        if key[-1] != ("str", fragment):
            continue
        index.setdefault((row["selection"]["start"]["line"], fragment), []).append(key)
    joined = []; linked = set()
    for row in lexical:
        candidates = index.get((row["line"], row["name"]), [])
        result = {k:row[k] for k in ("path", "line", "name", "kind", "reject_reason")}
        result["status"] = "no-direct-location-match"
        if len(candidates) > 1:
            result["status"] = "ambiguous-direct-location-match"
        elif candidates:
            key = candidates[0]; declaration = known[key]
            if KINDS.get(row["kind"]) != declaration["kind"]:
                result["status"] = "declaration-kind-mismatch"
            elif declaration["status"] != "serialized":
                result["status"] = "unsupported-signature"
            elif key in linked:
                raise ValueError("multiple lexical rows claim one constant")
            else:
                linked.add(key)
                result.update(status="direct-source-signature-link", declaration=declaration["declaration"],
                              signature=declaration["signature"], selection=reported[key]["selection"])
        joined.append(result)
    return {"basis": "Pinned source bytes plus direct compiler location, exact name/line and declaration kind",
            "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "lexical_total": len(joined), "linked": len(linked),
            "unresolved": len(joined)-len(linked), "rows": joined,
            "visible_kernel_total": len(known),
            "kernel_without_lexical_link": [row["declaration"] for key,row in known.items() if key not in linked],
            "ownership_verified": False, "unloaded_private_artifacts_covered": False}


def read_log(path, expected_sha256=None):
    raw = binder.observer.read_log_bytes(path, expected_sha256)
    lines = raw.decode().splitlines()
    env = [line for line in lines if line.startswith(binder.observer.PREFIX)]
    data = [line for line in lines if line.startswith(PREFIX)]
    if len(env) != 1 or len(data) != 1 or len(lines) != 2:
        raise ValueError("unexpected location log lines")
    return (binder.observer.json_load(env[0][len(binder.observer.PREFIX):].encode()),
            binder.observer.json_load(data[0][len(PREFIX):].encode()))


def read_bound_json(path, expected):
    """Use only exact child bytes committed by the successful live return value."""
    if binder.regular(path)["sha256"] != expected:
        raise ValueError("live child artifact hash mismatch: "+path.name)
    with path.open("rb") as stream:
        raw = stream.read(binder.observer.MAX_LOG+1)
    if len(raw) > binder.observer.MAX_LOG or hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError("live child bytes/hash mismatch: "+path.name)
    def finite_float(text):
        value = float(text)
        if not math.isfinite(value): raise ValueError("non-finite child receipt number")
        return value
    return json.loads(raw,object_pairs_hook=binder.observer.unique_object,
                      parse_constant=binder.observer.reject_number,parse_float=finite_float)


def run(output):
    """Caller holds the writer lease across all fresh builds and checks."""
    pins = json.loads(PINS.read_text()); probe = binder.FIXTURES / "SignatureSourceLocations.lean"
    if binder.regular(probe)["sha256"] != pins["probe_sha256"]:
        raise ValueError("source-location probe pin drift")
    if binder.sha(kernel.PINS) != pins["kernel_census_pins_sha256"]:
        raise ValueError("kernel census contract drift")
    if not output.is_absolute(): raise ValueError("output must be absolute")
    output.mkdir(mode=0o700, exist_ok=False)
    receipt = {"schema":1,"kind":"trusted-live-source-location-binding","status":"failed","steps":[],
               "driver_sha256":binder.sha(Path(__file__)),"probe_sha256":pins["probe_sha256"],"pins_sha256":binder.sha(PINS)}
    try:
        live = kernel.run(output / "kernel")
        live_hash = hashlib.sha256((json.dumps(live,indent=2)+"\n").encode()).hexdigest()
        child_hashes = {output / "kernel/receipt.json": live_hash,
                        output / "kernel/census.json": live["census_sha256"],
                        output / "kernel/rebuild/receipt.json": live["rebuild_receipt_sha256"]}
        children = {path:read_bound_json(path,digest) for path,digest in child_hashes.items()}
        receipt["kernel_receipt_sha256"] = live_hash
        compiler_pins = json.loads(binder.PINS.read_text()); compiler = binder.check_inputs(compiler_pins)
        old_env, _, _ = binder.observer.read_log(output / "kernel/rebuild/logs/consumer.log",binder.expected_log_hash(children[output / "kernel/rebuild/receipt.json"]["steps"],output / "kernel/rebuild/logs/consumer.log"))
        before = binder.observer.capture_environment(old_env)
        rebuild = children[output / "kernel/rebuild/receipt.json"]
        if binder.observer.canonical(before["artifacts"]) != binder.observer.canonical(rebuild["compiled_artifacts"]):
            raise ValueError("artifacts changed before location probe")
        runtime = binder.runtime_files(compiler); companions = binder.companion_artifacts(before["artifacts"])
        staged = output / probe.name; staged.write_bytes(probe.read_bytes()); staged.chmod(0o444)
        if binder.regular(staged)["sha256"] != pins["probe_sha256"]:
            raise ValueError("staged location probe pin drift")
        env = dict(binder.clean_environment(compiler),LEAN_PATH=str(output / "kernel/rebuild/compiled"))
        log = output / "locations.log"
        binder.checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(output),str(staged)],env,log,receipt["steps"])
        observed, locations = read_log(log,binder.expected_log_hash(receipt["steps"],log))
        a, b = dict(old_env), dict(observed)
        if binder.observer.name_parts(a.pop("main_module")) != ("SignatureObservedConsumer",) or binder.observer.name_parts(b.pop("main_module")) != ("SignatureSourceLocations",):
            raise ValueError("unexpected location probe module")
        if binder.observer.canonical(a) != binder.observer.canonical(b):
            raise ValueError("location probe import environment drift")
        after = binder.observer.capture_environment(observed)
        if binder.observer.canonical(before["artifacts"]) != binder.observer.canonical(after["artifacts"]) or companions != binder.companion_artifacts(after["artifacts"]) or runtime != binder.runtime_files(compiler):
            raise ValueError("location probe dependency/runtime drift")
        source_path = binder.FIXTURES / "SignatureFingerprint.lean"
        source = source_path.read_bytes()
        if hashlib.sha256(source).hexdigest() != compiler_pins["fixture_sources"][source_path.name]:
            raise ValueError("source changed before source-location join")
        lexical = binder.scanner.scan(source_path,binder.ROOT,source)
        census = children[output / "kernel/census.json"]
        joined = join_locations(source.decode(),lexical,census,locations)
        binder.check_inputs(compiler_pins)
        for path,digest in child_hashes.items(): read_bound_json(path,digest)
        if binder.regular(probe)["sha256"] != pins["probe_sha256"] or binder.regular(staged)["sha256"] != pins["probe_sha256"]:
            raise ValueError("location probe source drift")
        (output / "source-bindings.json").write_text(json.dumps(joined,sort_keys=True,indent=2)+"\n")
        binder.verify_process_logs(receipt["steps"]); binder.verify_process_logs(live["steps"])
        binder.verify_process_logs(children[output / "kernel/rebuild/receipt.json"]["steps"])
        receipt.update(status="pass",lexical_total=joined["lexical_total"],linked=joined["linked"],unresolved=joined["unresolved"],
                       source_sha256=joined["source_sha256"],bindings_sha256=binder.sha(output / "source-bindings.json"),
                       boundary="Trusted live pinned fixture source/name/type linkage only. No ownership, unloaded/private levels, global coverage, proof-body equality or remote attestation.")
    except Exception as exc:
        receipt["error"] = str(exc); raise
    finally:
        (output / "receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument("--output",type=Path,required=True);args=parser.parse_args()
    try:
        with binder.writer_lease(): result = run(args.output)
    except (OSError,ValueError,RecursionError,subprocess.SubprocessError) as exc:
        parser.exit(1,"SOURCE_LOCATION_REJECT: "+str(exc)+"\n")
    print("LOCAL_SOURCE_LOCATION_PASS "+json.dumps({k:result[k] for k in ("lexical_total","linked","unresolved")}))


if __name__ == "__main__": main()
