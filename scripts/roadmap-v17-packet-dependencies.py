#!/usr/bin/env python3
"""Lexical, hash-bound packet dependency requests. Not commit or kernel validation."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import resource
import signal

ROOT = Path(__file__).resolve().parents[1]

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value

p = module("v17_packets", ROOT/"scripts/roadmap-v17-packets.py")
k = module("v17_dependency_kernel", ROOT/"scripts/roadmap-v17-kernel.py")


def imports(body):
    result = []
    for line in k.uncomment(body.decode("utf-8", errors="strict")).splitlines():
        line = line.strip()
        if not line: continue
        if line.startswith("import "):
            name = line[7:].strip()
            p.require(k.NAME.fullmatch(name), "unsupported lexical import")
            result.append(name)
        elif line.startswith(("import", "prelude", "module", "public import", "private import")):
            raise ValueError("unsupported lexical header")
        else: break
    return result


def module_path(name):
    p.require(isinstance(name, str) and k.NAME.fullmatch(name), "module name")
    if name.startswith("Solidity."): return name.replace(".", "/")+".lean"
    if name.startswith("SolidityBridge."): return "Bridge/"+name.replace(".", "/")+".lean"
    raise ValueError("unsupported repository module")


def interface_request(packet, expected):
    """Translate a hash-authenticated reference interface's claims, never proof facts."""
    _, bodies = p._inspect(packet, expected)
    p.require("PARALLEL-INTERFACE.json" in bodies, "missing interface")
    interface = p.load(bodies["PARALLEL-INTERFACE.json"])
    p.require(isinstance(interface, dict) and interface.get("kind") == "PARALLEL-INTERFACE",
              "interface kind")
    p.require(interface.get("producer_head") == expected["producerHead"], "interface producer mismatch")
    for flag in ("kernelValidated", "replayValidated", "semanticPremisesDischarged", "releaseClosed"):
        p.require(flag not in interface or interface[flag] is False, "source-only interface promotion")
    sources = interface.get("module_hashes")
    p.require(isinstance(sources, dict) and sources ==
              {path: sha for path, sha in expected["members"].items() if path.endswith(".lean")},
              "interface module inventory mismatch")
    sources = dict(sources)
    direct = interface.get("direct_imports")
    p.require(isinstance(direct, dict) and len(direct) <= 4096, "direct imports shape")
    for name, claim in direct.items():
        path = module_path(name)
        p.require(isinstance(claim, dict) and set(claim) == {"included", "path", "sha256"}
                  and claim["path"] == path and type(claim["included"]) is bool,
                  "direct import mapping")
        p.require(isinstance(claim["sha256"], str) and p.SHA.fullmatch(claim["sha256"]), "direct import digest")
        p.require(claim["included"] == (path in bodies), "direct import inclusion contradiction")
        if path in sources: p.require(sources[path] == claim["sha256"], "direct import hash contradiction")
        sources[path] = claim["sha256"]
    roots = sorted(path[:-5].replace("/", ".") for path in interface["module_hashes"])
    return {"schema": 1, "producerHead": expected["producerHead"],
            "producerBase": interface.get("original_base"), "packetSha256": expected["packetSha256"],
            "roots": roots, "sources": sources}


def reconcile(packet, expected, request, directories, supplementary=None):
    receipt, bodies = p._inspect(packet, expected)
    p.require(isinstance(request, dict) and set(request) ==
              {"schema", "producerHead", "producerBase", "packetSha256", "roots", "sources"},
              "dependency request shape")
    p.require(type(request["schema"]) is int and request["schema"] == 1, "dependency schema")
    p.require(request["producerHead"] == expected["producerHead"] and
              request["packetSha256"] == expected["packetSha256"], "wrong producer/request linkage")
    p.require(isinstance(request["producerBase"], str) and
              re.fullmatch(r"[0-9a-f]{40}", request["producerBase"]), "producer base")
    roots, sources = request["roots"], request["sources"]
    if "PARALLEL-INTERFACE.json" in bodies:
        reference = interface_request(packet, expected)
        p.require(request["producerBase"] == reference["producerBase"], "interface base contradiction")
        p.require(roots == reference["roots"], "interface roots contradiction")
        p.require(isinstance(sources, dict) and all(sources.get(path) == sha
                  for path, sha in reference["sources"].items()), "interface source mismatch")
    p.require(isinstance(roots, list) and 0 < len(roots) <= 16 and
              all(isinstance(x, str) for x in roots) and len(set(roots)) == len(roots), "root list")
    for name in roots: module_path(name)
    p.require(isinstance(sources, dict) and 0 < len(sources) <= 4096, "source inventory")
    for path, sha in sources.items():
        p.safe_path(path)
        p.require(path.endswith(".lean") and isinstance(sha, str) and p.SHA.fullmatch(sha),
                  "source inventory digest")
    packet_sources = {path for path in bodies if path.endswith(".lean")}
    p.require(packet_sources <= set(sources), "packet source omitted from inventory")
    p.require(0 < len(directories) <= 4, "source directory count")
    directories = [Path(d) for d in directories]
    for directory in directories:
        p.require(directory.is_absolute() and directory.is_dir() and
                  directory.resolve() == directory, "noncanonical source directory")
    active, done, used, issues, toolchain = set(), {}, set(), [], set()
    supplementary = supplementary or []
    p.require(isinstance(supplementary, list) and len(supplementary) <= 4, "supplementary archive count")
    p.require(receipt["compressedBytes"]+sum(x["receipt"]["compressedBytes"] for x in supplementary) <= p.COMPRESSED,
              "aggregate compressed archive bound")
    p.require(receipt["rawBytes"]+sum(x["receipt"]["rawBytes"] for x in supplementary) <= p.RAW,
              "aggregate raw archive bound")
    p.require(len(receipt["members"])+sum(len(x["receipt"]["members"]) for x in supplementary) <= 256,
              "aggregate archive member bound")
    for item in supplementary:
        p.require(isinstance(item, dict) and set(item) == {"receipt", "bodies"}, "supplementary shape")
        p.require(item["receipt"].get("status") == "source-bytes-only", "supplementary source receipt")
        for flag in ("kernelValidated", "replayValidated", "releaseClosed", "semanticPremisesDischarged"):
            p.require(item["receipt"].get(flag) is False, "supplementary proof promotion")
        p.require(set(item["bodies"]) == set(item["receipt"]["members"]), "supplementary member linkage")
        for path, body in item["bodies"].items():
            p.require(isinstance(body, bytes) and hashlib.sha256(body).hexdigest() ==
                      item["receipt"]["members"][path], "supplementary source bytes changed")
    reads = []
    measured = {"bytes": 0, "edges": 0}

    def account(data):
        measured["bytes"] += len(data)
        p.require(measured["bytes"] <= p.RAW, "total source byte bound")

    def source(path, sha):
        if path in bodies:
            data = bodies[path]
            account(data)
            if hashlib.sha256(data).hexdigest() != sha:
                issues.append({"path": path, "expectedSha256": sha, "status": "packet-source-mismatch"})
                return None
            return data, "packet"
        candidates = []
        for item in supplementary:
            if path not in item["bodies"]: continue
            data = item["bodies"][path]; account(data)
            digest = hashlib.sha256(data).hexdigest()
            origin = "archive:"+item["receipt"]["packetSha256"]
            candidates.append({"path": origin+":"+path, "actualSha256": digest})
            if digest == sha: return data, origin
        for directory in directories:
            candidate = directory/path
            if not candidate.exists() and not candidate.is_symlink(): continue
            p.require(candidate.resolve() == candidate, "symlinked dependency")
            data = p.stable_read(candidate, p.RAW)
            account(data)
            digest = hashlib.sha256(data).hexdigest()
            candidates.append({"path": str(candidate), "actualSha256": digest})
            if digest == sha:
                reads.append((candidate, digest))
                return data, str(candidate)
        issues.append({"path": path, "expectedSha256": sha,
                       "status": "missing" if not candidates else "hash-mismatch", "candidates": candidates})
        return None

    stack = [(name, False) for name in reversed(roots)]
    while stack:
        name, leaving = stack.pop()
        if leaving:
            active.remove(name)
            continue
        path = module_path(name)
        p.require(name not in active, "circular dependency metadata/imports")
        if name in done: continue
        p.require(len(done) < 4096 and len(active) < 128, "dependency node/depth bound")
        if path not in sources:
            issues.append({"path": path, "status": "missing-required-hash", "importedModule": name})
            done[name] = {"status": "unbound"}
            continue
        used.add(path)
        value = source(path, sources[path])
        if value is None:
            done[name] = {"status": "unavailable"}
            continue
        data, origin = value
        active.add(name)
        deps = imports(data)
        measured["edges"] += len(deps)
        p.require(measured["edges"] <= 16384, "dependency edge bound")
        done[name] = {"path": path, "sha256": sources[path], "origin": origin, "imports": deps}
        stack.append((name, True))
        for dep in reversed(deps):
            if dep.startswith(("Solidity.", "SolidityBridge.")):
                p.require(not (name.startswith("Solidity.") and dep.startswith("SolidityBridge.")),
                          "core-to-Bridge import")
                stack.append((dep, False))
            else:
                p.require(dep.split(".")[0] in ("Init", "Lean", "Std"), "unsupported external import")
                toolchain.add(dep)
    # Never silently discard assertions about unreached dependencies or source files.
    unused = sorted(set(sources)-used)
    if unused: issues.append({"status": "unreached-source-metadata", "paths": unused})
    for path, sha in reads:
        data = p.stable_read(path, p.RAW)
        account(data)
        p.require(path.resolve() == path and hashlib.sha256(data).hexdigest() == sha,
                  "dependency changed during inventory")
    digest = lambda value: hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",", ":")).encode()).hexdigest()
    return {"schema": 1, "status": "NONPASS" if issues else "lexical-source-match-only",
            "packetReceipt": receipt, "requestSha256": digest(request),
            "producerHeadClaim": request["producerHead"], "producerBaseClaim": request["producerBase"],
            "modules": done, "issues": issues, "measurements": measured,
            "supplementaryArchives": [x["receipt"] for x in supplementary],
            "unusedSupplementarySources": {x["receipt"]["packetSha256"]:sorted(path for path in x["bodies"]
                if path.endswith(".lean") and not any(v.get("path")==path and
                    v.get("origin")=="archive:"+x["receipt"]["packetSha256"] for v in done.values()))
                for x in supplementary}, "sourceInventorySha256": digest(sources),
            "toolchainImportsPendingBinding": sorted(toolchain),
            "anchorValidated": False, "kernelValidated": False, "replayValidated": False,
            "semanticPremisesDischarged": False, "releaseClosed": False,
            "sourceSearch": "hash-addressed search of supplied directories, not Lean import-path resolution",
            "boundary": "Lexical imports and exact source bytes only; no revision/ancestry/type/value/axiom/replay proof"}


def main():
    resource.setrlimit(resource.RLIMIT_AS, (512*1024**2, 512*1024**2))
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError("metadata deadline")))
    signal.alarm(60)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path); parser.add_argument("expected", type=Path)
    parser.add_argument("request", type=Path); parser.add_argument("sources", type=Path, nargs="+")
    args = parser.parse_args()
    try:
        lock = open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a")
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        result = reconcile(p.stable_read(args.packet, p.COMPRESSED),
                           p.load(p.stable_read(args.expected, 1024**2)),
                           p.load(p.stable_read(args.request, 1024**2)), args.sources)
        print(json.dumps(result, sort_keys=True))
        return 2 if result["status"] == "NONPASS" else 0
    except (TypeError, ValueError, OSError, EOFError, p.tarfile.TarError, p.zlib.error,
            TimeoutError, MemoryError) as exc:
        print(json.dumps({"status":"NONPASS", "error":str(exc), "kernelValidated":False,
                          "replayValidated":False, "releaseClosed":False,
                          "semanticPremisesDischarged":False}))
        return 2


if __name__ == "__main__": raise SystemExit(main())
