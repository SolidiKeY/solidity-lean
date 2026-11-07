#!/usr/bin/env python3
"""Combine source/tool and selected cache identities; no VM attestation."""
import importlib.util
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent

def load(name):
    spec = importlib.util.spec_from_file_location("h55_" + name, ROOT / (name + ".py"))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

provenance = load("provenance")
cache_fingerprint = load("cache_fingerprint")


def capture(root, expected_head, tool, source, cache):
    # Check the source and tool on both sides of reading the selected cache.
    before = provenance.snapshot(root, expected_head, tool, source)
    cache_path = pathlib.Path(cache)
    if not cache_path.is_absolute() or cache_path.resolve() != cache_path:
        raise ValueError("cache path must be absolute and canonical")
    manifest = cache_fingerprint.fingerprint(cache_path)
    after = provenance.snapshot(root, expected_head, tool, source)
    if not provenance.unchanged(before, after):
        raise ValueError("source or tool changed during cache capture")
    return {"identity": before, "tool_path": str(tool), "cache_path": str(cache_path),
            "cache": manifest}


def compare(before, after):
    # A structural comparison of caller-provided data is not authentication.
    keys = {"identity", "tool_path", "cache_path", "cache"}
    if not isinstance(before, dict) or set(before) != keys or before != after:
        return False
    if not provenance.unchanged(before["identity"], before["identity"]):
        return False
    cache = before["cache"]
    if not isinstance(cache, dict) or set(cache) != {"root_mode", "root_mtime_ns", "directories", "files", "manifest_sha256"}:
        return False
    if not isinstance(before["tool_path"], str) or not before["tool_path"].startswith("/"):
        return False
    if not isinstance(before["cache_path"], str) or not before["cache_path"].startswith("/"):
        return False
    # Recompute the cache manifest digest to reject a malformed equal pair.
    import hashlib
    import json
    data = {k: cache[k] for k in ("root_mode", "root_mtime_ns", "directories", "files")}
    try:
        raw = json.dumps(data, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode()
    except (TypeError, ValueError):
        return False
    return isinstance(cache["manifest_sha256"], str) and hashlib.sha256(raw).hexdigest() == cache["manifest_sha256"]
