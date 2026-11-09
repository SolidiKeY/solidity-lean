#!/usr/bin/env python3
"""Guard H127 timing intake against substituted files and cross-run journal mixing.

Externally pinned canonical records are assessed without executing observations
or opening a live journal lease. Pins and matching identities authenticate bytes,
not the recorded execution, CI context, resources, cleanup or barrier release.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import importlib.util
import json
from pathlib import Path


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


offline = load("stage_offline_journal", "offline-journal.py")
timing = load("stage_offline_timing", "stage-timing.py")


def inspect_files(stage_path, stage_sha256, journal_path, journal_sha256):
    """Inspect exact bounded inputs; no producer fact becomes acceptance."""
    journal_bytes = offline.read_pinned(journal_path, journal_sha256)
    journal_result = offline.inspect_bytes(journal_bytes, journal_sha256)
    stage_bytes = offline.read_pinned(stage_path, stage_sha256)
    stage = json.loads(stage_bytes)
    if (not isinstance(stage, dict) or offline.journal.encode(stage) != stage_bytes or
            set(stage) != {"journalSha256", "identity", "timing"}):
        raise ValueError("canonical stage envelope required")
    if stage["journalSha256"] != journal_sha256:
        raise ValueError("stage names another journal")
    # Canonical bytes avoid Python's bool/int equality conflating identities.
    if offline.journal.encode(stage["identity"]) != offline.journal.encode(journal_result["identity"]):
        raise ValueError("stage and journal identities differ")
    record = stage["timing"]
    if not isinstance(record, dict) or not isinstance(record.get("context"), str):
        raise ValueError("fixed timing context required")
    assessment = timing.assess(record)
    lifecycle = json.loads(journal_bytes)
    reserved_ns = lifecycle["events"][0]["monotonicNs"]
    for check in record["checks"]:
        for field in ("start", "end"):
            observation = check[field]
            if observation["bootId"] != journal_result["identity"]["bootId"]:
                raise ValueError("timing and journal boot identities differ")
            if observation["monotonicBeforeNs"] < reserved_ns:
                raise ValueError("timing precedes journal reservation")
    return {"status": "pinned-declared-stage-only", "stageSha256": stage_sha256,
            "journalSha256": journal_sha256, "identity": journal_result["identity"],
            "lastRecordedState": journal_result["lastRecordedState"],
            "timing": assessment, "recordedFactsVerified": False,
            "executionAccepted": False, "resourceAccepted": False,
            "measurementAccepted": False, "cleanupAccepted": False,
            "postCreateBarrierReleased": False,
            "boundary": "Exact pinned records and declared timing only; no execution, CI identity, source, kernel, resources, cleanup or recovery verification."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage")
    parser.add_argument("--sha256", required=True)
    parser.add_argument("--journal", required=True)
    parser.add_argument("--journal-sha256", required=True)
    args = parser.parse_args()
    print(json.dumps(inspect_files(args.stage, args.sha256, args.journal,
                                   args.journal_sha256), sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
