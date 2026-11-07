"""Shared archive input authentication and optimization-independent checks."""
import json
from pathlib import Path
import bulk_inputs


def require(condition, message="archive validation failed"):
    if not condition:
        raise ValueError(message)


def read_bytes(path, repo=None):
    root = Path(__file__).resolve().parents[4] if repo is None else Path(repo)
    return bulk_inputs.read(root, Path(path))


def read_json(path, repo=None):
    return json.loads(read_bytes(path, repo))
