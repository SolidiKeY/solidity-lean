"""Inspect pin-changing Git commits; callers must authenticate decision bindings.

This module only establishes which commits changed the pin file and extracts a
single canonical Goal-Change trailer. It is not an authorization decision.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

PIN_PATH = "Solidity/Goals/Pins.lean"
DECISION = re.compile(r"H(?:0|[1-9][0-9]*)\Z", re.ASCII)
RAW_TRAILER = re.compile(rb"Goal-Change: (H(?:0|[1-9][0-9]*))\n?\Z")


class TrailerError(ValueError):
    """The commit range or a pin-changing commit could not be checked."""


def git(repo: Path, *args: str, stdin: bytes | None = None) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], input=stdin, capture_output=True, check=False
    )
    if result.returncode:
        raise TrailerError(f"git {args[0]} failed: {result.stderr.decode(errors='replace').strip()}")
    return result.stdout


def commit_id(repo: Path, ref: str) -> str:
    # Resolve before using the reference in a revision range or as an argument.
    if not ref or ref.startswith("-"):
        raise TrailerError("invalid commit reference")
    return git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}").decode().strip()


def pin_changes(repo: Path, base: str, head: str) -> list[tuple[str, str]]:
    """Return (commit, decision id) for each changed pin file in base..head.

    The caller supplies a trusted, available base, handles push creation/deletion,
    and checks every returned id against authenticated exact-triple approvals.
    Merges are compared with every parent, including conflict resolutions.
    """
    # A shallow boundary can hide commits on a merge side even when base is
    # an ancestor of head. Require complete history before enumerating changes.
    if git(repo, "rev-parse", "--is-shallow-repository").strip() != b"false":
        raise TrailerError("shallow repository cannot establish complete push history")
    before, after = commit_id(repo, base), commit_id(repo, head)
    ancestor = subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", before, after],
                              capture_output=True, check=False)
    if ancestor.returncode:
        raise TrailerError("push base is not an ancestor of head, or ancestry cannot be verified")
    commits = git(repo, "rev-list", "--reverse", after, "--not", before).decode().splitlines()
    changes: list[tuple[str, str]] = []
    for commit in commits:
        changed = git(repo, "diff-tree", "--root", "-m", "--no-commit-id", "--name-only",
                      "-r", "-z", commit, "--", PIN_PATH)
        if not changed:
            continue
        message = git(repo, "show", "-s", "--format=%B", commit)
        trailers = git(repo, "interpret-trailers", "--parse", stdin=message).decode("utf-8", "strict")
        matches = [line for line in trailers.splitlines()
                   if line.partition(":")[0].lower() == "goal-change"]
        if len(matches) != 1 or not matches[0].startswith("Goal-Change: "):
            raise TrailerError(f"{commit}: expected exactly one canonical Goal-Change: H<n> trailer")
        decision = matches[0][len("Goal-Change: "):]
        if not DECISION.fullmatch(decision):
            raise TrailerError(f"{commit}: malformed Goal-Change decision")
        # Git normalizes whitespace in its output. Locate an exact raw line and
        # prove it is the parsed trailer, rather than a lookalike in the body.
        lines = message.splitlines(keepends=True)
        sentinel = decision + "0"
        found = False
        for index, line in enumerate(lines):
            raw = RAW_TRAILER.fullmatch(line)
            if raw is None or raw.group(1).decode("ascii") != decision:
                continue
            modified = lines.copy()
            modified[index] = b"Goal-Change: " + sentinel.encode("ascii") + b"\n"
            probe = git(repo, "interpret-trailers", "--parse", stdin=b"".join(modified))
            probe_lines = probe.decode("utf-8", "strict").splitlines()
            candidates = [item for item in probe_lines
                          if item.partition(":")[0].lower() == "goal-change"]
            if candidates == ["Goal-Change: " + sentinel]:
                found = True
                break
        if not found:
            raise TrailerError(f"{commit}: Goal-Change trailer is not spelled exactly")
        changes.append((commit, decision))
    return changes
