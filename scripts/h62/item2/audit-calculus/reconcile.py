"""Exact source-to-kernel identity reconciliation, independent of witnesses."""
from collections import defaultdict


def reconcile_sources(sources, kernel):
    """Return source-id -> actual kernel key; fail closed on ambiguous names.

    A private declaration's canonical user name comes from Lean's exporter.
    No suffix heuristic or proof status participates in this identity join.
    """
    index = defaultdict(list)
    for key, row in kernel.items():
        if key != (row["module"], row["name"]):
            raise RuntimeError("inconsistent kernel identity")
        if "user_name" not in row or "is_private" not in row:
            raise RuntimeError("kernel export lacks canonical privacy metadata")
        index[(row["module"], row["user_name"], row["is_private"])].append(key)
    matched, seen = {}, set()
    for row in sources:
        module = row["file"].removesuffix(".lean").replace("/", ".")
        identity = (module, row["source_name"], row["private"])
        if identity in seen:
            raise RuntimeError("duplicate source identity: " + str(identity))
        seen.add(identity)
        candidates = index.get(identity, [])
        if len(candidates) > 1:
            raise RuntimeError("ambiguous canonical kernel identity: " + str(identity))
        if candidates:
            matched[row["id"]] = candidates[0]
    return matched
