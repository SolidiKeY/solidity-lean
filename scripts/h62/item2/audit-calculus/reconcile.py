"""Exact source-to-kernel identity reconciliation, independent of witnesses."""
from collections import defaultdict
import re


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

def verification_requests(text):
    """Preserve public/private verification order and actual private identity."""
    result=[]
    for line in text.splitlines():
        public=re.fullmatch(r"#verify_joint(_dag)? (\S+) with (\S+)",line)
        private=re.fullmatch(r"#verify_private_joint (\S+) (\S+) with (\S+)",line)
        if public:
            result.append((public[2],public[3],"expr-dag-v1" if public[1] else "repr-v1"))
        elif private:
            result.append(("_private."+private[1]+".0."+private[2],private[3],"repr-v1"))
        elif line.startswith(("#verify_joint ","#verify_joint_dag ","#verify_private_joint ")):
            raise RuntimeError("malformed verification request")
    return result
