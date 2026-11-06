from pathlib import Path
import hashlib, json, tarfile, time, resource
out = Path(__file__).resolve().parent
receipt = json.loads((out / "local-export.json").read_text())
catalog = json.loads((out / "catalog.json").read_text())
expected = {}
def sha(stream):
    h = hashlib.sha256()
    for block in iter(lambda: stream.read(1048576), b""):
        h.update(block)
    return h.hexdigest()
with tarfile.open(receipt["archive"], "r:gz") as tar:
    # Expected hashes come from the immutable original run seals and source/cache catalog.
    for run in catalog["runs"]:
        prefix = "runs/" + run["run"] + "/"
        seal = tar.extractfile(prefix + "SHA256SUMS").read().decode()
        for line in seal.splitlines():
            digest, name = line.split("  ", 1)
            expected[prefix + name] = digest
    for source, digest in catalog["owned_sources"].items():
        expected["source-snapshot/" + source] = digest
    dependencies = json.loads(tar.extractfile("dependency-cache/manifest.json").read())
    for name, digest in dependencies["artifact_sha256"].items():
        expected["dependency-cache/lib/lean/" + name] = digest
with open(receipt["archive"], "rb") as stream:
    assert sha(stream) == receipt["sha256"], "archive digest mismatch"
seen = set()
start = time.monotonic()
with tarfile.open(receipt["archive"], "r:gz") as tar:
    for member in tar:
        if member.isdir():
            continue
        assert member.isfile() and member.name not in seen, member.name
        seen.add(member.name)
        if member.name in expected:
            assert sha(tar.extractfile(member)) == expected[member.name], member.name
assert set(expected) <= seen
print(json.dumps({"status": "pass", "command": "python3 -B " + str(Path(__file__).resolve()), "archive": receipt["archive"], "verified_members": len(expected), "regular_members": len(seen), "seconds": time.monotonic() - start, "maxrss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, "cache_transport_receipt": None}, indent=2))
