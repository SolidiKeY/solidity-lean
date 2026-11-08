"""Guard complete H109 source/cache/toolchain input identity observations.

This is a fail-closed tree inventory, not an immutable snapshot or VM
attestation. The runner must separately enforce read-only inputs and the writer
lock, then compare inventories before/after. It never executes input files.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import stat


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def attributes(handle):
    # A regular/directory fd pins the inode; symlink metadata uses a pinned
    # parent fd via procfs and never follows the leaf link.
    if isinstance(handle, int):
        return {name: os.getxattr(handle, name).hex() for name in sorted(os.listxattr(handle))}
    return {name: os.getxattr(handle, name, follow_symlinks=False).hex()
            for name in sorted(os.listxattr(handle, follow_symlinks=False))}


def fingerprint(value):
    return (value.st_mode, value.st_uid, value.st_gid, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns, value.st_dev, value.st_ino, value.st_nlink)


def inventory(root):
    root = Path(root)
    if not root.is_absolute() or root != root.resolve(strict=True) or not root.is_dir():
        raise ValueError("Expected absolute non-symlink input directory")
    records = []

    def visit(parent, name, relative, root_fd=None):
        before = os.fstat(root_fd) if root_fd is not None else os.stat(name, dir_fd=parent, follow_symlinks=False)
        descriptor = None
        try:
            if stat.S_ISDIR(before.st_mode):
                descriptor = (os.dup(root_fd) if root_fd is not None else
                              os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent))
                kind = "directory"
            elif stat.S_ISREG(before.st_mode):
                descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
                kind = "file"
            elif stat.S_ISLNK(before.st_mode):
                kind = "symlink"
            else:
                raise ValueError("Unsupported special input file")
            if descriptor is not None and fingerprint(os.fstat(descriptor)) != fingerprint(before):
                raise ValueError("Input replaced while opening")
            attr_handle = descriptor if descriptor is not None else f"/proc/self/fd/{parent}/{name}"
            common = {"path": relative, "kind": kind, "mode": stat.S_IMODE(before.st_mode),
                      "uid": before.st_uid, "gid": before.st_gid,
                      "mtimeNs": before.st_mtime_ns, "xattrs": attributes(attr_handle)}
            identity = {"device": before.st_dev, "inode": before.st_ino,
                        "ctimeNs": before.st_ctime_ns, "links": before.st_nlink}
            if kind == "file":
                hasher, count = hashlib.sha256(), 0
                while count <= before.st_size:
                    chunk = os.read(descriptor, min(262144, before.st_size + 1 - count))
                    if not chunk:
                        break
                    hasher.update(chunk)
                    count += len(chunk)
                if count != before.st_size:
                    raise ValueError("Input size changed")
                common.update(bytes=count, sha256=hasher.hexdigest())
            elif kind == "symlink":
                target = os.readlink(name, dir_fd=parent)
                if os.path.isabs(target):
                    raise ValueError("Escaping input symlink")
                common.update(target=target)
            records.append({"contentMetadata": common, "observedIdentity": identity})
            if kind == "directory":
                names = sorted(os.listdir(descriptor))
                for child in names:
                    visit(descriptor, child, child if relative == "." else relative + "/" + child)
                if names != sorted(os.listdir(descriptor)):
                    raise ValueError("Input directory changed")
            after = os.fstat(descriptor) if descriptor is not None else os.stat(name, dir_fd=parent, follow_symlinks=False)
            if fingerprint(before) != fingerprint(after) or common["xattrs"] != attributes(attr_handle):
                raise ValueError("Input changed during observation")
            if root_fd is None and fingerprint(os.stat(name, dir_fd=parent, follow_symlinks=False)) != fingerprint(before):
                raise ValueError("Input path replaced")
        finally:
            if descriptor is not None:
                os.close(descriptor)

    fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        visit(None, None, ".", fd)
    finally:
        os.close(fd)
    # Resolve links in the recorded namespace; never follow a filesystem link.
    table = {r["contentMetadata"]["path"]: r["contentMetadata"] for r in records}
    for entry in table.values():
        if entry["kind"] != "symlink":
            continue
        pending, resolved, seen, expansions = entry["path"].split("/"), [], set(), 0
        while pending:
            part = pending.pop(0)
            if part in ("", "."):
                continue
            if part == "..":
                if not resolved:
                    raise ValueError("Escaping input symlink")
                resolved.pop()
                continue
            candidate = "/".join(resolved + [part])
            if candidate not in table:
                raise ValueError("Dangling input symlink")
            target_entry = table[candidate]
            if target_entry["kind"] == "symlink":
                state = (candidate, tuple(resolved), tuple(pending))
                expansions += 1
                if state in seen or expansions > 40:
                    raise ValueError("Cyclic input symlink")
                seen.add(state)
                # Expand links before interpreting subsequent '..', as the
                # kernel does. Lexical normpath here would conceal escapes.
                pending = target_entry["target"].split("/") + pending
            else:
                resolved.append(part)
                if pending and target_entry["kind"] != "directory":
                    raise ValueError("Non-directory input symlink ancestor")
    aliases = {}
    for item in records:
        if item["contentMetadata"]["kind"] == "file":
            key = (item["observedIdentity"]["device"], item["observedIdentity"]["inode"])
            aliases.setdefault(key, []).append(item)
    external = [group[0]["contentMetadata"]["path"] for group in aliases.values()
                if group[0]["observedIdentity"]["links"] > len(group)]
    return {"schemaVersion": 1, "root": str(root), "records": records,
            "externalHardlinkAliases": sorted(external),
            "contentMetadataSha256": digest([r["contentMetadata"] for r in records]),
            "observationSha256": digest(records),
            "boundary": "Descriptor-relative non-atomic observation; no execution or immutable snapshot claim. "
                        "File hashes stream in256KiB chunks. Mode/owner/mtime/xattrs/content recorded; "
                        "atime excluded because observation itself can change it. Device/inode/ctime "
                        "are not cross-copy equivalence. Symlinks resolve only in the recorded root. "
                        "External hardlink aliases are flagged; sealing must flatten or reject them. "
                        "No physical/page-cache equivalence; caller must enforce reserve during all stages."}


def verify(root, expected):
    current = inventory(root)
    if current != expected:
        raise ValueError("Input tree identity drift")
    return current


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--output", type=Path)
    group.add_argument("--verify", type=Path)
    parser.add_argument("--expected-sha256", help="Trusted receipt pin for the exact inventory JSON bytes")
    args = parser.parse_args()
    if args.verify:
        data = args.verify.read_bytes()
        if not args.expected_sha256 or hashlib.sha256(data).hexdigest() != args.expected_sha256:
            raise ValueError("Inventory receipt pin mismatch")
        result = verify(args.root, json.loads(data))
        print("PASS input tree unchanged; observation only")
    else:
        if args.output.resolve().is_relative_to(args.root.resolve()):
            raise ValueError("Inventory output must be outside the input tree")
        result = inventory(args.root)
        descriptor = os.open(args.output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(descriptor, "w") as stream:
            json.dump(result, stream, indent=2)
            stream.write("\n")
