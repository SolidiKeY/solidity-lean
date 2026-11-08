#!/usr/bin/env python3
"""Guard H127 sealed worker inputs against writable or nested mount substitution.

Read-only Linux mount observations, not mount creation, immutable host storage,
source-content verification or worker authorization. The trusted controller must
separately bind namespaces, ownership, source/package/cache pins and lifetime.
No commands, mount operations, Docker or cleanup are performed here.
"""
import hashlib
import os
from pathlib import Path
import re
import stat


class MountError(RuntimeError):
    pass


def unescape(value):
    # mountinfo's only pathname escapes (proc_pid_mountinfo(5)).
    escapes = {"040": " ", "011": "\t", "012": "\n", "134": "\\"}
    if re.search(r"\\(?!040|011|012|134)", value):
        raise MountError("unknown mountinfo escape")
    return re.sub(r"\\(040|011|012|134)", lambda m: escapes[m[1]], value)


def parse(data):
    if not isinstance(data, str) or len(data) > 4 * 1024 * 1024:
        raise MountError("bounded mountinfo text required")
    rows = {}
    for line in data.splitlines():
        fields = line.split(" ")
        if fields.count("-") != 1:
            raise MountError("invalid mountinfo separator")
        at = fields.index("-")
        if at < 6 or len(fields) != at + 4 or any(not x for x in fields):
            raise MountError("invalid mountinfo fields")
        if not fields[0].isdecimal() or not fields[1].isdecimal() or not re.fullmatch(r"[0-9]+:[0-9]+", fields[2]):
            raise MountError("invalid mount identity")
        mid = int(fields[0])
        if mid <= 0 or mid in rows:
            raise MountError("duplicate or invalid mount ID")
        root, point = unescape(fields[3]), unescape(fields[4])
        if not root.startswith("/") or not point.startswith("/"):
            raise MountError("absolute mount paths required")
        options = fields[5].split(",")
        if ("ro" in options) == ("rw" in options):
            raise MountError("ambiguous mount access flags")
        rows[mid] = {"id": mid, "parent": int(fields[1]), "device": fields[2],
                     "root": root, "point": point, "options": options,
                     "filesystem": fields[at+1], "source": unescape(fields[at+2]),
                     "superOptions": fields[at+3].split(",")}
    if not rows:
        raise MountError("empty mount table")
    return rows


def table_text():
    with open("/proc/self/mountinfo", "r", encoding="utf-8") as stream:
        text = stream.read(4 * 1024 * 1024 + 1)
    if len(text) > 4 * 1024 * 1024:
        raise MountError("oversized mount table")
    return text


def mount_id(fd):
    text = Path(f"/proc/self/fdinfo/{fd}").read_text()
    values = re.findall(r"^mnt_id:\s*([0-9]+)$", text, re.MULTILINE)
    if len(values) != 1:
        raise MountError("FD mount ID unavailable")
    return int(values[0])


def open_directory(path):
    raw = os.fspath(path)
    if not raw.startswith("/") or any(x in (".", "..") for x in raw.split("/")):
        raise MountError("absolute path without dot components required")
    fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for name in Path(raw).parts[1:]:
            child = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        return fd
    except BaseException:
        os.close(fd)
        raise


def validate_mount(rows, mid, path, device, flags):
    if mid not in rows:
        raise MountError("FD mount absent from observed table")
    row = rows[mid]
    if row["point"] != path or row["device"] != f"{os.major(device)}:{os.minor(device)}":
        raise MountError("input must be the exact observed mount point/device")
    if "ro" not in row["options"] or not flags & os.ST_RDONLY:
        raise MountError("input mount is writable")
    prefix = path.rstrip("/") + "/"
    if any(r["id"] != mid and (r["point"] == path or r["point"].startswith(prefix)) for r in rows.values()):
        raise MountError("nested or stacked input mount refused")
    return row


def observe(path):
    """Pin a directory, compare mount table/namespace before and after capture."""
    path = os.fspath(path)
    if path == "/" or path.rstrip("/") != path:
        raise MountError("dedicated non-root input mount required")
    fd = open_directory(path)
    try:
        namespace = os.readlink("/proc/self/ns/mnt")
        before = table_text()
        info = os.fstat(fd)
        if not stat.S_ISDIR(info.st_mode):
            raise MountError("input must be a directory")
        mid = mount_id(fd)
        row = validate_mount(parse(before), mid, path, info.st_dev, os.fstatvfs(fd).f_flag)
        other = open_directory(path)
        try:
            current = os.fstat(other)
            if (info.st_dev, info.st_ino, mid) != (current.st_dev, current.st_ino, mount_id(other)):
                raise MountError("input path identity changed")
        finally:
            os.close(other)
        if (before != table_text() or namespace != os.readlink("/proc/self/ns/mnt") or
                mount_id(fd) != mid or not os.fstatvfs(fd).f_flag & os.ST_RDONLY):
            raise MountError("input mount or namespace drift")
        return {"path": path, "mount": row, "mountNamespace": namespace,
                "device": info.st_dev, "inode": info.st_ino,
                "mountTableSha256": hashlib.sha256(before.encode()).hexdigest(),
                "readOnlyMountObserved": True, "contentAuthenticated": False,
                "immutableHostStorageAuthenticated": False, "lifetimeSealed": False,
                "workerExecutionAuthorized": False,
                "boundary": "Point observation under trusted kernel/host; other writable aliases and future remounts are not excluded."}
    finally:
        os.close(fd)
