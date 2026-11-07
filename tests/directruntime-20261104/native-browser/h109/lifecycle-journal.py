"""Guard H127 interrupted-create ownership and unsafe next-worker regressions.

Durable journal primitives only: no Docker invocation, resource attestation,
measurement verdict or post-create barrier release. The future controller must
hold this lease through create, observation and authenticated cleanup. A crashed
or ambiguous create remains blocked; an approval is not cleanup evidence.
"""
import fcntl
import hashlib
import json
import os
import re
import secrets
import stat
import time
from pathlib import Path


class JournalError(RuntimeError):
    pass


class Busy(JournalError):
    pass


class Unresolved(JournalError):
    pass


HEX64 = re.compile(r"[0-9a-f]{64}\Z")
STATES = {
    "reserved": {"create-intent", "aborted-before-create"},
    "create-intent": {"created", "create-unknown"},
    "created": {"start-intent", "cleanup-unresolved", "drain-observed"},
    "start-intent": {"started", "start-unknown"},
    "started": {"kernel-observed", "cleanup-unresolved"},
    "kernel-observed": {"worker-intent", "cleanup-unresolved"},
    "worker-intent": {"exit-observed", "worker-unknown"},
    "exit-observed": {"drain-observed", "cleanup-unresolved"},
    "create-unknown": {"cleanup-unresolved"},
    "start-unknown": {"cleanup-unresolved"},
    "worker-unknown": {"cleanup-unresolved"},
    "cleanup-unresolved": set(),
    "drain-observed": set(),
    "aborted-before-create": set(),
}


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n").encode()


def digest(value):
    return hashlib.sha256(encode(value)).hexdigest()


def current_boot_id():
    value = Path("/proc/sys/kernel/random/boot_id").read_text().strip()
    if not re.fullmatch(r"[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}", value):
        raise JournalError("unsupported boot identity")
    return value


def private_regular(fd):
    s = os.fstat(fd)
    if not stat.S_ISREG(s.st_mode) or s.st_uid != os.geteuid() or s.st_nlink != 1 or stat.S_IMODE(s.st_mode) != 0o600:
        raise JournalError("journal file must be private, owned, regular and unaliased")


def open_directory(path):
    """Pin every ancestor by descriptor; never resolve through a symlink."""
    raw = os.fspath(path)
    if not raw.startswith("/") or ".." in raw.split("/"):
        raise JournalError("store requires an absolute path without parent traversal")
    fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in Path(raw).parts[1:]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        s = os.fstat(fd)
        if s.st_uid != os.geteuid() or stat.S_IMODE(s.st_mode) != 0o700:
            raise JournalError("store directory must be owned and mode0700")
        return fd
    except BaseException:
        os.close(fd)
        raise


def provision(path):
    """Create a fresh lease inode once; caller persists this locator externally.

    Existing or partly provisioned stores are never silently rebound. No worker
    can start until the returned locator itself has been durably recorded.
    """
    fd = open_directory(path)
    lock = None
    try:
        if os.listdir(fd):
            raise JournalError("provisioning requires a new empty private store")
        lock = os.open("controller.lock", os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=fd)
        private_regular(lock)
        token = (secrets.token_hex(32)+"\n").encode()
        offset = 0
        while offset < len(token):
            wrote = os.write(lock, token[offset:])
            if wrote <= 0:
                raise JournalError("short lease-token write")
            offset += wrote
        os.fsync(lock)
        os.fsync(fd)
        directory, lease = os.fstat(fd), os.fstat(lock)
        return {"version": 1, "directory": (directory.st_dev, directory.st_ino), "lock": (lease.st_dev, lease.st_ino), "leaseSha256": hashlib.sha256(token).hexdigest()}
    finally:
        if lock is not None:
            os.close(lock)
        os.close(fd)


class Journal:
    """One controller lease, with a persistent active-run barrier.

    The caller provisions the private directory/lease once and persists both
    (device,inode) pairs and the random lease-content SHA256 outside that
    directory before opening it. A newly observed locator
    cannot authenticate a replaced root. Journal descriptors must never enter a
    worker; inherited post-fork API use is refused. Unresolved state
    has no force/approval override. `drain-observed` records a fact reference,
    not verified cleanup; this component cannot release a post-create run.
    The private store must be excluded from other writers and worker mounts.
    Hash chaining is corruption detection, not hostile same-UID authentication.
    """
    def __init__(self, path, locator):
        self.path = os.fspath(path)
        if not isinstance(locator, dict) or set(locator) != {"version", "directory", "lock", "leaseSha256"} or type(locator["version"]) is not int or locator["version"] != 1:
            raise JournalError("a separately persisted store/lease locator is required")
        for key in ("directory", "lock"):
            value = locator[key]
            if not isinstance(value, (tuple, list)) or len(value) != 2 or any(type(n) is not int or n < 0 for n in value):
                raise JournalError("invalid store/lease locator")
        if not isinstance(locator["leaseSha256"], str) or not HEX64.fullmatch(locator["leaseSha256"]):
            raise JournalError("invalid external lease-token pin")
        self.expected_token = locator["leaseSha256"]
        self.expected_directory = tuple(locator["directory"])
        self.expected_lock = tuple(locator["lock"])
        self.fd = self.lock = None
        self.owner_pid = None

    def __enter__(self):
        if self.fd is not None:
            raise JournalError("journal lease cannot be reentered")
        self.fd = open_directory(self.path)
        try:
            identity = os.fstat(self.fd)
            if (identity.st_dev, identity.st_ino) != self.expected_directory:
                raise JournalError("store differs from pinned directory identity")
            self.owner_pid = os.getpid()
            self.lock = os.open("controller.lock", os.O_RDWR | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=self.fd)
            private_regular(self.lock)
            lease = os.fstat(self.lock)
            if (lease.st_dev, lease.st_ino) != self.expected_lock:
                raise JournalError("lease inode differs from external pin")
            if lease.st_size != 65 or hashlib.sha256(os.pread(self.lock, 66, 0)).hexdigest() != self.expected_token:
                raise JournalError("lease token differs from external pin")
            try:
                fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as e:
                raise Busy("another controller owns the journal lease") from e
            return self
        except BaseException:
            self.__exit__(None, None, None)
            raise

    def __exit__(self, *args):
        for name in ("lock", "fd"):
            fd = getattr(self, name)
            if fd is not None:
                os.close(fd)
                setattr(self, name, None)

    def _check(self):
        if self.fd is None or self.lock is None or self.owner_pid != os.getpid():
            raise JournalError("journal lease is not held")
        private_regular(self.lock)
        held = os.fstat(self.lock)
        if held.st_size != 65 or hashlib.sha256(os.pread(self.lock, 66, 0)).hexdigest() != self.expected_token:
            raise JournalError("lease token differs from external pin")
        entry = os.stat("controller.lock", dir_fd=self.fd, follow_symlinks=False)
        if (held.st_dev, held.st_ino) != self.expected_lock or (entry.st_dev, entry.st_ino) != self.expected_lock or not stat.S_ISREG(entry.st_mode):
            raise JournalError("lease inode was replaced")
        # Detect a renamed/replaced store before publishing or removing records.
        fd = open_directory(self.path)
        try:
            a, b = os.fstat(fd), os.fstat(self.fd)
            if (a.st_dev, a.st_ino) != (b.st_dev, b.st_ino):
                raise JournalError("store directory identity changed")
        finally:
            os.close(fd)

    def _read(self, name):
        self._check()
        try:
            fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=self.fd)
        except FileNotFoundError:
            return None
        try:
            private_regular(fd)
            if os.fstat(fd).st_size > 65536:
                raise JournalError("oversized journal")
            data = bytearray()
            while len(data) <= 65536:
                block = os.read(fd, min(4096, 65537-len(data)))
                if not block:
                    break
                data.extend(block)
            if len(data) > 65536:
                raise JournalError("oversized journal")
            try:
                value = json.loads(data)
            except (ValueError, UnicodeError) as e:
                raise JournalError("truncated or invalid journal; barrier remains") from e
            if not isinstance(value, dict) or encode(value) != data:
                raise JournalError("noncanonical journal")
            return value
        finally:
            os.close(fd)

    def _new(self, name, value):
        self._check()
        data = encode(value)
        if len(data) > 65536:
            raise JournalError("oversized journal")
        fd = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=self.fd)
        try:
            private_regular(fd)
            # A short write or fsync failure leaves an active barrier, never a pass.
            with os.fdopen(fd, "wb", closefd=False) as stream:
                stream.write(data)
                stream.flush()
                os.fsync(fd)
        finally:
            os.close(fd)
        os.fsync(self.fd)

    def read_active(self):
        active = self._read("active.json")
        if active is not None:
            self._validate(active)
        return active

    @staticmethod
    def _validate(active):
        if set(active) != {"version", "identity", "events"} or type(active["version"]) is not int or active["version"] != 1:
            raise JournalError("unknown journal schema")
        identity = active["identity"]
        if not isinstance(identity, dict) or set(identity) != {"nonce", "name", "planSha256", "imageId", "bootId"}:
            raise JournalError("invalid identity")
        nonce = identity["nonce"]
        if not isinstance(nonce, str) or not re.fullmatch(r"[0-9a-f]{32}", nonce) or identity["name"] != "h127-"+nonce:
            raise JournalError("invalid ownership nonce/name")
        if not isinstance(identity["planSha256"], str) or not HEX64.fullmatch(identity["planSha256"]):
            raise JournalError("invalid plan pin")
        if not isinstance(identity["imageId"], str) or not re.fullmatch(r"sha256:[0-9a-f]{64}", identity["imageId"]):
            raise JournalError("invalid image ID syntax; no Docker image is queried")
        if not isinstance(identity["bootId"], str) or not re.fullmatch(r"[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}", identity["bootId"]):
            raise JournalError("invalid boot identity")
        events = active["events"]
        if not isinstance(events, list) or not events:
            raise JournalError("missing event history")
        previous, state, previous_time = digest(identity), None, -1
        for i, event in enumerate(events):
            if not isinstance(event, dict) or set(event) != {"sequence", "state", "previous", "monotonicNs", "facts"}:
                raise JournalError("invalid event schema")
            if type(event["sequence"]) is not int or event["sequence"] != i or event["previous"] != previous:
                raise JournalError("broken journal event chain")
            if type(event["monotonicNs"]) is not int or event["monotonicNs"] < 0 or event["monotonicNs"] < previous_time or not isinstance(event["facts"], dict):
                raise JournalError("invalid event observation")
            next_state = event["state"]
            if not isinstance(next_state, str):
                raise JournalError("invalid state")
            if (i == 0 and next_state != "reserved") or (i and next_state not in STATES.get(state, set())):
                raise JournalError("illegal lifecycle transition")
            previous, state, previous_time = digest(event), next_state, event["monotonicNs"]

    def reserve(self, plan_sha256, image_id):
        if self._read("active.json") is not None:
            raise Unresolved("an active run already blocks the next worker")
        nonce = secrets.token_hex(16)
        identity = {"nonce": nonce, "name": "h127-"+nonce, "planSha256": plan_sha256, "imageId": image_id, "bootId": current_boot_id()}
        active = {"version": 1, "identity": identity, "events": [{"sequence": 0, "state": "reserved", "previous": digest(identity), "monotonicNs": time.monotonic_ns(), "facts": {}}]}
        self._validate(active)
        self._new("active.json", active)
        return identity.copy()

    def advance(self, state, facts):
        active = self.read_active()
        if active is None:
            raise JournalError("no reserved run")
        if active["identity"]["bootId"] != current_boot_id():
            raise Unresolved("boot changed; authenticated recovery is not implemented")
        event = {"sequence": len(active["events"]), "state": state, "previous": digest(active["events"][-1]), "monotonicNs": time.monotonic_ns(), "facts": facts}
        active["events"].append(event)
        self._validate(active)
        # Stage an exclusive sibling; fsync before atomic replacement and dir sync.
        temporary = "stage-"+secrets.token_hex(16)+".json"
        self._new(temporary, active)
        os.replace(temporary, "active.json", src_dir_fd=self.fd, dst_dir_fd=self.fd)
        os.fsync(self.fd)

    def seal_pre_create_abort(self):
        active = self.read_active()
        if active is None:
            raise JournalError("no active run")
        if active["identity"]["bootId"] != current_boot_id():
            raise Unresolved("boot changed; authenticated recovery is not implemented")
        if active["events"][-1]["state"] == "reserved":
            self.advance("aborted-before-create", {})
            active = self.read_active()
        if active["events"][-1]["state"] != "aborted-before-create":
            raise Unresolved("post-create cleanup requires the future authenticated verifier")
        name = "abort-"+active["identity"]["nonce"]+".json"
        existing = self._read(name)
        if existing is None:
            self._new(name, active)
        elif existing != active:
            raise JournalError("conflicting sealed abort receipt")
        # Publication succeeds before the active barrier can be removed.
        self._check()
        os.unlink("active.json", dir_fd=self.fd)
        os.fsync(self.fd)
        return name
