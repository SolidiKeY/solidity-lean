#!/usr/bin/env python3
"""Guard regression: hidden ancestor CPU limits masquerade as matching child settings.

These are visible cgroup-v2 values only. A namespace can hide ancestors; this
module does not attest the mount, VM, daemon, or completeness of ancestry.
"""
import pathlib
import re

IDENT = re.compile(r"[0-9a-f]{64}\Z")
CPUSET = re.compile(r"[0-9]+(?:-[0-9]+)?(?:,[0-9]+(?:-[0-9]+)?)*\Z")




def ascii_uint(value):
    return (isinstance(value, str) and len(value) <= 20 and re.fullmatch(r"[0-9]+", value) is not None
            and int(value) <= (1 << 64) - 1)

def valid_cpuset(value):
    if not isinstance(value, str) or not CPUSET.fullmatch(value):
        return False
    previous = -1
    for part in value.split(","):
        ends = part.split("-")
        if any(not ascii_uint(end) for end in ends):
            return False
        low, high = int(ends[0]), int(ends[-1])
        if low > high or low <= previous:
            return False
        previous = high
    return True

def read_chain(root, leaf):
    root, leaf = pathlib.Path(root), pathlib.Path(leaf)
    if (not root.is_absolute() or not leaf.is_absolute() or root.resolve(strict=True) != root
            or leaf.resolve(strict=True) != leaf or not leaf.is_relative_to(root)):
        raise ValueError("invalid cgroup path")
    paths = []
    path = leaf
    while True:
        paths.append(path)
        if path == root:
            break
        path = path.parent
    result = []
    for path in reversed(paths):
        quota = (path / "cpu.max").read_text().strip()
        burst = (path / "cpu.max.burst").read_text().strip()
        weight = (path / "cpu.weight").read_text().strip()
        idle = (path / "cpu.idle").read_text().strip()
        cpus = (path / "cpuset.cpus.effective").read_text().strip()
        mems = (path / "cpuset.mems.effective").read_text().strip()
        fields = quota.split()
        if (len(fields) != 2 or (fields[0] != "max" and (not ascii_uint(fields[0]) or int(fields[0]) <= 0))
                or not ascii_uint(fields[1]) or int(fields[1]) <= 0
                or not ascii_uint(burst) or not ascii_uint(weight) or not 1 <= int(weight) <= 10000
                or idle not in ("0", "1") or not valid_cpuset(cpus) or not valid_cpuset(mems)):
            raise ValueError("invalid or unavailable effective CPU policy")
        result.append({"path": "/" if path == root else "/" + path.relative_to(root).as_posix(),
                       "cpu_max": quota, "cpu_burst": burst, "cpu_weight": weight, "cpu_idle": idle,
                       "cpus_effective": cpus, "mems_effective": mems})
    return result


def process_identity(container_id, pid):
    stat_text = pathlib.Path("/proc", pid, "stat").read_text()
    if not stat_text.startswith(pid + " (") or ")" not in stat_text:
        raise ValueError("invalid process stat")
    fields = stat_text.rsplit(")", 1)[1].split()
    if len(fields) <= 19 or not ascii_uint(fields[19]):
        raise ValueError("missing process start time")
    group = pathlib.Path("/proc", pid, "cgroup").read_text().strip()
    if group != "0::/../docker/" + container_id:
        raise ValueError("unexpected process cgroup")
    return fields[19], group


def local_mount_supported():
    mounts = pathlib.Path("/proc/self/mountinfo").read_text().splitlines()
    return any(len(line.split()) >= 6 and line.split()[3:5] == ["/..", "/sys/fs/cgroup"]
               and " - cgroup2 " in line for line in mounts)


def local_snapshot(container_id, pid):
    if not isinstance(container_id, str) or not IDENT.fullmatch(container_id) or not isinstance(pid, str) or not ascii_uint(pid) or int(pid) <= 0:
        raise ValueError("invalid container identity")
    first_identity = process_identity(container_id, pid)
    if not local_mount_supported():
        raise ValueError("unsupported cgroup mount")
    root = pathlib.Path("/sys/fs/cgroup")
    leaf = root / "docker" / container_id
    first = read_chain(root, leaf)
    second = read_chain(root, leaf)
    if first != second or process_identity(container_id, pid) != first_identity:
        raise ValueError("process identity, membership or CPU policy changed while sampling")
    # The observed mount root is /.. in the current namespace; ancestors above
    # that view cannot be authenticated here, so this is never a gate pass.
    return {"mount_root": "/..", "ancestor_complete": False, "container_id": container_id,
            "pid": pid, "start_ticks": first_identity[0], "visible_chain": first}


def valid_snapshot(value):
    if (not isinstance(value, dict) or set(value) != {"mount_root", "ancestor_complete", "container_id", "pid", "start_ticks", "visible_chain"}
            or value["mount_root"] != "/.." or value["ancestor_complete"] is not False
            or not isinstance(value["container_id"], str) or not IDENT.fullmatch(value["container_id"])
            or not isinstance(value["pid"], str) or not ascii_uint(value["pid"]) or int(value["pid"]) <= 0
            or not isinstance(value["start_ticks"], str) or not ascii_uint(value["start_ticks"])
            or not isinstance(value["visible_chain"], list) or len(value["visible_chain"]) != 3):
        return False
    previous = None
    for item in value["visible_chain"]:
        if (not isinstance(item, dict) or set(item) != {"path", "cpu_max", "cpu_burst", "cpu_weight", "cpu_idle", "cpus_effective", "mems_effective"}
                or any(not isinstance(item[key], str) for key in item)):
            return False
        path = item["path"]
        if previous is None:
            if path != "/":
                return False
        else:
            if (not path.startswith("/") or any(part in ("", ".", "..") for part in path[1:].split("/"))
                    or str(pathlib.PurePosixPath(path).parent) != previous):
                return False
        fields = item["cpu_max"].split()
        if (len(fields) != 2 or (fields[0] != "max" and (not ascii_uint(fields[0]) or int(fields[0]) <= 0))
                or not ascii_uint(fields[1]) or int(fields[1]) <= 0
                or not ascii_uint(item["cpu_burst"]) or not ascii_uint(item["cpu_weight"])
                or not 1 <= int(item["cpu_weight"]) <= 10000 or item["cpu_idle"] not in ("0", "1")
                or not valid_cpuset(item["cpus_effective"]) or not valid_cpuset(item["mems_effective"])):
            return False
        previous = path
    return [row["path"] for row in value["visible_chain"]] == ["/", "/docker", "/docker/" + value["container_id"]]


def compare(before, after):
    if not valid_snapshot(before) or not valid_snapshot(after):
        return "invalid"
    if before != after:
        return "mismatch"
    return "matching-visible-unattested"


def compare_visible_policies(before, after):
    """Compare two separately identified runs without attesting hidden ancestors."""
    if not valid_snapshot(before) or not valid_snapshot(after):
        return "invalid"
    def normalized(snapshot):
        # The final path contains the per-run container ID; preserve the root
        # and parent entries, normalize only that leaf identity.
        chain = [dict(row) for row in snapshot["visible_chain"]]
        chain[-1]["path"] = "/docker/<container>"
        return chain
    if normalized(before) != normalized(after):
        return "mismatch"
    return "matching-visible-unattested"
