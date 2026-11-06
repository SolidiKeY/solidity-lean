#!/usr/bin/env python3
"""Guard regression: a different or privileged container masquerades as the timed Lean job.

This validates a supplied Docker inspect object against an explicit plan. It
is not image, daemon, VM, mount-content or measurement authentication.
"""
import re

IMAGE = re.compile(r"sha256:[0-9a-f]{64}\Z")
GIB = 1024 ** 3


def validate(inspect, plan):
    if not isinstance(inspect, dict) or not isinstance(plan, dict):
        return ["invalid inspect or plan"]
    config, host, mounts = inspect.get("Config"), inspect.get("HostConfig"), inspect.get("Mounts")
    if not isinstance(config, dict) or not isinstance(host, dict) or not isinstance(mounts, list):
        return ["missing container configuration"]
    errors = []
    image = plan.get("image")
    if not isinstance(image, str) or not IMAGE.fullmatch(image) or inspect.get("Image") != image:
        errors.append("image identity mismatch")
    args = plan.get("argv")
    if (not isinstance(args, list) or len(args) != 4 or
            any(not isinstance(a, str) or not a for a in args) or
            not args[0].startswith("/") or args[0].rsplit("/", 1)[-1] != "lean" or
            any(p in ("", ".", "..") for p in args[0][1:].split("/")) or
            args[1:3] != ["-j1", "--tstack=131072"] or not args[3].endswith(".lean") or
            args[3].startswith("/") or "\\" in args[3] or
            any(p in ("", ".", "..") for p in args[3].split("/"))):
        errors.append("invalid fixed Lean command")
    elif config.get("Entrypoint") != [args[0]] or config.get("Cmd") != args[1:]:
        errors.append("container command mismatch")
    cwd = plan.get("cwd")
    if (not isinstance(cwd, str) or not cwd.startswith("/") or cwd == "/"
            or any(part in ("", ".", "..") for part in cwd[1:].split("/"))
            or config.get("WorkingDir") != cwd):
        errors.append("container working directory mismatch")
    user = plan.get("user")
    if (not isinstance(user, str) or not re.fullmatch(r"[1-9][0-9]*:[1-9][0-9]*", user)
            or config.get("User") != user):
        errors.append("container user mismatch")
    env = plan.get("env")
    allowed = {"HOME", "LANG", "LC_ALL", "LEAN_NUM_THREADS", "LEAN_PATH", "PATH", "TZ"}
    if (not isinstance(env, dict) or set(env) - allowed or env.get("LEAN_NUM_THREADS") != "1"
            or any(not isinstance(k, str) or not isinstance(v, str) for k, v in env.items())):
        errors.append("invalid expected environment")
    else:
        actual = config.get("Env")
        if (not isinstance(actual, list) or any(not isinstance(v, str) or "=" not in v for v in actual)
                or len(actual) != len(env) or set(actual) != {k + "=" + v for k, v in env.items()}):
            errors.append("container environment mismatch")
    # Restart and healthcheck helpers could launch additional Lean processes.
    restart = host.get("RestartPolicy")
    if (not isinstance(restart, dict) or restart != {"Name": "no", "MaximumRetryCount": 0}
            or type(restart.get("MaximumRetryCount")) is not int):
        errors.append("container restart policy is not disabled")
    if "Healthcheck" not in config or config["Healthcheck"] not in (None, {"Test": ["NONE"]}):
        errors.append("container healthcheck is not explicitly disabled")
    parent = plan.get("cgroup_parent")
    if (not isinstance(parent, str) or (parent and (not parent.startswith("/") or
            any(part in ("", ".", "..") for part in parent[1:].split("/"))))
            or "CgroupParent" not in host or host["CgroupParent"] != parent):
        errors.append("container cgroup parent differs or is missing")
    cpu_fields = ("NanoCpus", "CpuQuota", "CpuPeriod", "CpuShares", "CpusetCpus", "CpusetMems")
    cpu = plan.get("cpu")
    if (not isinstance(cpu, dict) or set(cpu) != set(cpu_fields) or
            any(type(cpu.get(key)) is not int for key in cpu_fields[:4]) or
            any(cpu[key] < 0 for key in ("NanoCpus", "CpuPeriod", "CpuShares")) or cpu["CpuQuota"] < -1 or
            any(not isinstance(cpu.get(key), str) for key in cpu_fields[4:]) or
            any(key not in host or type(host[key]) is not type(cpu[key]) or host[key] != cpu[key] for key in cpu_fields)):
        errors.append("container CPU constraints differ or are missing")
    mem, swap, pids = host.get("Memory"), host.get("MemorySwap"), host.get("PidsLimit")
    if (type(mem) is not int or not 0 < mem <= 12 * GIB or type(swap) is not int or swap != mem
            or type(pids) is not int or not 0 < pids <= 128):
        errors.append("container resource limits invalid")
    if (host.get("NetworkMode") != "none" or host.get("Privileged") is not False
            or host.get("ReadonlyRootfs") is not True or host.get("PidMode") not in ("", "private")
            or host.get("IpcMode") not in ("", "private") or host.get("UTSMode") not in ("", "private")
            or host.get("CgroupnsMode") != "private"
            or host.get("CapAdd") not in (None, []) or host.get("Devices") not in (None, [])
            or host.get("DeviceRequests") not in (None, [])
            or host.get("SecurityOpt") != ["no-new-privileges"]):
        errors.append("container isolation settings invalid")
    expected = plan.get("mounts")
    if (not isinstance(expected, list) or not expected or
            any(not isinstance(m, dict) or set(m) != {"source", "destination"}
                or any(not isinstance(m[k], str) or not m[k].startswith("/") or m[k] == "/"
                       or any(part in ("", ".", "..") for part in m[k][1:].split("/")) for k in m)
                for m in expected)):
        errors.append("invalid planned mounts")
    else:
        wanted = [(m["source"], m["destination"]) for m in expected]
        if len(set(wanted)) != len(wanted) or len({m[1] for m in wanted}) != len(wanted):
            errors.append("duplicate planned mounts")
        actual = []
        for mount in mounts:
            if (not isinstance(mount, dict) or mount.get("Type") != "bind" or mount.get("RW") is not False
                    or not isinstance(mount.get("Source"), str) or not isinstance(mount.get("Destination"), str)):
                errors.append("unexpected or writable mount")
            else:
                actual.append((mount["Source"], mount["Destination"]))
        if sorted(actual) != sorted(wanted):
            errors.append("container mounts mismatch")
    return errors
