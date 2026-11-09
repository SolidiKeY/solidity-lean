"""Guard fixed validation entry points against unlocked and unbounded builds.

Only the two tracked recipes below are admitted. Resource checks are local
kernel observations, not H127 whole-job provenance or cleanup acceptance.
The 300-second local invocation maximum includes writer-lease waiting.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import fcntl
import importlib.util
import os
from pathlib import Path
import subprocess
import time

os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
ROOT = Path(__file__).resolve().parents[3]
LOCK = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
CGROUP = Path("/sys/fs/cgroup")
OUTER = Path("/task-outer-cgroup")
MARKER = "# FIXED-ADMITTED-RECIPE\n"
ENTRIES = {
    "read-bounds": "tests/directruntime-20261104/shared-translator/read-bounds-validate.sh",
    "registration-parent": "tests/directruntime-20261104/native-browser/h109/scripts/registration-parent-checks.sh",
}


def resources():
    if os.environ.get("NATIVE_BROWSER_BOUNDED_GATE") != "1" or os.environ.get("LEAN_NUM_THREADS") != "1":
        raise RuntimeError("bounded-command admission and LEAN_NUM_THREADS=1 required")
    if ((CGROUP / "memory.max").read_text().strip(), (CGROUP / "memory.swap.max").read_text().strip()) != ("12884901888", "0"):
        raise RuntimeError("exact 12GiB/no-swap scope required")
    fields = (CGROUP / "cpu.max").read_text().split()
    if len(fields) != 2 or not all(x.isdecimal() for x in fields) or not 0 < int(fields[0]) <= int(fields[1]) or not os.sched_getaffinity(0):
        raise RuntimeError("bounded single-CPU quota and nonempty affinity required")
    maximum = (OUTER / "memory.max").read_text().strip()
    current = (OUTER / "memory.current").read_text().strip()
    if not maximum.isdecimal() or not current.isdecimal() or int(maximum)-int(current) < 4294967296:
        raise RuntimeError("4GiB outer reserve required")


def recipe(name):
    text = (ROOT / ENTRIES[name]).read_text()
    if text.count(MARKER) != 1:
        raise ValueError("fixed recipe delimiter missing or duplicated")
    return text.split(MARKER, 1)[1]


def serial_setup():
    original = (ROOT / "lakefile.toml").read_text()
    serial = original.replace('weakLeanArgs = ["--tstack=131072"]',
                              'weakLeanArgs = ["--tstack=131072", "-j1"]')
    if serial == original or (ROOT / ".lake/native-browser-serial.toml").read_text() != serial:
        raise RuntimeError("serial Lake configuration differs from current source")
    shim = ROOT / ".lake/native-browser-rowsnine-gates/bin/lake"
    tracked = ROOT / "tests/directruntime-20261104/native-browser/h109/scripts/registration-lake.sh"
    if shim.read_bytes() != tracked.read_bytes():
        raise RuntimeError("cached Lake shim differs from tracked implementation")


def run_recipe(name):
    resources()
    serial_setup()
    body = recipe(name)
    # Same action process group: the invocation supervisor owns termination.
    child = subprocess.Popen(["/bin/bash", "-c", body], cwd=ROOT)
    try:
        while child.poll() is None:
            resources()
            time.sleep(0.05)
        if child.returncode:
            raise RuntimeError("fixed validation recipe failed: " + str(child.returncode))
        resources()
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()


def main():
    start = time.monotonic_ns()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("entry", choices=tuple(ENTRIES))
    args = parser.parse_args()
    if Path.cwd().resolve() != ROOT:
        raise ValueError("run from the assigned checkout root")
    resources()  # Before opening the lease or running setup/build mutations.
    spec = importlib.util.spec_from_file_location("validation_deadline", ROOT / "tests/directruntime-20261104/native-browser/readbounds/invocation-deadline.py")
    timer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(timer)
    deadline = start + timer.MAXIMUM_NS
    # The supervisor parent owns the lease until its group cleanup/reaping ends.
    with LOCK.open("a") as lease:
        while True:
            resources()
            if time.monotonic_ns() >= deadline:
                raise TimeoutError("validation writer-lease deadline expired")
            try:
                fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                time.sleep(0.01)
        remaining = deadline - time.monotonic_ns()
        if remaining <= 0:
            raise TimeoutError("validation admission deadline expired")
        timer.execute(lambda: run_recipe(args.entry), budget_ns=remaining)


if __name__ == "__main__":
    main()
