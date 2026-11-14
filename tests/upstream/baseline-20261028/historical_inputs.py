"""Read selected pruned validation inputs from their immutable Git snapshots."""
import hashlib
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
PINS = {
    "tests/upstream/baseline-20261028/summary.json": ("2207c1bba286538fd63e4a0ff4960ed4a593a8ab", "e0031a071dc040fed1ad329c354c330f5ec150b0"),
    "tests/upstream/baseline-20261028/final-gates/doc-paths.log.gz": ("66629757c15a819af17bb2d97e18c9bea4777351", "7339f2dcfb81bf405f987e5e0e18677146d9ac2c"),
    "tests/upstream/baseline-20261028/native-cache/validation.json": ("38871aee752a24e37c2ac6196e9539ea3fd2c03a", "387fc6f4a6c77d3a265bd2b45a7f30740c9eaf45"),
    "tests/upstream/baseline-20261028/native-cache/check-12.log.gz": ("38871aee752a24e37c2ac6196e9539ea3fd2c03a", "4fb258b95dad7fb5556368b7dd6661d9c8e6978d"),
}


def read_historical(path):
    """Prefer the working file; recover only known missing inputs from Git."""
    path = Path(path)
    if not path.is_absolute():
        path = ROOT / path
    try:
        return path.read_bytes()
    except FileNotFoundError:
        try:
            relative = path.relative_to(ROOT).as_posix()
        except ValueError:
            raise FileNotFoundError(path) from None
        if relative not in PINS:
            raise
        commit, expected = PINS[relative]
        data = subprocess.check_output(["git", "-C", str(ROOT), "show", f"{commit}:{relative}"])
        actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if actual != expected:
            raise ValueError(f"historical input blob mismatch: {relative}")
        return data
