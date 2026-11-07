#!/usr/bin/env python3
"""Resolve immutable H44 evidence from the committed path/size/SHA256 manifest."""
from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[4]
MANIFEST = ROOT / "tests/h62/item6/migrate-optimizer/BULK-MANIFEST.json"
def metadata():
    return json.loads(MANIFEST.read_text())
def bulk_path(name):
    entry = metadata()["files"]["tests/h62/item6/migrate-optimizer/" + name]
    path = Path(entry["path"])
    if not path.is_file():
        raise FileNotFoundError(f"Restore H44 evidence from {metadata()['archive']['path']}: {path}")
    assert path.stat().st_size == entry["bytes"], f"bulk size mismatch: {path}"
    with path.open("rb") as stream:
        assert hashlib.file_digest(stream, "sha256").hexdigest() == entry["sha256"], f"bulk digest mismatch: {path}"
    return path
def load_bulk_json(name):
    return json.loads(bulk_path(name).read_text())
def derived_directory():
    path = Path(metadata()["derived_output_directory"])
    assert not path.is_relative_to(ROOT), "bulk output must be outside the checkout"
    path.mkdir(parents=True, exist_ok=True)
    return path

def pack_archive(destination):
    """Repack verified historical payloads deterministically, outside Git."""
    import gzip, tarfile
    destination = Path(destination).resolve()
    assert not destination.is_relative_to(ROOT.resolve()), "archive output must be outside checkout"
    entries = metadata()["files"]
    with destination.open("xb") as raw:
        with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.USTAR_FORMAT) as archive:
                for relative in sorted(entries):
                    path = bulk_path(Path(relative).name)
                    info = tarfile.TarInfo(relative)
                    info.size = path.stat().st_size
                    info.mode = 0o644
                    info.mtime = 0
                    with path.open("rb") as source:
                        archive.addfile(info, source)
    return destination
if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pack", type=Path, help="create a deterministic archive outside checkout")
    args = parser.parse_args()
    if args.pack:
        print(pack_archive(args.pack))
    else:
        for relative in sorted(metadata()["files"]):
            print(bulk_path(Path(relative).name))
