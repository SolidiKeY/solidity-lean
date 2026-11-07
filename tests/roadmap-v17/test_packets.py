import copy
import gzip
import hashlib
import importlib.util
import io
from pathlib import Path
import tarfile
import unittest

spec = importlib.util.spec_from_file_location("packets", Path(__file__).resolve().parents[2]/"scripts/roadmap-v17-packets.py")
p = importlib.util.module_from_spec(spec); spec.loader.exec_module(p)


def fixture(entries=None):
    entries = entries or [("Solidity/Roadmap/V17/Client.lean", b"import Solidity.KeySort\n")]
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w", format=tarfile.USTAR_FORMAT) as t:
        for name, body in entries:
            info = tarfile.TarInfo(name); info.size = len(body)
            t.addfile(info, io.BytesIO(body))
    data = gzip.compress(raw.getvalue())
    return data, {"schema": 1, "packetSha256": hashlib.sha256(data).hexdigest(),
                  "producerHead": "a"*40,
                  "members": {n: hashlib.sha256(b).hexdigest() for n,b in entries}}


class Packets(unittest.TestCase):
    def test_positive_bytes_only(self):
        data, req = fixture(); result = p.inspect(data, req)
        self.assertFalse(result["kernelValidated"])
        self.assertFalse(result["releaseClosed"])
        self.assertIn("mandatory live replay", result["pending"])

    def test_bad_digest(self):
        data, req = fixture(); req["packetSha256"] = "0"*64
        with self.assertRaisesRegex(ValueError, "packet digest mismatch"): p.inspect(data, req)

    def test_wrong_member_hash(self):
        data, req = fixture(); req["members"][next(iter(req["members"]))] = "0"*64
        with self.assertRaisesRegex(ValueError, "member digest mismatch"): p.inspect(data, req)

    def test_missing_source(self):
        data, req = fixture(); req["members"]["Missing.lean"] = "0"*64
        with self.assertRaisesRegex(ValueError, "missing members"): p.inspect(data, req)

    def test_unexpected_source(self):
        data, req = fixture(); req["members"] = {"Other.lean": "0"*64}
        with self.assertRaisesRegex(ValueError, "unexpected member"): p.inspect(data, req)

    def test_duplicate(self):
        data, req = fixture([("X.lean", b"x"), ("X.lean", b"x")])
        with self.assertRaisesRegex(ValueError, "duplicate member"): p.inspect(data, req)

    def test_unsafe_paths(self):
        for path in (".", "../x", "/x", "a//b", "a/./b", "a\\b", ".git/config", "x\n"):
            with self.subTest(path=path), self.assertRaises(ValueError): p.safe_path(path)

    def test_wrong_head_shape(self):
        data, req = fixture(); req["producerHead"] = "main"
        with self.assertRaisesRegex(ValueError, "producer head"): p.inspect(data, req)

    def test_promotion_shape(self):
        data, req = fixture(); req["releaseClosed"] = True
        with self.assertRaisesRegex(ValueError, "request shape"): p.inspect(data, req)

    def test_truncation_and_appended_archive(self):
        data, req = fixture()
        for raw in (gzip.decompress(data)[:1024], gzip.decompress(data)*2):
            bad = gzip.compress(raw); req["packetSha256"] = hashlib.sha256(bad).hexdigest()
            with self.assertRaises(ValueError): p.inspect(bad, req)

    def test_zero_payload_without_end_blocks(self):
        data, req = fixture([("Zero.lean", bytes(1024))])
        data = gzip.compress(gzip.decompress(data)[:1536])
        req["packetSha256"] = hashlib.sha256(data).hexdigest()
        with self.assertRaisesRegex(ValueError, "missing end blocks"): p.inspect(data, req)

    def test_concatenated_gzip(self):
        data, req = fixture(); data += gzip.compress(b"")
        req["packetSha256"] = hashlib.sha256(data).hexdigest()
        with self.assertRaisesRegex(ValueError, "concatenated gzip"): p.inspect(data, req)

    def test_scalar_request(self):
        data, _ = fixture()
        for req in (None, 1, [], True):
            with self.subTest(req=req), self.assertRaisesRegex(ValueError, "request shape"):
                p.inspect(data, req)

    def test_size_bounds(self):
        data, req = fixture(); original = p.RAW
        try:
            p.RAW = 1024
            with self.assertRaisesRegex(ValueError, "raw bound"): p.inspect(data, req)
        finally: p.RAW = original

    def test_duplicate_json(self):
        with self.assertRaisesRegex(ValueError, "duplicate JSON"): p.load('{"x":1,"x":2}')

    def test_links_and_pax(self):
        for kind in ("link", "pax"):
            raw = io.BytesIO()
            with tarfile.open(fileobj=raw, mode="w", format=tarfile.PAX_FORMAT) as t:
                info=tarfile.TarInfo("X.lean")
                if kind == "link": info.type=tarfile.SYMTYPE; info.linkname="/etc/passwd"
                else: info.pax_headers={"comment":"override"}
                t.addfile(info)
            data=gzip.compress(raw.getvalue())
            req={"schema":1,"packetSha256":hashlib.sha256(data).hexdigest(),"producerHead":"a"*40,"members":{"X.lean":hashlib.sha256(b"").hexdigest()}}
            with self.assertRaises(ValueError): p.inspect(data,req)


if __name__ == "__main__": unittest.main()
