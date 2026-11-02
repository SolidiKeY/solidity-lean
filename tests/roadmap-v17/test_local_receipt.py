import gzip
import hashlib
import importlib.util
import io
from pathlib import Path
import tarfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location("local_receipt",ROOT/"scripts/roadmap-v17-local-receipt.py")
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)


def wire(change=None):
    files={"payload"+str(i)+".json":b"{}\n" for i in range(15)}
    files["SHA256SUMS"]="".join(hashlib.sha256(data).hexdigest()+"  "+name+"\n" for name,data in files.items()).encode()
    if change:change(files)
    raw=io.BytesIO()
    with tarfile.open(fileobj=raw,mode="w",format=tarfile.USTAR_FORMAT) as t:
        for name,data in files.items():
            info=tarfile.TarInfo(name);info.size=len(data);t.addfile(info,io.BytesIO(data))
    return gzip.compress(raw.getvalue())


class CapsuleGuards(unittest.TestCase):
    def test_wire_only_integrity_not_proof(self):
        raw=wire();receipt,members=x.capsule(raw,hashlib.sha256(raw).hexdigest())
        self.assertEqual(len(members),16);self.assertTrue(receipt["byteIntegrityVerified"])
        self.assertFalse(receipt["kernelValidated"]);self.assertFalse(receipt["selectorsAuthenticated"])

    def test_wrong_whole_hash(self):
        with self.assertRaisesRegex(ValueError,"hash mismatch"):x.capsule(wire(),"0"*64)

    def test_payload_corruption_and_omission(self):
        for change in (lambda files:files.update({"payload1.json":b"corrupt"}),lambda files:files.pop("payload1.json")):
            raw=wire(change)
            with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_unsafe_payload_and_extra_member(self):
        for name in ("../outside","/outside","extra"):
            raw=wire(lambda files:files.update({name:b"x"}))
            with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_truncation_and_concatenated_gzip(self):
        for raw in (wire()[:-5],wire()+gzip.compress(b"")):
            with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_link_device_and_duplicate_members(self):
        valid=gzip.decompress(wire())
        with tarfile.open(fileobj=io.BytesIO(valid),mode="r:") as t:
            entries=[(member.name,t.extractfile(member).read()) for member in t]
        for kind in (tarfile.SYMTYPE,tarfile.LNKTYPE,tarfile.CHRTYPE,"duplicate"):
            out=io.BytesIO()
            with tarfile.open(fileobj=out,mode="w",format=tarfile.USTAR_FORMAT) as t:
                for index,(name,data) in enumerate(entries):
                    member=tarfile.TarInfo(name);member.size=len(data)
                    if index==0 and kind!="duplicate":
                        member.type=kind;member.linkname="/outside";member.size=0;t.addfile(member)
                    else:t.addfile(member,io.BytesIO(data))
                if kind=="duplicate":
                    member=tarfile.TarInfo(entries[0][0]);member.size=0;t.addfile(member,io.BytesIO())
            raw=gzip.compress(out.getvalue())
            with self.subTest(kind=kind),self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_zero_last_payload_without_end_blocks(self):
        files={"payload"+str(i)+".json":b"{}" for i in range(14)};files["payload14.json"]=bytes(1024)
        checks="".join(hashlib.sha256(data).hexdigest()+"  "+name+"\n" for name,data in files.items()).encode()
        out=io.BytesIO()
        with tarfile.open(fileobj=out,mode="w",format=tarfile.USTAR_FORMAT) as t:
            for name,data in [("SHA256SUMS",checks),*files.items()]:
                member=tarfile.TarInfo(name);member.size=len(data);t.addfile(member,io.BytesIO(data))
        raw=out.getvalue()
        with tarfile.open(fileobj=io.BytesIO(raw),mode="r:") as t:
            for _ in t:pass
            end=t.offset
        compressed=gzip.compress(raw[:end])
        with self.assertRaisesRegex(ValueError,"end blocks"):x.capsule(compressed,hashlib.sha256(compressed).hexdigest())

    def test_timestamp_only_pax_metadata_not_payload_or_proof(self):
        source=gzip.decompress(wire())
        with tarfile.open(fileobj=io.BytesIO(source),mode="r:") as t:
            entries=[(m.name,t.extractfile(m).read()) for m in t]
        for metadata,accepted in (({"mtime":"123.456"},True),({"path":"../outside"},False)):
            out=io.BytesIO()
            with tarfile.open(fileobj=out,mode="w",format=tarfile.PAX_FORMAT) as t:
                for name,data in entries:
                    item=tarfile.TarInfo(name);item.size=len(data);item.pax_headers=metadata;t.addfile(item,io.BytesIO(data))
            raw=gzip.compress(out.getvalue())
            if accepted:
                receipt,_=x.capsule(raw,hashlib.sha256(raw).hexdigest());self.assertFalse(receipt["kernelValidated"])
            else:
                with self.assertRaises(ValueError):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_timestamp_cannot_hide_gnu_extension(self):
        base=gzip.decompress(wire());body=b"mtime=123.456\n";length=len(body)+3
        while True:
            record=str(length).encode()+b" "+body
            if len(record)==length:break
            length=len(record)
        def block(name,kind,data):
            info=tarfile.TarInfo(name);info.type=kind;info.size=len(data)
            return info.tobuf(format=tarfile.USTAR_FORMAT)+data+bytes((-len(data))%512)
        prefix=block("pax",tarfile.XHDTYPE,record)+block("longname",tarfile.GNUTYPE_LONGNAME,b"payload0.json\0")
        raw=gzip.compress(prefix+base)
        with self.assertRaisesRegex(ValueError,"non-PAX capsule extension"):x.capsule(raw,hashlib.sha256(raw).hexdigest())

    def test_payload_limit(self):
        raw=wire(lambda files:files.update({"payload1.json":bytes(201*1024)}))
        with self.assertRaisesRegex(ValueError,"bound"):x.capsule(raw,hashlib.sha256(raw).hexdigest())


if __name__=="__main__":unittest.main()
