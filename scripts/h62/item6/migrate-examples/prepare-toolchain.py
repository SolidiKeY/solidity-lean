#!/usr/bin/env python3
"""Create a private serial wrapper; never alter official binaries or tracked pins."""
import argparse,hashlib,json,pathlib,shlex,subprocess
p=argparse.ArgumentParser();p.add_argument("--official",type=pathlib.Path,required=True);p.add_argument("--private",type=pathlib.Path,required=True);p.add_argument("--lock",type=pathlib.Path,required=True);p.add_argument("--archive",type=pathlib.Path);p.add_argument("--pin",type=pathlib.Path);a=p.parse_args()
if a.pin:
    pin=json.loads(a.pin.read_text());assert a.archive and hashlib.sha256(a.archive.read_bytes()).hexdigest()==pin["sha256"]
    version=pin["toolchain"].split(":v")[-1]
    for name in ("lean","lake"):
        output=subprocess.check_output([str(a.official/"bin"/name),"--version"],text=True)
        assert ("version "+version) in output,(name,output)
        member=a.archive.name.removesuffix(".tar.zst")+"/bin/"+name
        proc=subprocess.Popen(["tar","--zstd","-xOf",str(a.archive),member],stdout=subprocess.PIPE)
        digest=hashlib.file_digest(proc.stdout,"sha256").hexdigest();assert proc.wait()==0
        assert digest==hashlib.sha256((a.official/"bin"/name).read_bytes()).hexdigest(),name
        print(name+" archive-member sha256 "+digest)
assert not a.private.exists(),"refuse to replace a private installation"
a.private.mkdir(parents=True);(a.private/"bin").mkdir()
for child in a.official.iterdir():
    if child.name!="bin":(a.private/child.name).symlink_to(child.resolve())
for child in (a.official/"bin").iterdir():
    if child.name!="lean":(a.private/"bin"/child.name).symlink_to(child.resolve())
wrapper=a.private/"bin/lean";wrapper.write_text('#!/usr/bin/env bash\nset -euo pipefail\nexec flock '+shlex.quote(str(a.lock.resolve()))+' '+shlex.quote(str((a.official/"bin/lean").resolve()))+' -j1 "$@"\n');wrapper.chmod(0o755)
for name in ("lean","lake"):subprocess.run([str(a.official/"bin"/name),"--version"],check=True)
