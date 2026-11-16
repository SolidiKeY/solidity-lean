"""Read the frozen audit snapshot directly from Git objects, never live sources."""
import subprocess,tarfile
from pathlib import Path
BASE="d4ad633a9624263a59b14fd2c520b9bc602f88f3"
ROOT=Path(__file__).resolve().parents[4]

def read_base_blobs(paths):
    wanted=set(paths);result={}
    proc=subprocess.Popen(["git","archive","--format=tar",BASE],cwd=ROOT,stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=proc.stdout,mode="r|") as archive:
            for member in archive:
                if member.name in wanted:
                    assert member.isfile(),member.name
                    result[member.name]=archive.extractfile(member).read()
    finally:
        proc.stdout.close()
        status=proc.wait()
    if status:raise RuntimeError("git archive failed: "+str(status))
    return result
