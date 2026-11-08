"""Guard closure classification against missing or substituted historical receipts.

These exact reference bytes come from the previously published H44 archive;
no new classification, exemption, current-binary verdict or trust root is
admitted. Caller supplies the private receipt directory explicitly. No fallback
restores public evidence or executes scripts from that directory.
"""
import hashlib
import json
import os
from pathlib import Path
import stat

EXPECTED={
    'native-audit.json':'7b53d6764a4ce401b657a5caf1eb8b61a37229caa38f1407d2dc32b819e3a956',
    'native-input-identities.json':'c29c4c4bbf83f5db288b23ea59129baa7f908767b984e7b2711b4862c340f539',
    'native-stub-classification.json':'8a144c8df84b05c23b0a366949e7bff9358667435f017d8c5fbd220cfca9c1c1',
}


def pairs(items):
    result={}
    for key,value in items:
        if key in result:raise ValueError('duplicate baseline JSON key')
        result[key]=value
    return result


def load(directory):
    path=Path(directory)
    if not path.is_absolute() or path!=path.resolve(strict=True):
        raise ValueError('explicit absolute non-symlink baseline directory required')
    fd=os.open(path,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    result={}
    try:
        for name,pin in EXPECTED.items():
            f=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=fd)
            try:
                before=os.fstat(f)
                if not stat.S_ISREG(before.st_mode) or before.st_nlink!=1 or before.st_size>8*1024*1024:
                    raise ValueError('unsafe baseline receipt')
                raw=bytearray()
                while len(raw)<=before.st_size:
                    part=os.read(f,min(262144,before.st_size+1-len(raw)))
                    if not part:break
                    raw.extend(part)
                if len(raw)!=before.st_size or hashlib.sha256(raw).hexdigest()!=pin:
                    raise ValueError('baseline receipt hash mismatch: '+name)
                after=os.fstat(f);entry=os.stat(name,dir_fd=fd,follow_symlinks=False)
                signature=lambda s:(s.st_dev,s.st_ino,s.st_mode,s.st_size,s.st_nlink,s.st_mtime_ns,s.st_ctime_ns)
                if signature(before)!=signature(after) or signature(after)!=signature(entry):
                    raise ValueError('baseline receipt changed during read')
                value=json.loads(raw,object_pairs_hook=pairs)
                if not isinstance(value,dict):raise ValueError('baseline receipt must be an object')
                result[name]={'sha256':pin,'data':value}
            finally:os.close(f)
    finally:os.close(fd)
    return result
