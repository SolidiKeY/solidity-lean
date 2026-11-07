#!/usr/bin/env python3
"""Guard H112 drift-baseline regeneration against absorbing newer pin changes.

Stream only the pinned Git tree's eligible Lean files into a disposable directory,
then compare its source pins to its recorded inventory. No Lean is executed.
"""
import hashlib,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
if not __debug__:
    raise SystemExit("optimized Python refused: baseline verification requires enabled assertions")
ROOT=Path(__file__).resolve().parents[4]
EXPECTED='4d98b1810853c54992feb064f1a7b028e23d8212fd2aad8b8b65e81895d7c701'
def git(*args):return subprocess.check_output(['git','--no-replace-objects',*args],cwd=ROOT)
raw=(ROOT/'scripts/g07-unrecorded-baseline.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()==EXPECTED,'immutable baseline hash mismatch'
meta=json.loads(raw);source=meta['sourceCommit']
def eligible(path):
    parts=Path(path).parts
    return path.endswith('.lean') and (len(parts)==1 or parts[0] in ('Solidity','Bridge','tests')) and not path.startswith('Solidity/Scratch/') and not any(x.startswith('.') or x in ('vendor','node_modules') for x in parts)
files=[x for x in git('ls-tree','-r','--name-only',source).decode().splitlines() if eligible(x)]
inventory=git('show',source+':scripts/g07-axiom-pins.json')
assert hashlib.sha256(inventory).hexdigest()==meta['inventorySha256'],'pinned inventory hash mismatch'
with tempfile.TemporaryDirectory(prefix='h112-reproduce-') as tmp:
    root=Path(tmp)
    proc=subprocess.Popen(['git','--no-replace-objects','archive',source,'--',*files],cwd=ROOT,stdout=subprocess.PIPE)
    with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:
        for item in archive:
            if item.isdir():continue
            assert item.isfile() and item.name in files,'unexpected archive entry'
            target=root/item.name
            assert target.resolve().is_relative_to(root),'unsafe archive path'
            target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('wb') as out:shutil.copyfileobj(archive.extractfile(item),out)
    assert proc.wait()==0,'Git archive failed'
    inv=root/'scripts/g07-axiom-pins.json';inv.parent.mkdir(parents=True,exist_ok=True);inv.write_bytes(inventory)
    code="""import {collect,compare} from MODULE;
import {readFileSync} from 'node:fs';
const {errors,changes}=compare(collect(process.argv[1]),JSON.parse(readFileSync(process.argv[1]+'/scripts/g07-axiom-pins.json')));
if(errors.length)throw Error(errors.join('\\n'));
changes.sort((a,b)=>a.key<b.key?-1:a.key>b.key?1:0);console.log(JSON.stringify(changes));""".replace('MODULE',json.dumps((ROOT/'scripts/check-axiom-pins.mjs').as_uri()))
    entries=json.loads(subprocess.check_output(['node','--input-type=module','-e',code,str(root)],cwd=ROOT))
result=dict(schema=1,sourceCommit=source,masterCommit=meta['masterCommit'],inventorySha256=meta['inventorySha256'],entries=entries)
output=(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode()
assert len(entries)==99 and hashlib.sha256(output).hexdigest()==EXPECTED,'reproduction differs from pinned99 changes'
sys.stdout.buffer.write(output)
