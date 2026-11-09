"""Guards H90 parity regression by freezing CR census inputs at an exact head.
No translator, fixture migration or producer pin update is performed.
"""
from pathlib import Path
import subprocess,hashlib,json
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
HEAD='e0a5ac26ed521bde70e3ce4da5120d05a991d9ca'
out=OWNED/'artifacts/h90/cr-census';out.mkdir(exist_ok=True)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',HEAD,'tests/solc'],cwd=ROOT,text=True).splitlines()
rows=[]
for path in sorted(p for p in paths if p.endswith('.ast.json')):
 data=subprocess.check_output(['git','show',HEAD+':'+path],cwd=ROOT)
 target=out/Path(path).name;target.write_bytes(data)
 rows.append({'path':path,'copy':str(target.relative_to(ROOT)),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
packet={'regression':'H90 pinned canonical-reader parity','head':HEAD,'fixtures':rows,'ownerBaseline':{'functions':1599,'existingPrinted':1446,'canonicalAdmitted':226,'both':222},'boundary':'Exact committed AST bytes. Existing printed bodies are not elaboration or source adequacy. Owner census can skip compilation-unit parse failures; All78 files including subdirectories designated by Q-H90-CENSUS option2;1599/1446/226 retained as historical only.'}
(out.parent/'cr-census-inputs.json').write_text(json.dumps(packet,indent=2)+'\n')
print(json.dumps({'head':HEAD,'candidateFixtureFiles':len(rows),'bytes':sum(r['bytes'] for r in rows)}))
