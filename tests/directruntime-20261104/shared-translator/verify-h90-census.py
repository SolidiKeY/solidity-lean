"""Guards H90 matched-reader parity and exact78-file census provenance.
Admission and printed-body observations are not elaboration/source adequacy.
"""
from pathlib import Path
import argparse,collections,hashlib,json,subprocess,tarfile,gzip,io,re
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent;OUT=OWNED/'artifacts/h90'
parser=argparse.ArgumentParser();parser.add_argument('--capture-manifest',action='store_true');args=parser.parse_args()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
AUTHORIZED_HEAD='e0a5ac26ed521bde70e3ce4da5120d05a991d9ca'
inputs=json.loads((OUT/'cr-census-inputs.json').read_text());assert inputs['head']==AUTHORIZED_HEAD,'unauthorized CR census head'
expectedPaths=sorted(p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',AUTHORIZED_HEAD,'tests/solc'],cwd=ROOT,text=True).splitlines() if p.endswith('.ast.json'))
assert len(inputs['fixtures'])==len(expectedPaths)==78
assert [r['path'] for r in inputs['fixtures']]==expectedPaths,'census fixture selection mismatch' 
for row in inputs['fixtures']:
 assert row['copy']==str((OUT/'cr-census'/Path(row['path']).name).relative_to(ROOT))
 p=ROOT/row['copy'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
 assert hashlib.sha256(subprocess.check_output(['git','show',inputs['head']+':'+row['path']],cwd=ROOT)).hexdigest()==row['sha256']
a=json.loads((OUT/'base-census-results.json').read_text());b=json.loads((OUT/'cr-census-results.json').read_text())
assert a['summary']['candidateFiles']==b['summary']['candidateFiles']==78
assert a['summary']['functions']==b['summary']['functions']==1655
assert not a['parseRefusals'] and not b['parseRefusals']
for result in [a,b]:
 rows=result['rows'];keys=[]
 for row in rows:
  assert row['fixture'] in expectedPaths and type(row['existingPrinted']) is bool and isinstance(row['canonical'],str)
  assert type(row['sourceId']) is int and row['sourceId']>0
  keys.append((row['fixture'],row['contract'],row['function'],row['sourceId']))
 assert len(set(keys))==len(keys),'duplicate census identity'
 recomputed={'candidateFiles':len(expectedPaths),'parsedUnits':len(expectedPaths)-len(result['parseRefusals']),'functions':len(rows),'existingPrinted':sum(r['existingPrinted'] for r in rows),'canonicalAdmitted':sum(r['canonical']=='ok' for r in rows),'both':sum(r['existingPrinted'] and r['canonical']=='ok' for r in rows)}
 assert result['summary']==recomputed,'census summary mismatch' 
changes=[];gains=[];refinements=[]
for old,new in zip(a['rows'],b['rows'],strict=True):
 assert {k:v for k,v in old.items() if k!='canonical'}=={k:v for k,v in new.items() if k!='canonical'},'row identity/printer changed'
 assert old['canonical']!='ok' or new['canonical']=='ok','lost admission'
 if old==new:continue
 assert re.fullmatch(r'compact verifier: unsupported type (?:(?:uint|int)[0-9]+|bytes[0-9]+|address)',old['canonical']), 'changed refusal outside narrow/fixed-byte/address local scope'
 row={'identity':{k:old[k] for k in ['fixture','contract','function','sourceId']},'before':old['canonical'],'after':new['canonical']}
 changes.append(row)
 (gains if new['canonical']=='ok' else refinements).append(row)
assert len(gains)==b['summary']['canonicalAdmitted']-a['summary']['canonicalAdmitted']
modules=['Solidity/Frontend/ExecutableAst/Shared/Translate.lean','Solidity/Frontend/ExecutableAst/Shared/Compose.lean','Solidity/Frontend/ExecutableAst/ControlTuple/Adapter.lean']
base=(OUT/'measurement-base.txt').read_text().strip()
summary={'regression':'H90 narrow/fixed-byte/address local function admission','decision':'Q-H90-CENSUS GitHub42 option2: all78 files at CR e0a5ac26','inputHead':inputs['head'],'inputSha256':sha(OUT/'cr-census-inputs.json'),'measurementBase':base,'sourceFiles':[{'path':p,'baseSha256':hashlib.sha256(subprocess.check_output(['git','show',base+':'+p],cwd=ROOT)).hexdigest(),'headSourceSha256':sha(ROOT/p)} for p in modules],'base':a['summary'],'head':b['summary'],'gains':gains,'refusalRefinements':len(refinements),'lostAdmissions':0,'historicalBaseline':{'functions':1599,'existingPrinted':1446,'canonicalAdmitted':226,'boundary':'Historical reported68-fixture baseline; exact original selection unavailable. Exploratory69-top-level run reproduced counts but is not authoritative. Not used for matched78-file parity.'},'boundary':'Printer/name-matched census and decoder admissions only; no elaboration, overload identity, whole-contract, source or backend adequacy claim.'}
manifest=OWNED/'h90-census-manifest.json'
if args.capture_manifest:
 (OUT/'census-changes.json').write_text(json.dumps(changes,indent=2)+'\n')
 files=[OUT/n for n in ['cr-census-inputs.json','base-census-results.json','cr-census-results.json','census-changes.json']]
 data=io.BytesIO()
 with gzip.GzipFile(fileobj=data,mode='wb',mtime=0) as compressed:
  with tarfile.open(fileobj=compressed,mode='w') as tar:
   for p in files:
    raw=p.read_bytes();member=tarfile.TarInfo(p.name);member.size=len(raw);member.mtime=0;tar.addfile(member,io.BytesIO(raw))
 raw=data.getvalue();digest=hashlib.sha256(raw).hexdigest();pack=OUT/('census-'+digest[:16]+'.tar.gz');pack.write_bytes(raw)
 summary['archive']={'path':str(pack),'archiveRelative':str(pack.relative_to(ROOT)),'sha256':digest,'bytes':len(raw),'files':{p.name:sha(p) for p in files}}
 manifest.write_text(json.dumps(summary,indent=2)+'\n')
else:
 expected=json.loads(manifest.read_text());archive=expected.pop('archive');assert summary==expected,'census manifest mismatch'
 pack=ROOT/archive['archiveRelative'];assert pack.stat().st_size==archive['bytes'] and sha(pack)==archive['sha256']
 seen=set()
 with tarfile.open(pack,'r:gz') as tar:
  for member in tar:
   assert member.isfile() and member.name in archive['files'] and member.name not in seen;seen.add(member.name)
   raw=tar.extractfile(member).read();assert hashlib.sha256(raw).hexdigest()==archive['files'][member.name]==sha(OUT/member.name)
 assert seen==set(archive['files'])
print(json.dumps({'base':a['summary'],'head':b['summary'],'gains':len(gains),'refusalRefinements':len(refinements),'lostAdmissions':0,'boundary':summary['boundary']}))
