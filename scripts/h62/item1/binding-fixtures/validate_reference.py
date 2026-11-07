"""Guard isolated reference-fixture proofs against producer edits and false acceptance.
Validate under the existing bounded runner. Pack retained evidence deterministically;
no fixture extraction, relation unification or runtime qualification is performed.
"""
import argparse,gzip,hashlib,io,json,os,pathlib,re,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[4]
AREA=ROOT/'tests/h62/item1/binding-fixtures'
OUT=AREA/'artifacts/reference-fixture'
BASE='a10b60f23315b62e3ebf6ef925f87516ce7bca69'
ORIGINAL='Solidity/Lowering/V07/P12Controls.lean'
ORIGINAL_SHA='c62269e9eb79c411fcdfa96544681cf54c19093e9471a109ae90a6116c59ebbf'
MODULE='tests/h62/item1/binding-fixtures/ReferenceFixtureControls.lean'
OWNERSHIP='tests/directruntime-20261104/shared-translator/ownership-baseline.json'
NAMES=['memory_pair_unique','storage_pair_unique','memory_absent_refused',
       'storage_absent_refused','reference_pairs_inhabited']
def sha(raw):return hashlib.sha256(raw).hexdigest()
def require(ok,message):
 if not ok:raise ValueError(message)
def scope():
 changed=subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT,text=True).splitlines()
 changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=ROOT,text=True).splitlines()
 require(all(p.startswith(('tests/h62/item1/binding-fixtures/','scripts/h62/item1/binding-fixtures/')) or
             p in ['docs/feature-work/h62-1-binding-fixtures.md',OWNERSHIP] for p in changed),'unowned path changed')
 oldpin=json.loads(subprocess.check_output(['git','show',BASE+':'+OWNERSHIP],cwd=ROOT))
 newpin=json.loads((ROOT/OWNERSHIP).read_text());fields={'commit','publishedAncestor','publication'}
 require({k:v for k,v in oldpin.items() if k not in fields}==
         {k:v for k,v in newpin.items() if k not in fields},'ownership scope expanded')
 require(newpin['commit']==BASE and newpin['publishedAncestor']==BASE,
         'ownership publication pin')
 expected_source=subprocess.check_output(['git','show',BASE+':'+ORIGINAL],cwd=ROOT)
 require(sha(expected_source)==ORIGINAL_SHA,'pinned original Git identity')
 expected={'head':BASE,'original':ORIGINAL,'originalSha256':ORIGINAL_SHA}
 OUT.mkdir(parents=True,exist_ok=True)
 record=OUT/'base.json'
 if record.exists():require(json.loads(record.read_text())==expected,'altered base record')
 else:record.write_text(json.dumps(expected,indent=2)+'\n')
 saved=expected
 original=(ROOT/saved['original']).read_bytes()
 require(saved['head']==BASE and sha(original)==saved['originalSha256'] and
         original==subprocess.check_output(['git','show',BASE+':'+saved['original']],cwd=ROOT),
         'original P12 source changed')
 return saved

def validate():
 saved=scope()
 subprocess.run(['python3','tests/directruntime-20261104/shared-translator/audit.py'],cwd=ROOT,check=True)
 source=(ROOT/MODULE).read_text()
 require(not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b',source,re.M),'new trust shortcut')
 require(re.findall(r'^theorem\s+([^\s(]+)',source,re.M)==NAMES,'theorem inventory')
 logpath=OUT/'gates/1.log'
 logpath.unlink(missing_ok=True)
 gate_env={**os.environ,'GATE_LOGS':str(OUT/'gates')}
 subprocess.run(['bash','scripts/coord-tools/gate.sh','per-file',MODULE],cwd=ROOT,env=gate_env,check=True)
 require(logpath.is_file(),'missing fresh gate log')
 log=logpath.read_text()
 axioms={}
 for name in NAMES:
  full='Solidity.H62.BindingFixtures.'+name
  match=re.search(re.escape("'"+full+"'")+r' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)',log)
  require(match is not None,'missing axiom report: '+name)
  found=sorted(x.strip() for x in (match[1] or '').split(',') if x.strip())
  require(set(found)<= {'propext','Classical.choice','Quot.sound'},'custom axiom: '+name)
  axioms[name]=found
 baseline={}
 for name in ['BindingRel','initial']:
  full='Solidity.Lowering.V07.P12Controls.'+name
  match=re.search(re.escape("'"+full+"'")+r' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)',log)
  require(match is not None,'missing original axiom report: '+name)
  baseline[name]=sorted(x.strip() for x in (match[1] or '').split(',') if x.strip())
 require(all(set(found)<=set(baseline['initial']) for found in axioms.values()),'axioms beyond existing fixture')
 report={'baselineAxioms':baseline,'guardedRegression':__doc__.splitlines()[0],'checkpointBase':BASE,
         'originalUnchanged':saved,'testModule':{'repositoryRelative':MODULE,'sha256':sha(source.encode())},
         'axioms':axioms,'theorems':NAMES,'productionEdits':False,
         'scope':'Five isolated P12 reference-branch controls at fixed target.H; all four extraction checkpoints remain open.',
         'timingBoundary':'New additive test file has no pre-work equivalent. Gate wall times are checking evidence only; before/after extraction timings remain pending.',
         'boundary':'Existing fixture properties and explicit inhabited pairs only; no source/world/compiler/native transport or arbitrary heap/content equivalence.'}
 (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report))

def pack():
 scope()
 files=sorted(p for p in OUT.rglob('*') if p.is_file() and p.name!='SHA256SUMS')
 require(not any(p.is_symlink() for p in files),'symlink evidence')
 (OUT/'SHA256SUMS').write_text(''.join(f'{sha(p.read_bytes())}  {p.relative_to(OUT)}\n' for p in files))
 files=sorted(files+[OUT/'SHA256SUMS'])
 def encoded():
  raw=io.BytesIO()
  with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as zipped:
   with tarfile.open(fileobj=zipped,mode='w') as tar:
    for p in files:
     data=p.read_bytes();info=tarfile.TarInfo(str(p.relative_to(OUT)))
     info.size=len(data);info.mode=0o644;info.mtime=0;info.uid=info.gid=0
     tar.addfile(info,io.BytesIO(data))
  return raw.getvalue()
 raw=encoded();require(raw==encoded(),'nondeterministic evidence encoding')
 archive=AREA/'artifacts/reference-fixture-evidence.tar.gz';archive.write_bytes(raw)
 with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as tar:
  members=tar.getmembers();require(len(members)==len(files),'evidence denominator')
  for member,p in zip(members,files,strict=True):
   require(member.isfile() and member.name==str(p.relative_to(OUT)) and
           tar.extractfile(member).read()==p.read_bytes(),'evidence roundtrip')
 report=json.loads((OUT/'report.json').read_text())
 manifest={'guardedRegression':report['guardedRegression'],'checkpointBase':BASE,
           'report':report,'archive':{'repositoryRelative':str(archive.relative_to(ROOT)),
               'path':str(archive),'sha256':sha(raw),'bytes':len(raw),'regularMembers':len(files)},
           'sourceFiles':[{'repositoryRelative':str(p.relative_to(ROOT)),'sha256':sha(p.read_bytes())}
                          for p in [ROOT/MODULE,pathlib.Path(__file__).resolve(),ROOT/OWNERSHIP]],
           'reviews':json.loads((OUT/'reviews.json').read_text()),
           'registration':'Test-only module candidate; no generated root, module map or production import changed.',
           'initialVerifier':'Multiline theorem-name pattern failed before the Lean gate; exit1 retained in inventory-parser-failure.log. Parser fixed; statements unchanged.',
           'initialMcp':'Incomplete response during cold dependency setup; exit2 retained. Explicit bounded P12 build then cached MCP passed.',
           'limits':['No original/producer/relation/frozen statement edits. No extraction checkpoint or timing delta claimed.',
                     'Original whole assignment and all runtime/source/compiler/performance obligations remain unfinished.']}
 (AREA/'reference-fixture-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps(manifest['archive']))
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--pack',action='store_true')
 args=parser.parse_args();pack() if args.pack else validate()
