"""Guard full decoder validation against hidden VM inputs and unsafe restoration.
Only missing, untracked data under this lane's artifacts directory may be restored.
Tracked fixture drift fails closed; no source, gate or runtime result is substituted.
"""
import argparse,gzip,hashlib,importlib.util,io,json,pathlib,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[3]
OWN='tests/directruntime-20261104/shared-translator/'
ART=OWN+'artifacts/'
MANIFEST=ROOT/(OWN+'validation-inputs-manifest.json')
CAPTURE_BASE='16c7ecb40198fb62187f4adf8dcaee6733e4990f'
spec=importlib.util.spec_from_file_location('intake',ROOT/(OWN+'verify-sourcebuild-intake.py'))
helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
require=helper.require
sha=lambda data:hashlib.sha256(data).hexdigest()
def tracked_files(root):
 return set(subprocess.check_output(['git','ls-files'],cwd=root,text=True).splitlines())
def target(root,name):
 path=pathlib.PurePosixPath(name)
 require(not path.is_absolute() and '..' not in path.parts and str(path)==name and name not in ['', '.'],'unsafe input path')
 dest=root/name
 for parent in [dest,*dest.parents]:
  if parent==root:break
  require(not parent.is_symlink(),'symlink input path')
 require(dest.resolve().is_relative_to(root.resolve()),'input path escapes root')
 return dest

def records(manifest,tracked):
 rows=manifest['files'];require(len({r['path'] for r in rows})==len(rows),'duplicate input path')
 for row in rows:
  name=row['path'];require(row['tracked']==(name in tracked),'tracked classification changed')
  require(isinstance(row['bytes'],int) and row['bytes']>=0 and len(row['sha256'])==64,'invalid input record')
  if not row['tracked']:
   require(name.startswith(ART) and name.endswith(('.json','.txt','.tar.gz')),'unowned restore input')
 return rows

def check(root,manifest,tracked):
 missing=[];changed=[]
 for row in records(manifest,tracked):
  path=target(root,row['path'])
  if not path.exists():missing.append(row['path']);continue
  require(path.is_file(),'nonregular input')
  if path.stat().st_size!=row['bytes'] or sha(path.read_bytes())!=row['sha256']:changed.append(row['path'])
 return {'missing':missing,'changed':changed,'files':len(manifest['files'])}

def restore(root,manifest,archive,tracked):
 require(archive.stat().st_size==manifest['archive']['bytes'] and sha(archive.read_bytes())==manifest['archive']['sha256'],'input archive hash/size')
 expected={r['path']:r for r in records(manifest,tracked) if not r['tracked']}
 with tarfile.open(archive,'r:gz') as tar:
  entries=helper.members(tar);require(set(entries)==set(expected),'input archive member set')
  payload={}
  for name,row in expected.items():
   raw=tar.extractfile(name).read()
   require(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'input member hash/size')
   payload[name]=raw
 status=check(root,manifest,tracked)
 require(not status['changed'],'changed inputs; refusing overwrite')
 require(not any(p in tracked for p in status['missing']),'missing tracked inputs; restore checkout first')
 # Validate every destination before the first write; no archive extraction API.
 destinations={name:target(root,name) for name in status['missing']}
 for name,path in destinations.items():
  require(name in payload,'unarchived missing input')
  path.parent.mkdir(parents=True,exist_ok=True)
  with path.open('xb') as stream:stream.write(payload[name])
 final=check(root,manifest,tracked);require(not final['missing'] and not final['changed'],'restored input integrity')
 return {'restored':len(destinations),'files':final['files']}

def tar_members(path,digest):
 require(sha(path.read_bytes())==digest,'origin archive hash')
 proc=None
 if path.name.endswith('.zst'):
  proc=subprocess.Popen(['zstd','-dc',str(path)],stdout=subprocess.PIPE);tar=tarfile.open(fileobj=proc.stdout,mode='r|')
  data={}
  with tar:
   for m in tar:
    require(m.isfile() and m.name not in data and not pathlib.PurePosixPath(m.name).is_absolute() and '..' not in pathlib.PurePosixPath(m.name).parts,'unsafe origin member')
    data[m.name]=tar.extractfile(m).read()
  require(proc.wait()==0,'origin decompression')
  return data
 with tarfile.open(path,'r:gz') as tar:
  return {name:tar.extractfile(name).read() for name in helper.members(tar)}

def capture():
 expected={}
 def add(name,digest):
  path=target(ROOT,name);require(path.is_file() and sha(path.read_bytes())==digest,'capture input identity: '+name)
  if name in expected:require(expected[name]==digest,'conflicting input pin')
  expected[name]=digest
 def anchor(name):
  rel=OWN+name;raw=(ROOT/rel).read_bytes()
  require(raw==subprocess.check_output(['git','show',CAPTURE_BASE+':'+rel],cwd=ROOT),'unreviewed input anchor')
  add(rel,sha(raw));return json.loads(raw)
 census=anchor('h90-census-manifest.json');profile=anchor('h90-reader-profile-manifest.json')
 address=anchor('address-manifest.json');environment=anchor('environment-manifest.json')
 for m in [census,profile]:
  a=m['archive'];rel=a.get('archiveRelative',a.get('repositoryRelative'));add(rel,a['sha256'])
  data=tar_members(ROOT/rel,a['sha256'])
  if m is census:
   for name,digest in a['files'].items():
    require(sha(data[name])==digest,'census archive index');add(ART+'h90/'+name,digest)
  else:
   names={pathlib.PurePosixPath(r['profile']).name:r for r in m['files']}
   require(set(data)==set(names)|{'reader-profile-changes.json'},'profile archive member set')
   for name,raw in data.items():
    rel=names[name]['profile'] if name in names else ART+'h90/'+name
    add(rel,sha(raw))
 inputs=json.loads((ROOT/(ART+'h90/cr-census-inputs.json')).read_bytes())
 require(sha((ROOT/(ART+'h90/cr-census-inputs.json')).read_bytes())==census['inputSha256'],'census inputs identity')
 for row in inputs['fixtures']:add(row['copy'],row['sha256'])
 add(ART+'h90/measurement-base.txt',sha((census['measurementBase']+'\n').encode()))
 for name,digest in profile['inputs'].items():add(name,digest)
 for row in profile['files']:
  add(row['legacy'],row['legacySha256']);add(row['profile'],row['profileSha256'])
 for m,folder,name in [(address,'address','AddressLocals.ast.json'),(environment,'environment','EnvironmentMembers.ast.json')]:
  a=m['archive'];rel=a.get('repositoryRelative',a.get('archiveRelative'))
  data=tar_members(ROOT/rel,a['sha256']);require(name in data,'origin fixture member')
  add(ART+folder+'/'+name,sha(data[name]))
 tracked=tracked_files(ROOT)
 rows=[{'path':name,'sha256':digest,'bytes':(ROOT/name).stat().st_size,'tracked':name in tracked} for name,digest in sorted(expected.items())]
 manifest={'guardedRegression':__doc__.splitlines()[0],'captureBase':CAPTURE_BASE,'files':rows,
  'gitObjects':sorted({census['inputHead'],census['measurementBase'],'88a946c78971ef2fadc6d4ff72d7020092e6dfb6','b419c3cf4f642ae519b66bebc26cdf2f7cf93574','fcdddfcc446b5004860875f772ff6033e60c745f'}),
  'boundary':'Frozen validation data only; no executable cache, runtime input or source/semantic adequacy claim.'}
 records(manifest,tracked);require(not check(ROOT,manifest,tracked)['changed'],'capture changed input')
 raw=io.BytesIO()
 with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as zipped:
  with tarfile.open(fileobj=zipped,mode='w') as tar:
   for row in rows:
    if row['tracked']:continue
    data=(ROOT/row['path']).read_bytes();entry=tarfile.TarInfo(row['path']);entry.size=len(data);entry.mode=0o644;entry.mtime=0;tar.addfile(entry,io.BytesIO(data))
 data=raw.getvalue();digest=sha(data);rel=ART+'validation-inputs-'+digest[:16]+'.tar.gz';(ROOT/rel).write_bytes(data)
 manifest['archive']={'repositoryRelative':rel,'sha256':digest,'bytes':len(data)}
 MANIFEST.write_text(json.dumps(manifest,indent=2)+'\n')
 return {'files':len(rows),'archivedFiles':sum(not r['tracked'] for r in rows),'archive':manifest['archive']}

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--capture',action='store_true');parser.add_argument('--restore',type=pathlib.Path)
 args=parser.parse_args()
 if args.capture:print(json.dumps(capture()))
 else:
  manifest=json.loads(MANIFEST.read_text());tracked=tracked_files(ROOT)
  if args.restore:print(json.dumps(restore(ROOT,manifest,args.restore,tracked)))
  status=check(ROOT,manifest,tracked)
  status['missingGitObjects']=[ref for ref in manifest['gitObjects'] if subprocess.run(['git','cat-file','-e',ref+'^{commit}'],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode]
  print(json.dumps(status));require(not status['missing'] and not status['changed'] and not status['missingGitObjects'],'validation inputs unavailable; restore pinned data archive and listed Git objects before full validation')
