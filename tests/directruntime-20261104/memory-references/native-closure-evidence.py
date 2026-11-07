"""Replay the unchanged producer extractor and bind candidate bodies to compiled objects."""
import hashlib,importlib.util,json,pathlib,re,sys
repo,prefix,native,out=map(lambda p:pathlib.Path(p).resolve(),sys.argv[1:]);out.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
manifest=json.loads((native/'build.json').read_text());audit=json.loads((out.parent/'native-boundary/audit.json').read_text());wanted=set(audit['frontendOriginCandidates'])
spec=importlib.util.spec_from_file_location('producer_closure',repo/'scripts/direct-runtime-closure.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
inputs,closure=helper.extract(repo,native/'runtime',native_roots=set(manifest['closure']['nativeRoots']));assert closure==manifest['closure']
flags=['-O2','-ffunction-sections','-fdata-sections','-I'+str(prefix/'include')]
assert sha(native/'direct-check')==manifest['executable']
if 'buildInputs' in manifest:
 # Current producer keys bind the complete snapshotted compiler/input set.
 provenance=manifest['buildInputs'];assert isinstance(provenance,dict) and provenance
 for file,expected in provenance.items(): assert sha(pathlib.Path(file))==expected,file
 assert manifest['closureScriptSha256']==sha(repo/'scripts/direct-runtime-closure.py')
 assert provenance[str(repo/'scripts/build-direct-native.py')]==sha(repo/'scripts/build-direct-native.py')
 identity=json.dumps(provenance,sort_keys=True)
else:
 # Exact legacy producer scheme, retained for already sealed older packets.
 identity=sha(prefix/'bin/clang')+sha(prefix/'include/lean/config.h')
objects=[];found={}

for module,text,source,expected in inputs:
 assert sha(source)==expected
 key=hashlib.sha256((text+str(flags)+identity).encode()).hexdigest();obj=native/(key+'.o');assert obj.is_file(),module
 objects.append({'module':module,'compiledCSha256':hashlib.sha256(text.encode()).hexdigest(),'object':str(obj),'objectSha256':sha(obj),'original':str(source),'originalSha256':expected})
 for match in helper.FUNC.finditer(text):
  name=match[1]
  if name in wanted:
   body=text[match.start():helper.end_brace(text,match.start())];assert name not in found
   path=out/f'body-{len(found)}.c.txt';path.write_text(body+'\n');found[name]={'module':module,'body':str(path),'sha256':sha(path)}
assert set(found)==wanted,(wanted-set(found))
result={'objects':objects,'candidates':found,'extractorSha256':sha(repo/'scripts/direct-runtime-closure.py'),'builderSha256':sha(repo/'scripts/build-direct-native.py'),'nativeSha256':manifest['executable'],'closure':closure,'boundary':'Reproducible exact producer C/object provenance plus frontend-origin candidate body evidence; not an exhaustive binary functionality proof.'}
(out/'evidence.json').write_text(json.dumps(result,indent=2)+'\n');print(f'PASS{len(objects)} producer object keys;{len(found)} candidate bodies')
