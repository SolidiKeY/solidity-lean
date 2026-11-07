"""Guard OT-STACK-SYMBOLS: names require exact historical WASM index/body identity.
Diagnostic relink only; no historical request/benchmark execution or runtime edit.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
root=Path.cwd();old=root/".lake/native-browser-h81/direct";out=Path(os.environ.get("NATIVE_BROWSER_SYMBOL_OUTPUT",str(root/".lake/native-browser-stack-symbols")));out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((old/"build.json").read_text());assert sha(old/"direct.wasm")==m["wasm"]=="6ae1d6db106102dc38725cb32cb1ba7996c537d1948b156d4acae1cd9139b563"
for file,pin in {**m["compiler"],**m["runtimeLibraries"]}.items():assert sha(Path(file))==pin,file
objects=sorted(old.glob("*.o"));assert len(objects)==len(m["modules"])==206
nm=m["configuredTools"]["nm"];listing=subprocess.check_output([nm,"--defined-only","--print-file-name","--format=posix",*map(str,objects)],text=True);(out/"object-symbols.txt").write_text(listing)
byinit={}
for line in listing.splitlines():
 fields=line.split()
 if len(fields)>=3 and fields[1].startswith("initialize_") and fields[2].upper()=="T":byinit.setdefault(fields[1],set()).add(fields[0].rstrip(":"))
ordered=[]
for row in m["modules"]:
 key="initialize_"+row["module"].replace(".","_");found=byinit.get(key,set());assert len(found)==1,(key,found);ordered.append(next(iter(found)))
assert len(set(ordered))==206
bridge=old/("bridge-"+m["bridgeSha256"]+".c");assert sha(bridge)==m["bridgeSha256"]
inputs=[Path(x) for x in ordered]+[bridge,old/"initialize.c"]+[Path(x) for x in m["runtimeLibraries"]];before={str(p):sha(p) for p in inputs}
prefix=root/".lake/native-browser-prefix";flags=["-I"+str(old/"include"),"-O2","-sMEMORY64=2","-mtail-call","-ffunction-sections","-fdata-sections","-DLEAN_EXPORTING","-I"+str(prefix/"include")]
libs=list(m["runtimeLibraries"]);command=[sys.executable,"-E","/emsdk/upstream/emscripten/emcc.py",*flags,str(bridge),*ordered,str(old/"initialize.c"),"-Wl,--start-group",*libs,"-Wl,--end-group","--no-entry","-fwasm-exceptions","-sMODULARIZE=1","-sEXPORT_NAME=createDirectVerifier","-sENVIRONMENT=worker,node","-sALLOW_MEMORY_GROWTH=1","-sINITIAL_MEMORY=67108864","-sMAXIMUM_MEMORY=4294967296","-sSTACK_SIZE=16777216","-sASSERTIONS=0","-sEXPORTED_FUNCTIONS=_direct_init,_direct_check,_malloc,_free","-sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString","-Wl,--lto-O0,--threads=1","--emit-symbol-map","-o",str(out/"direct.js")]
(out/"command.json").write_text(json.dumps(command,indent=2)+"\n");subprocess.run(command,check=True)
assert {str(p):sha(p) for p in inputs}==before
# Exact non-custom sections bind all function indices, bodies and signatures.
def sections(data):
 assert data[:8]==b"\x00asm\x01\x00\x00\x00";pos=8;result=[]
 while pos<len(data):
  kind=data[pos];pos+=1;n=0;shift=0
  while True:
   b=data[pos];pos+=1;n|=(b&127)<<shift;shift+=7
   if not b&128:break
  payload=data[pos:pos+n];assert len(payload)==n;pos+=n
  if kind:result.append((kind,payload))
 return result
original=(old/"direct.wasm").read_bytes();candidate=(out/"direct.wasm").read_bytes();assert sections(original)==sections(candidate),"diagnostic relink changes indexed WASM bodies/types/imports/exports"
mapfile=out/"direct.js.symbols";symbols={int(line.split(":",1)[0]):line.split(":",1)[1] for line in mapfile.read_text().splitlines()};indices=[3207,2203,2205,3126,2208,2210];assert all(i in symbols for i in indices)
report={"ticket":"OT-STACK-SYMBOLS","historicalWasmSha256":m["wasm"],"diagnosticWasmSha256":sha(out/"direct.wasm"),"exactWholeBinaryEqual":original==candidate,"nonCustomSectionsByteIdentical":True,"inputObjectOrder":ordered,"inputHashes":before,"symbolMap":{"path":str(mapfile),"sha256":sha(mapfile)},"frames":[{"index":i,"name":symbols[i]} for i in indices],"boundary":"Function-index names bound by byte-identical indexed WASM sections; diagnostic only,no benchmark/request rerun,source preservation or universal machine-correctness proof."};(out/"mapping.json").write_text(json.dumps(report,indent=2)+"\n");print(json.dumps({k:v for k,v in report.items() if k not in ["inputObjectOrder","inputHashes"]}))
