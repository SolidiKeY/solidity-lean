"""Diagnostic-only relink with an external symbol map; original artifacts untouched."""
import gc,hashlib,importlib.util,json,os,pathlib,re,subprocess
root=pathlib.Path.cwd();work=root/".lake/native-browser-wasm";output=work/"direct";diag=work/"symbols"
diag.mkdir(exist_ok=True)
assert not (diag/"direct.wasm").exists(),"refusing diagnostic overwrite"
m=json.loads((output/"build.json").read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha((output/"direct.wasm").read_bytes())==m["wasm"]
for name,digest in m["runtimeLibraries"].items():assert sha(pathlib.Path(name).read_bytes())==digest
prefix=root/".lake/native-browser-prefix";stage=work/"build64/stage1";emcc="/emsdk/upstream/emscripten/emcc"
flags=["-I"+str(output/"include"),"-O2","-sMEMORY64=2","-mtail-call","-ffunction-sections","-fdata-sections","-DLEAN_EXPORTING","-I"+str(prefix/"include")]
identity=hashlib.sha256(json.dumps({"compiler":m["compiler"],"version":m["compilerVersion"],"headers":m["leanHeadersSha256"],"lean":m["leanCommit"]},sort_keys=True).encode()).digest()
config=(output/"include/lean/config.h").read_text()
spec=importlib.util.spec_from_file_location("closure",root/"scripts/direct-runtime-closure.py")
helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
undefined=subprocess.check_output(["/emsdk/upstream/bin/llvm-nm","--undefined-only","--format=posix",str(stage/"lib/lean/libleanrt.a")],text=True)
inputs,stats=helper.extract(root,stage,native_roots=set(re.findall(r"^(\w+) U ",undefined,re.M)))
assert stats==m["closure"]
objects=[];module_rows=[]
for (name,text,path,digest),record in zip(inputs,m["modules"],strict=True):
 assert name==record["module"] and sha(text.encode())==record["compiledCSha256"]
 key=sha(text.encode()+config.encode()+json.dumps(flags).encode()+identity)
 obj=output/(key+".o");assert obj.is_file(),name
 objects.append(str(obj));module_rows.append({"module":name,"objectKey":key,"objectSha256":sha(obj.read_bytes())})
del inputs,text;gc.collect()
command=[emcc,*flags,str(root/"web/browser/direct-bridge.c"),*objects,str(output/"initialize.c"),
 "-Wl,--start-group",str(stage/"lib/lean/libleanrt.a"),str(stage/"libuv/src/libuv/libuv.a"),str(work/"gmp-wasm64/lib/libgmp.a"),"-Wl,--end-group",
 "--no-entry","-fwasm-exceptions","-sMODULARIZE=1","-sEXPORT_NAME=createDirectVerifier","-sENVIRONMENT=worker,node",
 "-sALLOW_MEMORY_GROWTH=1","-sINITIAL_MEMORY=67108864","-sMAXIMUM_MEMORY=4294967296","-sSTACK_SIZE=16777216","-sASSERTIONS=0",
 "-sEXPORTED_FUNCTIONS=_direct_init,_direct_check,_malloc,_free","-sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString",
 "-Wl,--lto-O0,--threads=1","--emit-symbol-map","-o",str(diag/"direct.js")]
subprocess.run(command,check=True)
digest=sha((diag/"direct.wasm").read_bytes())
maps=list(diag.glob("*.symbols"));assert len(maps)==1
record={"originalWasmSha256":m["wasm"],"diagnosticWasmSha256":digest,"byteIdentical":digest==m["wasm"],"symbolMap":str(maps[0]),"symbolMapSha256":sha(maps[0].read_bytes()),"modules":module_rows,"command":command,"boundary":"Diagnostic-only symbol-map relink, existing verified objects, unchanged logical budgets/default browser configuration. Original runtime/package not modified. Original frame mapping is permitted only if byteIdentical."}
dest=root/"docs/benchmarks/directruntime-2026-11-04/before/wasm-symbol-link.json";assert not dest.exists();dest.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps({k:record[k]for k in ["byteIdentical","originalWasmSha256","diagnosticWasmSha256","symbolMap"]}))
