"""Classify exact retained primitive helpers, preserving the coarse audit failure."""
import hashlib, importlib.util, json, pathlib, re, subprocess
root=pathlib.Path.cwd()
out=root/"docs/benchmarks/directruntime-2026-11-04/before"
if (out/"native-stub-classification.json").exists():raise SystemExit("Refusing classification overwrite")
binary=root/".lake/direct-native/direct-check"
sha=lambda b:hashlib.sha256(b).hexdigest()
coarse=json.loads((out/"native-audit.json").read_text())
ident=json.loads((out/"native-input-identities.json").read_text())
if sha(binary.read_bytes())!=coarse["binarySha256"] or coarse["binarySha256"]!=ident["binarySha256"]:
 raise ValueError("binary differs from audited input")
spec=importlib.util.spec_from_file_location("closure",root/"scripts/direct-runtime-closure.py")
helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
if sha((root/"scripts/direct-runtime-closure.py").read_bytes())!=ident["closureScriptSha256"]:
 raise ValueError("closure implementation changed")
nm=subprocess.check_output(["nm","--defined-only","--format=posix",str(binary)],text=True)
symbols={line.split()[0] for line in nm.splitlines() if line.split()}
metadata={m["module"]:m for m in ident["modules"]}
modules={("initialize_"+m.replace(".","_")):m for m in metadata}
flags=["-O2","-ffunction-sections","-fdata-sections","-I"+str(root/".lake/native-browser-prefix/include")]
prefix=root/".lake/native-browser-prefix"
compiler_identity=sha((prefix/"bin/clang").read_bytes())+sha((prefix/"include/lean/config.h").read_bytes())
c_calls={"lean_nat_dec_lt","lean_dec","lean_string_utf8_get","lean_uint32_dec_eq","lean_string_utf8_next","lean_obj_tag","lean_ctor_get","lean_nat_dec_eq"}
machine_calls={"lean_dec_ref_cold","lean_nat_big_lt","lean_string_utf8_get","lean_string_utf8_next","lean_nat_big_eq","lean_notify_assert","lean_inc_heartbeat","lean_internal_panic_out_of_memory","mi_malloc_small"}
records=[];failures=[]
for line in coarse["blockedDefinedSymbols"]:
 symbol=line.split()[-1]
 if symbol not in modules:
  failures.append("not a rewritten module initializer: "+symbol);continue
 module=modules[symbol]
 path=root/".lake/native-browser-lean4/stage0/stdlib"/(module.replace(".","/")+".c")
 text=path.read_text()
 if sha(text.encode())!=metadata[module]["originalCSha256"]:
  raise ValueError("original C mismatch")
 functions={m[1]:(m.start(),helper.end_brace(text,m.start()),text[m.start():helper.end_brace(text,m.start())]) for m in helper.FUNC.finditer(text)}
 live={f for f in functions if f in symbols and f!=symbol}
 if len(live)!=1: failures.append("unexpected retained helper count: "+module)
 initializer="LEAN_EXPORT lean_object* "+symbol+"(uint8_t builtin, lean_object* w) {\nreturn lean_io_result_mk_ok(lean_box(0));\n}"
 rewritten=text
 for name,(start,end,body) in sorted(functions.items(),key=lambda item:item[1][0],reverse=True):
  rewritten=rewritten[:start]+(initializer if name==symbol else body if name in live else "")+rewritten[end:]
 compiled_sha=sha(rewritten.encode())
 if compiled_sha!=metadata[module]["compiledCSha256"]:
  raise ValueError("reconstruction is not the actual compiled closure: "+module)
 key=sha((rewritten+str(flags)+compiler_identity).encode())
 obj=root/".lake/direct-native"/(key+".o")
 if not obj.is_file():raise ValueError("matching compiled object missing: "+module)
 details=[]
 for name in sorted(live|{symbol}):
  body=initializer if name==symbol else functions[name][2]
  called=set(re.findall(r"\b([A-Za-z_]\w*)\s*\(",body.split("{",1)[1]))-{"if","return","sizeof"}
  if name!=symbol and not called<=c_calls:failures.append("unexpected C primitive: "+name)
  globals={m[1] for m in helper.GLOBAL.finditer(text) if not any(a<=m.start()<b for a,b,_ in functions.values())}
  if name!=symbol and globals & set(helper.IDENT.findall(body)):
   failures.append("helper accesses a module global: "+name)
  asm=subprocess.check_output(["objdump","-d","--disassemble="+name,str(binary)],text=True)
  callees=set(re.findall(r"\bcall\s+[0-9a-f]+ <([^>]+)>",asm))
  if not callees<=machine_calls:failures.append("unexpected machine callee: "+name)
  if re.search(r"\b(?:call|jmp)\s+\*",asm):failures.append("indirect transfer: "+name)
  details.append({"symbol":name,"cBody":body,"cBodySha256":sha(body.encode()),"cCalls":sorted(called),"machineCallees":sorted(callees),"disassembly":asm})
 records.append({"module":module,"originalCSha256":metadata[module]["originalCSha256"],"compiledCSha256":compiled_sha,"objectKey":key,"objectSha256":sha(obj.read_bytes()),"functions":details})
undefined=subprocess.check_output(["nm","--undefined-only","--format=posix",str(binary)],text=True)
unresolved=[line for line in undefined.splitlines() if line.split() and line.split()[0].startswith(("l_","_init_l_","lean_","initialize_"))]
if unresolved:failures.append("unresolved Lean imports")
initializers=(root/".lake/direct-native/initialize.c").read_text()
for record in records:
 init="initialize_"+record["module"].replace(".","_")
 if "res="+init+"(1,lean_io_mk_world());" not in initializers:failures.append("initializer call list mismatch")
frontend_modules={m for m in metadata if m.startswith(("Lean.Meta","Lean.Elab","Lean.Kernel","Lean.Environment"))}
if frontend_modules!={r["module"] for r in records}:failures.append("unclassified frontend-origin module")
result={"binarySha256":ident["binarySha256"],"coarseReceiptSha256":sha((out/"native-audit.json").read_bytes()),"coarseReceiptPassed":coarse["passed"],"records":records,"unresolvedLeanImports":unresolved,"failures":failures,"passed":not failures and len(records)==len(coarse["blockedDefinedSymbols"]) and bool(records),"boundary":"Callee checks are not a general purity analyzer; independent manual body inspection supports only these exact compiled bodies. Structural classification of exact compiled primitive helpers and empty IO-success initializers, reviewed independently by finder and skeptic. No namespace exemptions; original coarse failure remains immutable. This is external evidence, not an intrinsic theorem or whole-assignment acceptance."}
(out/"native-stub-classification.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"passed":result["passed"],"classifiedInitializers":len(records),"failures":failures}))
if not result["passed"]:raise SystemExit(1)
