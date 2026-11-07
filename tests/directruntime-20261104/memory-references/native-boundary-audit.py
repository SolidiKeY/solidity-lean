"""External binary observations only; not an exhaustive absence theorem."""
import hashlib,json,pathlib,re,subprocess,sys
binary=pathlib.Path(sys.argv[1]).resolve();out=pathlib.Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
manifest=json.loads((binary.parent/'build.json').read_text());assert sha(binary)==manifest['executable']
ldd=subprocess.check_output(['ldd',str(binary)],text=True);(out/'ldd.txt').write_text(ldd)
assert not re.search(r'lib(?:Lean|leanshared|Lake|leancpp)',ldd)
symbols=subprocess.check_output(['nm','-S','--defined-only',str(binary)],text=True);(out/'symbols.txt').write_text(symbols)
names=[line.split()[-1] for line in symbols.splitlines() if line.split()]
for prefix in ['lean_expr_','lean_mk_app','lean_mk_lambda','lean_mk_pi','lean_mk_sort','l_Lean_Expr_','lean_environment_','lean_kernel_','lean_import_modules','l_Lean_Environment_','l_Lean_Kernel_']:
 assert not any(n.startswith(prefix) for n in names),prefix
assert 'solidity_direct_check' in names
assert any(n.startswith('l_Solidity_Frontend_ExecutableAst_Shared_executable') for n in names)
candidates=[n for n in names if re.search(r'Lean_(?:Elab|Meta|Parser|Environment|Kernel|Compiler|Server|Widget)',n)]
for i,name in enumerate(candidates):
 text=subprocess.check_output(['objdump','-d','--disassemble='+name,str(binary)],text=True)
 (out/f'candidate-{i}.asm').write_text(text)
result={'binary':str(binary),'binarySha256':sha(binary),'symbolCount':len(names),'namedForbiddenPrefixesAbsent':True,'dynamicLeanFrontendLibraryObserved':False,'frontendOriginCandidates':candidates,'bridgeSha256':manifest['bridgeSha256'],'closure':manifest['closure'],'boundary':'Named-symbol checks and dynamic-link observations; origin names require body review. Does not prove exhaustive forbidden-functionality absence or runtime/Source adequacy.'}
(out/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
