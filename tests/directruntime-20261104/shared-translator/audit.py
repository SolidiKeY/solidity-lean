"""Static extraction/trust-boundary audit; not a semantic equivalence proof."""
import hashlib, json, pathlib, re, subprocess
root=pathlib.Path(__file__).resolve().parents[3]
base='b419c3cf4f642ae519b66bebc26cdf2f7cf93574'
original=subprocess.check_output(['git','show',base+':Solidity/Tools/DirectRuntime.lean'],cwd=root,text=True)
current=(root/'Solidity/Tools/DirectRuntime.lean').read_text()
shared=(root/'Solidity/Frontend/ExecutableAst/Shared/Translate.lean').read_text()
removed=original[original.index('private def field'):original.index('/-- Plain assertion obligations')]
literals=lambda s:re.findall(r'"(?:[^"\\]|\\.)*"',s)
assert literals(removed)==literals(shared), 'reader strings/order changed'
proofBlock=lambda s:s[s.index('/-- Plain assertion obligations'):s.index('def check (request')]
assert proofBlock(original)==proofBlock(current), 'intrinsic/proof-search block changed'
export=lambda s:s[s.index('@[export solidity_direct_check]'):]
assert export(original)==export(current), 'exported JSON wrapper changed'
assert 'private partial def expression' not in current
inventory=json.loads((root/'tests/directruntime-20261104/shared-translator/coverage-inventory.json').read_text())
assert inventory['counts']['compilerSolidityKinds']==58
assert len(inventory['rawConstructors']['RawStmt'])==42
assert all(not re.search(r'^\s*(?:axiom|(?:private )?theorem.*sorry|sorry|admit)\b',p.read_text(),re.M) for p in (root/'Solidity/Frontend/ExecutableAst/Shared').glob('*.lean'))
files=subprocess.check_output(['git','diff','--name-only',base],cwd=root,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines()
allowed=lambda p:p=='Solidity/Tools/DirectRuntime.lean' or p.startswith(('Solidity/Frontend/ExecutableAst/Shared/','tests/directruntime-20261104/shared-translator/')) or p=='docs/feature-work/directruntime-shared-translator.md'
assert all(allowed(p) for p in files), 'unowned path modified'
print(json.dumps({'readerStringLiteralCount':len(literals(removed)),'intrinsicProofSearchBlock':'byte-identical','exportedWrapper':'byte-identical','ownedPathsOnly':True,'newAxiomsOrAdmittedProofs':False,'boundary':'static source audit; not runtime or semantic proof'},sort_keys=True))
