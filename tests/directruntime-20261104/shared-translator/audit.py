"""Static extraction/trust-boundary audit; not a semantic equivalence proof."""
import hashlib, json, pathlib, re, subprocess
root=pathlib.Path(__file__).resolve().parents[3]
base='b419c3cf4f642ae519b66bebc26cdf2f7cf93574'
original=subprocess.check_output(['git','show',base+':Solidity/Tools/DirectRuntime.lean'],cwd=root,text=True)
current=(root/'Solidity/Tools/DirectRuntime.lean').read_text()
shared=(root/'Solidity/Frontend/ExecutableAst/Shared/Translate.lean').read_text()
removed=original[original.index('private def field'):original.index('/-- Plain assertion obligations')]
literals=lambda s:re.findall(r'"(?:[^"\\]|\\.)*"',s)
published=subprocess.check_output(['git','show','fcdddfcc446b5004860875f772ff6033e60c745f:Solidity/Frontend/ExecutableAst/Shared/Translate.lean'],cwd=root,text=True)
assert literals(removed)==literals(published), 'published extraction strings/order changed'
# Remove only the separately reviewed metadata/admission phase. Every existing
# decoding algorithm (including recursive calls and failure order) is unchanged.
# H90 is an explicit reviewed extension. Pin all three implementation bodies
# by source hash, then normalize exactly its two helpers/proof/callback before
# retaining the original byte-for-byte extraction audit below.
h90='def localPrim (j : Json)' in shared
if h90:
    approved=json.loads((root/'tests/directruntime-20261104/shared-translator/h90-census-manifest.json').read_text())
    for row in approved['sourceFiles']:
        assert hashlib.sha256((root/row['path']).read_bytes()).hexdigest()==row['headSourceSha256'], 'H90 implementation changed after review'
    begin=shared.index('/-- Shape gate for primitive expression leaves in local tuples.')
    end=shared.index('def typeNameStep',begin)
    shared=shared[:begin]+shared[end:]
    begin=shared.index('/-- A primitive local retains its source narrow spelling')
    end=shared.index('def expressionStep',begin)
    shared=shared[:begin]+shared[end:]
    shared=shared.replace('  | "MemberAccess" =>\n    let base ← field j "expression"\n    let decoded ← read base\n    let member ← str j "memberName"\n    if let some key := environmentMember? base member type then return .env key\n    return .field decoded member', '  | "MemberAccess" => return .field (← read (← field j "expression")) (← str j "memberName")')
    shared=shared.replace('statementsStep expression statements localTypeName j','statementsStep expression statements typeName j').replace('statementsStep expression statements localValueTypeName j','statementsStep expression statements typeName j')
    shared=shared.replace('H90 adds primitive narrow locals with their source spelling; parameter/state\nreaders and unrelated refusal paths retain the original fragment/errors.','The default retains the supported fragment and all original error strings.')
a=shared.index('/-- Metadata-only validation')
withoutGuards=(shared[:a]+'end Solidity.Frontend.ExecutableAst.Shared\n')
withoutGuards=withoutGuards.replace('private def decodeFunction (read : Reader)', 'def function (read : Reader)',1).replace('private def decodeContract (read : Reader)', 'def contract (read : Reader)',1)
assert withoutGuards==published, 'legacy decoding algorithm changed'
proofBlock=lambda s:s[s.index('private structure Stronger'):s.index('def check (request')]
assert proofBlock(original)==proofBlock(current), 'proof-search block changed'
intrinsic=(root/'Solidity/Frontend/ExecutableAst/Shared/Intrinsic.lean').read_text()
oldAssertion=original[original.index('private def assertionObligation'):original.index('private structure Stronger')]
oldBody=oldAssertion.split(':= do',1)[1].strip()
newBody=intrinsic.split('def assertionObligation',1)[1].split(':= do',1)[1].split('/-- One executable',1)[0].strip()
if 'def primitiveReturnObligation' in intrinsic:
    packet=json.loads((root/'tests/directruntime-20261104/shared-translator/primitive-return-manifest.json').read_text())
    assert hashlib.sha256(intrinsic.encode()).hexdigest()==packet['intrinsicSha256'], 'unreviewed primitive return helper'
    newBody=newBody.replace('  if !d.rets.isEmpty then\n    return ← primitiveReturnObligation lowerBodyLoops callPre C d box', '  unless d.rets.isEmpty do throw "plain return obligation"')
expected=oldBody.replace('  let ctx ← d.paramCtx', '  unless d.params.all (fun nt => nt.2 matches .prim _) do\n    throw "plain reference obligation"\n  let ctx ← d.paramCtx')
expected=expected.replace('(Problem.callPre C Γ false [] false [] true)', '(callPre C Γ)')
expected=expected.replace('  let (raw, st) ← (lowerBodyLoops [] 0 d.body).runFrom { funs := C.funs }\n    (ctx, RawStmt.maxIdxs d.body + 1)', '  let (raw, st) ← (do\n    let body ← renameStmts [] d.body\n    lowerBodyLoops [] 0 body).runFrom { funs := C.funs } (ctx, Scope.bodySeed C d)\n  Scope.validateScopes (d.params.map (·.1)) d.body')
assert newBody==expected, 'assertion body differs beyond explicit callbacks/reference gate and reviewed lexical preparation'
assert 'obligation lowerBodyLoops\n    (fun C Γ => Problem.callPre C Γ false [] false [] true)' in current, 'producer callbacks not pinned'
export=lambda s:s[s.index('@[export solidity_direct_check]'):]
assert export(original)==export(current), 'exported JSON wrapper changed'
assert 'private partial def expression' not in current
assert 'contract executableReader source' in current and 'function executableReader n avoid' in current, 'runtime does not use canonical composition'
inventory=json.loads((root/'tests/directruntime-20261104/shared-translator/coverage-inventory.json').read_text())
assert inventory['counts']['compilerSolidityKinds']==58
assert len(inventory['rawConstructors']['RawStmt'])==42
# Conservative source-token check, including inline sorry/private axiom forms.
# This is not a transitive theorem-axiom audit.
assert all(not re.search(r'\b(?:sorry|axiom|admit)\b', q.read_text())
           for q in (root/'Solidity/Frontend/ExecutableAst/Shared').glob('*.lean'))

# H68: this recorded publication is immutable. Moving remote refs must never
# hide committed out-of-scope changes. Updating the pin is an explicit review.
pin=json.loads((root/'tests/directruntime-20261104/shared-translator/ownership-baseline.json').read_text())
ownershipBase=pin['commit']
assert re.fullmatch(r'[0-9a-f]{40}', ownershipBase), 'invalid ownership baseline'
subprocess.run(['git','merge-base','--is-ancestor',base,ownershipBase],cwd=root,check=True)
subprocess.run(['git','merge-base','--is-ancestor',ownershipBase,'HEAD'],cwd=root,check=True)
files=subprocess.check_output(['git','diff','--name-only',ownershipBase],cwd=root,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines()
exclusive=set(pin['exclusiveFiles'])
newScopes=pin['newFileScopes']
allowed=lambda p:p in exclusive or any(p.startswith(s[:-2]) if s.endswith('/**') else p==s for s in newScopes)
assert all(allowed(p) for p in files), 'unowned path modified'
print(json.dumps({'publishedReaderStringLiteralCount':len(literals(removed)),'currentReaderChange':('H90 hash-pinned narrow locals/tuple leaves; original extraction normalized exactly' if h90 else 'whole-root metadata admission after unchanged legacy decoding'),'proofSearchBlock':'byte-identical','assertionBuilder':'callback extraction, reference gate and existing lexical renamer with scope/freshness checks','exportedWrapper':'byte-identical','ownedPathsOnly':True,'ownershipComparisonBase':ownershipBase,'ownershipBaselineRecord':'ownership-baseline.json','newAxiomsOrAdmittedProofs':False,'boundary':'static source audit; not runtime or semantic proof'},sort_keys=True))
