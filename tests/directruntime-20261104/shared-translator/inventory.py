"""Reproducible source census, deliberately separate from semantic/runtime gates."""
import hashlib, json, pathlib, re, subprocess
root = pathlib.Path(__file__).resolve().parents[3]
owned = pathlib.Path(__file__).resolve().parent
base = 'b419c3cf4f642ae519b66bebc26cdf2f7cf93574'
upstream = '1835d247de183f23e7b0e2bc4a50732af525b77c'
def read(path): return (root/path).read_text()
def sha(path): return hashlib.sha256((root/path).read_bytes()).hexdigest()
def refs(path, text):
    return [f'{path}:{i}' for i,line in enumerate(read(path).splitlines(),1) if '"'+text+'"' in line]
admissionPath = 'Solidity/Frontend/SolcJson/Admission.lean'
a = read(admissionPath)
a = a[a.index('private def nodeFeatures'):a.index('private def diagnostic')]
branches = list(re.finditer(r'^  \| "([A-Z]\w+)"', a, re.M))
recognized = {m[1] for m in branches} | {'InlineAssembly'}
exporterPath = str((owned/'evidence/upstream/ASTJsonExporter.cpp').relative_to(root))
exporter = read(exporterPath)
# All uppercase literal names in this pinned exporter are node names except
# the assembly field AST and the literal's Unknown token. Fail on drift.
emitted = set(re.findall(r'"([A-Z]\w+)"', exporter)) - {'AST','Unknown'}
assert emitted == recognized, (emitted-recognized, recognized-emitted)
data = (root/exporterPath).read_bytes()
assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == 'b855c19efcb9061c7b19b696cf7045f25e78dc74'
catalog = json.loads(read('docs/solidity-features.json'))
features = {x['id']:x for x in catalog['features']}
nodeFeatures = {}
for i,m in enumerate(branches):
    text=a[m.start():branches[i+1].start() if i+1<len(branches) else len(a)]
    nodeFeatures[m[1]]=sorted(set(re.findall(r'\.([a-z]\w+)',text)) & features.keys())
# Helper-dispatched features are conditional alternatives, not unconditional
# claims about every occurrence of a node kind.
fullAdmission = read(admissionPath)
for kind, start, end in [
    ('PragmaDirective', 'private def pragmaFeatures', 'private def nodeFeatures'),
    ('Identifier', 'private def builtinFeatures', 'private def pragmaFeatures'),
    ('MemberAccess', 'private def magicMember', 'private def builtinFeatures')]:
    text=fullAdmission[fullAdmission.index(start):fullAdmission.index(end)]
    nodeFeatures[kind]=sorted(set(nodeFeatures[kind]) | (set(re.findall(r'\.([a-z]\w+)',text)) & features.keys()))
nodeFeatures['InlineAssembly']=[f for f in ['inlineAssembly','canonicalRethrow'] if f in features]
# Admission.walk appends these conditional alternatives outside nodeFeatures.
for kind, alternatives in {'UnaryOperation':['operatorAliases'],
    'BinaryOperation':['operatorAliases','fixedPoint'],
    'MemberAccess':['emptyDataValueCall']}.items():
    nodeFeatures[kind]=sorted(set(nodeFeatures[kind]) | (set(alternatives) & features.keys()))

rawMap = {
 'Identifier':['RawExpr.name'], 'MemberAccess':['RawExpr.field','RawExpr.env'],
 'Literal':['RawExpr.num','RawExpr.bool','RawExpr.call (existing bytesLitName byte-literal encoding)'], 'UnaryOperation':['RawExpr.unop','RawExpr.incDec','RawStmt.delete'],
 'BinaryOperation':['RawExpr.binop'], 'Conditional':['RawExpr.ternary'], 'IndexAccess':['RawExpr.index'],
 'IndexRangeAccess':['RawExpr.call (existing slice lowering)'], 'TupleExpression':['RawExpr.tuple','RawExpr.call (inline arrays)'],
 'Assignment':['RawExpr.assign','RawExpr.opAssign','RawStmt.assign','RawStmt.tupleAssign'],
 'FunctionCall':['RawExpr.call','RawExpr.named','RawExpr.modular','RawStmt.call','RawStmt.assert','RawStmt.require'],
 'NewExpression':['RawExpr.newArr'], 'Block':['RawStmt.block'], 'UncheckedBlock':['RawStmt.unchecked'],
 'IfStatement':['RawStmt.ite'], 'WhileStatement':['RawStmt.whileLoop'], 'ForStatement':['RawStmt.forLoop'],
 'DoWhileStatement':['RawStmt.doWhile'], 'Break':['RawStmt.brk'], 'Continue':['RawStmt.cont'],
 'Return':['RawStmt.ret'], 'VariableDeclarationStatement':['RawStmt.decl','RawStmt.declMemory','RawStmt.declStorage','RawStmt.tupleDecl'],
 'ExpressionStatement':['RawStmt.assign','RawStmt.call','RawStmt.eval'],
 'RevertStatement':['RawStmt.revertErr'], 'EmitStatement':['RawStmt.eval'],
 'TryStatement':['RawStmt.tryCall'], 'TryCatchClause':['RawStmt.tryCall clause'],
 'InlineAssembly':['RawStmt.revertRaw (canonical byte rethrow only)'],
 'PlaceholderStatement':['RawStmt.hole'], 'ElementaryTypeName':['RawTy.named'],
 'UserDefinedTypeName':['RawTy.named'], 'ArrayTypeName':['RawTy.array','RawTy.fixed'], 'Mapping':['RawTy.mapping'],
 'FunctionTypeName':['RawTy.named (existing function-tag type lowering)'],
 'ElementaryTypeNameExpression':['RawExpr.call (existing conversion lowering)'],
 'FunctionDefinition':['FunDecl'], 'VariableDeclaration':['Contract.vars / parameter / RawStmt.decl'],
 'ParameterList':['FunDecl.params / FunDecl.rets'],
}
partial = {'ElementaryTypeName','ArrayTypeName','Mapping','Literal','Identifier','IndexAccess','MemberAccess','BinaryOperation','UnaryOperation','Conditional','Block','UncheckedBlock','Return','IfStatement','VariableDeclarationStatement','WhileStatement','ForStatement','Break','Continue','ExpressionStatement','Assignment','FunctionCall','FunctionDefinition','VariableDeclaration','ParameterList','ContractDefinition','StructuredDocumentation'}
control = {'TupleExpression','TryStatement','TryCatchClause','WhileStatement','ForStatement','DoWhileStatement','Break','Continue','Return','IfStatement'}
reference = {'ArrayTypeName','Mapping','UserDefinedTypeName','IndexAccess','IndexRangeAccess','NewExpression','VariableDeclarationStatement'}
producer = {'SourceUnit','PragmaDirective','ImportDirective','StorageLayoutSpecifier','InheritanceSpecifier','UsingForDirective','StructDefinition','EnumDefinition','EnumValue','UserDefinedValueTypeDefinition','OverrideSpecifier','ModifierDefinition','ModifierInvocation','EventDefinition','ErrorDefinition','IdentifierPath','FunctionTypeName'}
rows=[]
for kind in sorted(emitted):
    ids=nodeFeatures.get(kind,[])
    evidence=sorted({p for f in ids for p in features[f]['localEvidence'] if (root/p).exists()})
    rows.append({'nodeType':kind,'compilerExporter':refs(exporterPath,kind),
      'admission':{'recognized':True,'featureIds':ids,'featureMapping':'conservative conditional union of nodeFeatures, helpers and Admission.walk; actual feature use depends on fields/declaration identity/payment context','source':refs(admissionPath,kind)},
      'defaultExecutableReader':{'admission':'partial/context-dependent' if kind in partial else 'refused/not a standalone reader input',
        'source':refs('Solidity/Frontend/ExecutableAst/Shared/Translate.lean',kind)},
      'existingSolcJson':{'source':refs('Solidity/Frontend/SolcJson/Body.lean',kind)+refs('Solidity/Frontend/SolcJson/Contract.lean',kind),
        'note':'Source references locate dispatch/normalization; they are not a per-form support or proof verdict.'},
      'rawMappingCompleteness':'source encoding examples; full subtype mapping still pending',
      'existingElaborationInput':rawMap.get(kind,['contract metadata/type/specification wrapper; no standalone Raw statement']),
      'intrinsic':{'input':'existing Raw only, then elabProgAtS.go/specObligation',
        'admissionGate':'per-form fixture elaboration pending',
        'proofClosure':'No AST-to-solc semantic equivalence theorem supplied by this extraction; intrinsic proofs unchanged.'},
      'semanticSupport':{'catalog':[{k:features[f][k] for k in ('id','scope','current','requirement')} for f in ids],
        'evidence':evidence},
      'backendGap':'Fresh native/WASM closure and construct-specific backend evidence pending; source admission is not backend correctness.',
      'owners':{'implementation':'C' if kind in control else 'B' if kind in reference else 'CR' if kind in producer else 'A',
        'sharedAndDirectRuntime':'A','existingImportMigration':'CR',
        'nativeBrowserScripts':'DR-D (registered native/browser script scopes)',
        'admissionP8Migration':'CR', 'sourceH16':'VY5 (frozen; integration owner only)',
        'backendPasses':'V09 Passes', 'sourceLowering':'V08 Lowering/V08',
        'memoryOperations':'V11 MemoryOps (reference-dependent forms)',
        'aggregates':'V16 Aggregates/Roadmap (aggregate-dependent forms)'},
      'positiveNegativeRegressions':{'status':'full per-construct controls pending',
        'existingSourceCandidates':[p for p in evidence if p.startswith(('tests/','Solidity/Examples/'))]}})
# Observation matrices pin whole-witness reader behavior, not form-level semantics.
for prefix,casePrefix,label in [('', '', 'existingFixture'),('fresh-', 'fresh-', 'freshCompilerFixture'),('composed-', '', 'composedExistingFixture'),('composed-fresh-', 'fresh-', 'composedFreshCompilerFixture')]:
 matrix=owned/(prefix+'construct-reader-matrix.json');casefile=owned/(casePrefix+'construct-reader-cases.json')
 if matrix.exists() and casefile.exists():
  observed={r['nodeType']:r for r in json.loads(matrix.read_text())}
  cases={r['nodeType']:r for r in json.loads(casefile.read_text())['cases']}
  for row in rows:
   kind=row['nodeType']
   if kind not in observed:continue
   item=observed[kind];case=cases[kind]
   row.setdefault('standaloneReaderObservations',{})[label]={
    'stage':'Whole-witness decoding with existing root metadata checks; child refusals may dominate. No intrinsic, identity-resolution, semantic or backend support verdict.',
    'readerConfiguration':'Shared.executableReader' if prefix.startswith('composed-') else 'Shared.reader',
    'matrix':str(matrix.relative_to(root)),'cases':str(casefile.relative_to(root)),
    'route':item['route'],'natural':item['natural'],'unknownRoot':item['unknownRoot'],
    'producerExpression':item['producerExpression'],
    'sourceIdentity':{key:case.get(key) for key in ['fixture','fixtureSha256','pointer','nodeId','src','line','compilerVersion','compilerSha256']}}
   row['positiveNegativeRegressions']['status']='Standalone observations present; intrinsic/context/source/backend controls remain pending.'

yulPath='Solidity/Frontend/SolcJson/Yul.lean'
yul=sorted(set(re.findall(r'"(Yul[A-Z]\w+)"',read(yulPath))))
rawPath='Solidity/Syntax/Raw.lean'
raw={}
for name in ('RawTy','RawExpr','RawInv','RawStmt'):
    section=read(rawPath).split('inductive '+name+' where',1)[1].split('deriving',1)[0]
    raw[name]=re.findall(r'^  \| (\w+)',section,re.M)
# Static local import closure. Runtime closure is a separate generated-C gate.
seen={}
def visit(module):
    path=module.replace('.','/')+'.lean'
    if module in seen or not (root/path).exists(): return
    seen[module]={'path':path,'sha256':sha(path)}
    for dep in re.findall(r'^import ([\w.]+)',read(path),re.M): visit(dep)
visit('Solidity.Frontend.ExecutableAst.Shared.Translate')
rawClosure=dict(seen)
seen={}
visit('Solidity.Frontend.ExecutableAst.Shared.Intrinsic')
intrinsicClosure=dict(seen)
assert all(n in {'Solidity.Frontend.ExecutableAst.Shared.Intrinsic', 'Solidity.Frontend.ExecutableAst.Shared.Scope'} or not n.startswith('Solidity.Frontend.') for n in seen)
seen={}
visit('Solidity.Frontend.ExecutableAst.Shared.Compose')
composedClosure=dict(seen)
assert 'Solidity.Frontend.Import' not in seen and 'Solidity.Frontend.Testing' not in seen
seen=rawClosure
assert 'Solidity.Frontend.Import' not in seen and 'Solidity.Frontend.Testing' not in seen
result={'schemaVersion':1,'status':'initial census; full coverage gates pending','base':base,
 'headAtGeneration':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
 'upstream':{'commit':upstream,'exporterGitBlob':'b855c19efcb9061c7b19b696cf7045f25e78dc74','exporterSha256':sha(exporterPath)},
 'counts':{'compilerSolidityKinds':len(emitted),'recognizedYulKinds':len(yul),'catalogFeatures':len(features)},
 'constructs':rows,'yulConstructs':[{'nodeType':k,'source':refs(yulPath,k),'owner':'CR existing producer; A preserves refusal',
 'direct':'refused','raw':'canonical memory-byte rethrow is separate; no general Yul-to-Raw admission',
 'proofClosure':'decoder/static/shape derivations are not whole-Solidity semantic equivalence',
 'backend':'whole-assembly execution/compiled closure not established'} for k in yul],
 'rawConstructors':raw,'localSharedImportClosure':seen,'localIntrinsicImportClosure':intrinsicClosure,'localComposedImportClosure':composedClosure,
 'sourceProvenance':{p:sha(p) for p in [admissionPath,'Solidity/Frontend/SolcJson/Body.lean','Solidity/Frontend/SolcJson/Contract.lean',rawPath,'docs/solidity-features.json']},
 'featureCatalog':catalog['features']}
fixture=json.loads((owned/'ComposedReaders.ast.json').read_text())
contract=next(n for n in fixture['ast']['nodes'] if n.get('nodeType')=='ContractDefinition')
expected={'memoryAlias':'normal','storageCopy':'normal','tupleOrder':'normal','executeFirst':'normal','falseControl':'panic','wrongTupleOrder':'panic','discardedFailure':'revert','discardedReadFailure':'revert',**{n:'reader refusal' for n in ['unsupportedCallTuple','unsupportedReference','unsupportedInlineArray','unsupportedDiscardRead']}}
result['composedControls']={'fixture':'tests/directruntime-20261104/shared-translator/ComposedReaders.ast.json','fixtureSha256':sha('tests/directruntime-20261104/shared-translator/ComposedReaders.ast.json'),'controls':'tests/directruntime-20261104/shared-translator/ComposedControls.lean','receipt':'tests/directruntime-20261104/shared-translator/evidence/adoption-8495/composed-compilation.json','gate':'tests/directruntime-20261104/shared-translator/artifacts/post-f77-gates/2.log','boundary':'Eight finite zero-parameter intrinsic samples/listings and four reader refusals. Not source preservation, proof closure, backend execution or full per-kind parity.','cases':[{'name':n['name'],'nodeId':n['id'],'src':n['src'],'expected':expected[n['name']]} for n in contract['nodes'] if n.get('name') in expected]}
assert len(result['composedControls']['cases'])==12
observed=json.loads((owned/'direct-result-observations.json').read_text())
assert len(observed)==12
verifier={row['function']:row for row in observed}
assert len(verifier)==12
for case in result['composedControls']['cases']:
 row=verifier[case['name']];assert row['sourceId']==case['nodeId'] and row['tag']=='diamond'
 case['trustedExecutableVerifier']={k:row[k] for k in ['status','reason','tag','sourceId','verification','reading']}
result['directCheckerObservations']={'path':'tests/directruntime-20261104/shared-translator/direct-result-observations.json','sha256':sha('tests/directruntime-20261104/shared-translator/direct-result-observations.json'),'controls':'tests/directruntime-20261104/shared-translator/DirectResultControls.lean','gate':'tests/directruntime-20261104/shared-translator/evidence/adoption-b86/direct-result-frozen.log','counts':{status:sum(row['status']==status for row in observed) for status in sorted({row['status'] for row in observed})},'boundary':'Actual public trusted executable checker outcomes under Lean control harness; no proof terms/declarations constructed. Pending is not refutation; proved is not Solidity preservation or native/WASM correctness.'}
result['modalityControls']=json.loads((owned/'modality-ledger.json').read_text())
result['modalityControls']['gate']='tests/directruntime-20261104/shared-translator/evidence/adoption-8bf/modality-frozen.log'
result['nativeControls']={'receipt':'tests/directruntime-20261104/shared-translator/evidence/adoption-3ad/native-controls.json','binarySha256':'1d327a56e1501d4bf02fe66bd04c4a4c1d85d328d7a550846a20ab76f05caa5d','fixtureComparisons':18,'failClosedRequests':2,'boundary':'Native functional parity and observed runtime access only;14origin-name candidates independently reviewed generic/empty. Exhaustive binary closure,WASM and source preservation remain pending.'}
# H90 scope/proof/backend facets are explicit reviewed inputs, not inferred
# semantic support from a successful decoder or printer.
ledger=owned/'h90-support-ledger.json'
if ledger.exists():
 facet=json.loads(ledger.read_text());result['h90NarrowLocalIncrement']=facet
 for row in result['constructs']:
  if row['nodeType'] in ['ElementaryTypeName','VariableDeclarationStatement','TupleExpression']:
   row['h90LocalFacet']=facet
(owned/'coverage-inventory.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'counts':result['counts'],'rawConstructorCounts':{k:len(v) for k,v in raw.items()},'localSharedImportModules':len(seen),'localIntrinsicImportModules':len(intrinsicClosure),'status':result['status']},sort_keys=True))
