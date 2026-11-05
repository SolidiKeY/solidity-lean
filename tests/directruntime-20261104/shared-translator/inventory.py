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
for prefix,label in [('', 'existingFixture'),('fresh-', 'freshCompilerFixture')]:
 matrix=owned/(prefix+'construct-reader-matrix.json');casefile=owned/(prefix+'construct-reader-cases.json')
 if matrix.exists() and casefile.exists():
  observed={r['nodeType']:r for r in json.loads(matrix.read_text())}
  cases={r['nodeType']:r for r in json.loads(casefile.read_text())['cases']}
  for row in rows:
   kind=row['nodeType']
   if kind not in observed:continue
   item=observed[kind];case=cases[kind]
   row.setdefault('standaloneReaderObservations',{})[label]={
    'stage':'Whole-witness standalone tree decoding only; child refusals may dominate. No intrinsic, identity-resolution, semantic or backend support verdict.',
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
assert all(n=='Solidity.Frontend.ExecutableAst.Shared.Intrinsic' or not n.startswith('Solidity.Frontend.') for n in seen)
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
 'rawConstructors':raw,'localSharedImportClosure':seen,'localIntrinsicImportClosure':intrinsicClosure,
 'sourceProvenance':{p:sha(p) for p in [admissionPath,'Solidity/Frontend/SolcJson/Body.lean','Solidity/Frontend/SolcJson/Contract.lean',rawPath,'docs/solidity-features.json']},
 'featureCatalog':catalog['features']}
(owned/'coverage-inventory.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'counts':result['counts'],'rawConstructorCounts':{k:len(v) for k,v in raw.items()},'localSharedImportModules':len(seen),'localIntrinsicImportModules':len(intrinsicClosure),'status':result['status']},sort_keys=True))
