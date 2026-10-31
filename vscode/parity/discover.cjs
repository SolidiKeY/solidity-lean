#!/usr/bin/env node
'use strict';
const {readFileSync,writeFileSync,readdirSync,existsSync} = require('node:fs');
const {join,resolve,relative} = require('node:path');
const {createHash} = require('node:crypto');
const {spawnSync} = require('node:child_process');
const root=resolve(__dirname,'../..');
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
function files(directory,extensions) {
  return readdirSync(directory,{withFileTypes:true}).flatMap(e=>e.isDirectory()?files(join(directory,e.name),extensions):extensions.some(ext=>e.name.endsWith(ext))?[join(directory,e.name)]:[]).sort();
}
function scan(extension,server) {
  const features=[],sources=[];
  const source=(base,file,repository)=>{
    const bytes=readFileSync(join(base,file));const evidence={repository,path:file,sha256:digest(bytes)};
    if(!sources.some(s=>s.repository===repository&&s.path===file))sources.push(evidence);
    return {...evidence};
  };
  const add=(id,kind,evidence,detail)=>features.push({id,kind,upstream:evidence,detail});
  const manifest=JSON.parse(readFileSync(join(extension,'package.json'),'utf8'));
  const manifestEvidence=source(extension,'package.json','dafny-lang/ide-vscode');
  for(const [kind,rows] of Object.entries(manifest.contributes)) {
    if(kind==='configuration') {
      for(const section of Array.isArray(rows)?rows:[rows])for(const [key,value]of Object.entries(section.properties||{}))add('setting:'+key,'setting',manifestEvidence,value);
    } else if(Array.isArray(rows)) rows.forEach((value,i)=>add(kind+':'+(value.command||value.id||value.language||i),kind,manifestEvidence,value));
    else if(rows&&typeof rows==='object')for(const [key,value]of Object.entries(rows))add(kind+':'+key,kind,manifestEvidence,value);
  }
  for(const file of files(join(extension,'src'),['.ts']).filter(f=>!f.includes('/test/'))) {
    const text=readFileSync(file,'utf8');const rel=relative(extension,file);
    const methods=[...text.matchAll(/(?:onNotification|sendRequest)(?:<[^>]+>)?\(\s*['"]([^'"]+)['"]/g)];
    for(const match of methods)add('protocol:'+match[1],'custom-protocol',source(extension,rel,'dafny-lang/ide-vscode'),{method:match[1]});
  }
  const handlers='Source/DafnyLanguageServer/Handlers/LanguageServerExtensions.cs';
  for(const match of readFileSync(join(server,handlers),'utf8').matchAll(/\.WithHandler<([^>]+)>/g))
    add('handler:'+match[1],'language-server-handler',source(server,handlers,'dafny-lang/dafny'),{handler:match[1]});
  // Include custom methods discovered on the server even when the client does
  // not use them, and retain legacy client-only notification names.
  const requests='Source/DafnyLanguageServer/DafnyRequestNames.cs';
  for(const match of readFileSync(join(server,requests),'utf8').matchAll(/const string (\w+)\s*=\s*"([^"]+)"/g))
    add('protocol:'+match[2],'custom-protocol',source(server,requests,'dafny-lang/dafny'),{method:match[2]});
  const ui={
    'gutter-status':'src/ui/verificationGutterStatusView.ts','ghost-highlighting':'src/ui/ghostDiagnosticsView.ts',
    'verification-tests':'src/ui/verificationSymbolStatusView.ts','compilation-status':'src/ui/compilationStatusView.ts',
    'verification-trace':'src/ui/verificationTraceView.ts','related-errors':'src/ui/relatedErrorView.ts',
    'status-bar-actions':'src/ui/statusBarActionView.ts','version-status':'src/ui/dafnyVersionView.ts',
    'server-installation':'src/language/dafnyInstallation.ts','launch-and-concurrency':'src/language/dafnyLanguageClient.ts'};
  for(const [id,file]of Object.entries(ui))add('behavior:'+id,'editor-behavior',source(extension,file,'dafny-lang/ide-vscode'),{});
  const commands='src/commands.ts';
  for(const match of readFileSync(join(extension,commands),'utf8').matchAll(/['"](dafny\.[^'"]+)['"]/g))
    if(!uniqueCommand(features,match[1]))add('commands:'+match[1],'commands',source(extension,commands,'dafny-lang/ide-vscode'),{command:match[1],discovery:'source constant, including unmanifested runtime commands'});
  add('behavior:language-editing-configuration','editor-behavior',source(extension,'dafny-language-configuration.json','dafny-lang/ide-vscode'),{scope:'comments, brackets, auto-closing and surrounding pairs'});
  // Families independently rediscovered from upstream tests after the first
  // inventory pass. Test presence is discovery evidence, not local test success.
  const families={
    'project-discovery-and-ownership':['ProjectFiles/ProjectFilesTest.cs','ProjectFiles/CompetingProjectFilesTest.cs'],
    'project-includes-and-solver-options':['ProjectFiles/MultipleFilesProjectTest.cs','ProjectFiles/SolverOptionsTest.cs','Synchronization/IncludeFileTest.cs'],
    'parse-resolution-verification-diagnostics':['Various/CompilationStatusNotificationTest.cs'],
    'member-and-attribute-completion':['Completion/DotCompletionTest.cs','Completion/AtCompletionTest.cs'],
    'assertion-batch-hover-cost':['Lookup/HoverVerificationTest.cs'],
    'cache-invalidation-and-migration':['Synchronization/CachingTest.cs'],
    'scheduling-fairness-and-contention':['Synchronization/VerificationOrderTest.cs','Synchronization/VerificationOrderTest2.cs'],
    'concurrent-interactions-and-large-projects':['Various/ConcurrentInteractionsTest.cs','Performance/LargeFilesTest.cs'],
    'thread-retention':['Performance/ThreadUsageTest.cs']};
  for(const [id,paths]of Object.entries(families))for(const path of paths) {
    const file='Source/DafnyLanguageServer.Test/'+path;
    add('behavior:'+id,'independent-audit-family',source(server,file,'dafny-lang/dafny'),{scope:id});
  }
  const extra={
    'testing-exclusions-and-state-transitions':'src/ui/verificationSymbolStatusView.ts',
    'expanded-related-diagnostics':'src/ui/relatedErrorView.ts',
    'startup-and-version-compatibility':'src/startupCheck.ts'};
  for(const [id,file]of Object.entries(extra))add('behavior:'+id,'independent-audit-family',source(extension,file,'dafny-lang/ide-vscode'),{});
  for(const [id,file]of Object.entries({
    'plugin-handlers-and-code-actions':'Source/DafnyLanguageServer/Handlers/LanguageServerExtensions.cs',
    'assertion-splitting-and-task-scheduling':'Source/DafnyCore/Pipeline/Compilation.cs',
    'frontend-vc-generation-serialization':'Source/DafnyLanguageServer/Language/DafnyProgramVerifier.cs'}))
    add('behavior:'+id,'independent-audit-family',source(server,file,'dafny-lang/dafny'),{});
  const doc='docs/DafnyRef/VSCodeIDE.md';
  const evidence=source(server,doc,'dafny-lang/dafny');
  for(const match of readFileSync(join(server,doc),'utf8').matchAll(/^##+\s+(.+)$/gm))add('documentation:'+match[1],'documentation',evidence,{heading:match[1]});
  const unique=new Map();
  for(const f of features) {
    if(unique.has(f.id))unique.get(f.id).upstream.push(f.upstream);
    else unique.set(f.id,{...f,upstream:[f.upstream]});
  }
  const commit=path=>spawnSync('git',['-C',path,'rev-parse','HEAD'],{encoding:'utf8'}).stdout.trim();
  const discovered=[...unique.values()];
  return {schemaVersion:1,upstream:{extension:{repository:'dafny-lang/ide-vscode',commit:commit(extension),version:manifest.version},server:{repository:'dafny-lang/dafny',commit:commit(server)}},
    discovery:{featureCount:discovered.length,featureIdsSha256:digest(JSON.stringify(discovered.map(f=>f.id).sort()))},sources,features:discovered};
}
function uniqueCommand(features,command){return features.some(f=>f.id==='commands:'+command);}
function assess(feature) {
  const id=feature.id;
  const missing=/commands:dafny\.(build|run|test|showVerificationTrace|hideVerificationTrace|copyVerificationTrace|restartServer|openStatusBarMenu)|handler:Dafny(Definition|References|Rename|Completion|SignatureHelp|Formatting|DocumentSymbol|WorkspaceSymbol|CodeAction)Handler|behavior:(gutter-status|ghost-highlighting|verification-trace|status-bar-actions|version-status|server-installation|language-editing-configuration)|grammars:|languages:|submenus:|menus:|keybindings:/.test(id);
  const local=['vscode/src/extension.cjs','vscode/src/backend.cjs','vscode/src/model.cjs'];
  let status=missing?'missing':'unexamined',scenarios=[],reason=missing?'No corresponding provider, contribution or UI component in the local verification extension.':'Source discovery only; exact behavior has not been tested.';
  const map=[[/Hover/,'hover'],[/TextDocumentHandler/,'rapid-edits-stale-results'],[/verification-tests|symbolStatus/,'initial-verification'],
    [/counterExample/,'counterexamples'],[/cancelVerifySymbol/,'cancellation'],[/verifySymbol/,'initial-verification'],[/launch-and-concurrency|verificationVirtualCores/,'concurrent-files-and-requests'],
    [/automaticVerification/,'configuration-and-save'],[/verificationCachingPolicy/,'incremental-verification'],[/compilation-status|compilation\/status/,'initial-verification']];
  for(const [pattern,scenario]of map)if(pattern.test(id)) {status='partial';scenarios.push(scenario);reason='Related local behavior exists, but protocol, granularity or configuration differs. Runtime evidence is required.';}
  if(feature.kind==='custom-protocol') {status='missing';reason='Local extension uses CLI JSON and does not implement this Dafny LSP method. Related editor observations are listed separately.';}
  return {...feature,assessment:{status,reason,localSource:local,scenarioIds:scenarios,testEvidence:[]}};
}
function validate(inventory) {
  const errors=[];const ids=new Set();
  if(inventory.schemaVersion!==1)errors.push('unsupported schema');
  if(inventory.discovery?.featureCount!==inventory.features?.length||inventory.discovery?.featureIdsSha256!==digest(JSON.stringify((inventory.features||[]).map(f=>f.id).sort())))errors.push('discovered feature set changed');
  for(const component of ['extension','server'])if(!/^[0-9a-f]{40}$/.test(inventory.upstream?.[component]?.commit||''))errors.push('invalid source pin '+component);
  for(const feature of inventory.features||[]) {
    if(ids.has(feature.id))errors.push('duplicate '+feature.id);ids.add(feature.id);
    const a=feature.assessment;
    if(!['complete','partial','missing','broken','unexamined'].includes(a?.status))errors.push('invalid status '+feature.id);
    if(!feature.upstream?.length)errors.push('missing upstream evidence '+feature.id);
    for(const evidence of feature.upstream||[])if(!/^[a-f0-9]{64}$/.test(evidence.sha256)||!inventory.sources?.some(s=>JSON.stringify(s)===JSON.stringify(evidence)))errors.push('unregistered upstream evidence '+feature.id);
    if(a?.status==='complete') {
      if(!a.testEvidence?.length)errors.push('unsupported completeness claim '+feature.id);
      for(const t of a.testEvidence||[]) {
        let actual;try{const path=resolve(root,t.artifact);if(!path.startsWith(root+'/'))throw new Error('escaping evidence');actual=JSON.parse(readFileSync(path,'utf8'));}catch{}
        if(t.status!=='passed'||!t.assertion||!actual?.checks?.includes(t.assertion)||actual.target!==t.target||!actual.runId)errors.push('unsupported completeness claim '+feature.id);
      }
      if(!['local','dafny'].every(target=>a.testEvidence?.some(t=>t.target===target)))errors.push('completeness needs both targets '+feature.id);
    }
    for(const file of a?.localSource||[])if(!resolve(root,file).startsWith(root+'/')||!existsSync(join(root,file)))errors.push('missing or escaping local source '+file);
  }
  if(!inventory.features?.length)errors.push('empty inventory');
  return errors;
}
function main(args=process.argv.slice(2)) {
  const path=join(root,'docs/dafny-editor-features.json');
  if(args[0]==='--check') {
    const inventory=JSON.parse(readFileSync(path,'utf8')),errors=validate(inventory);
    if(errors.length)throw new Error(errors.join('\n'));process.stdout.write(`Validated ${inventory.features.length} editor features; no untested completeness claims.\n`);return;
  }
  const extension=args[args.indexOf('--extension')+1],server=args[args.indexOf('--server')+1];
  if(!args.includes('--extension')||!args.includes('--server'))throw new Error('Use --check or --extension DIR --server DIR [--write]');
  const inventory=scan(resolve(extension),resolve(server));inventory.features=inventory.features.map(assess);
  if(args.includes('--check-source')) {
    const expected=JSON.parse(readFileSync(path,'utf8'));
    if(JSON.stringify(expected.upstream)!==JSON.stringify(inventory.upstream)||JSON.stringify(expected.sources)!==JSON.stringify(inventory.sources)||
      JSON.stringify(expected.features.map(f=>f.id))!==JSON.stringify(inventory.features.map(f=>f.id)))throw new Error('Pinned source or discovered feature set drifted; inspect and reconcile the inventory');
    process.stdout.write('Pinned editor source and feature discovery match.\n');
  }
  else if(args.includes('--write'))writeFileSync(path,JSON.stringify(inventory,null,2)+'\n');
  else process.stdout.write(JSON.stringify(inventory,null,2)+'\n');
}
module.exports={scan,assess,validate,files};
if(require.main===module)try{main();}catch(e){process.stderr.write(e.stack+'\n');process.exitCode=1;}
