/* Mechanical discovery supplements the existing feature inventory; it never assesses parity. */
'use strict';
const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const hash=x=>crypto.createHash('sha256').update(x).digest('hex');
function walk(dir){return fs.readdirSync(dir,{withFileTypes:true}).sort((a,b)=>a.name.localeCompare(b.name)).flatMap(e=>e.isDirectory()?walk(path.join(dir,e.name)):/\.(?:tsx?|[cm]?js)$/.test(e.name)?[path.join(dir,e.name)]:[]);}
function callsites(extension){
  const ts=require(path.join(extension,'node_modules/typescript'));
  const rows=[];
  for(const file of walk(path.join(extension,'src'))){
    const bytes=fs.readFileSync(file),text=bytes.toString(),rel=path.relative(extension,file).split(path.sep).join('/');
    const source=ts.createSourceFile(file,text,ts.ScriptTarget.Latest,true);
    if(source.parseDiagnostics.length)throw Error('Cannot parse '+file);
    function visit(n){
      if(ts.isCallExpression(n)){
        const e=n.expression;
        const name=ts.isPropertyAccessExpression(e)?e.name.text:ts.isElementAccessExpression(e)&&ts.isStringLiteral(e.argumentExpression)?e.argumentExpression.text:ts.isIdentifier(e)?e.text:'';
        if(/^(?:registerCommand|createTextEditorDecorationType|setDecorations|createStatusBarItem|createOutputChannel|show\w*Message|register\w*Provider|onNotification|onRequest|sendNotification|sendRequest|onDid(?:Open|Change|Save|Close)\w*)$/.test(name)){
          const start=n.getStart(source),pos=source.getLineAndCharacterOfPosition(start);
          rows.push({id:`callsite:${rel}:${pos.line+1}:${pos.character+1}:${name}`,kind:'mechanical-callsite',upstream:[{repository:'dafny-lang/ide-vscode',path:rel,sha256:hash(bytes)}],detail:{api:name,line:pos.line+1,column:pos.character+1,expression:n.getText(source)}});
        }
      }
      ts.forEachChild(n,visit);
    }
    visit(source);
  }
  return rows;
}
function contributions(extension){
  const bytes=fs.readFileSync(path.join(extension,'package.json')),manifest=JSON.parse(bytes),rows=[];
  const upstream=[{repository:'dafny-lang/ide-vscode',path:'package.json',sha256:hash(bytes)}];
  function add(pointer,value){rows.push({id:'contribution:'+pointer,kind:'mechanical-contribution',upstream,detail:{pointer,value}});}
  for(const [kind,value] of Object.entries(manifest.contributes)){
    if(kind==='configuration'){
      (Array.isArray(value)?value:[value]).forEach((section,i)=>{
        add(`${kind}/${i}`,section);
        for(const [key,setting]of Object.entries(section.properties||{}))add(`${kind}/${i}/properties/${key}`,setting);
      });
    }else if(Array.isArray(value))value.forEach((v,i)=>add(`${kind}/${i}`,v));
    else if(value&&typeof value==='object')for(const [key,items]of Object.entries(value)){
      if(Array.isArray(items))items.forEach((v,i)=>add(`${kind}/${key}/${i}`,v));else add(`${kind}/${key}`,items);
    }else add(kind,value);
  }
  return rows;
}
function traceRows(file,repoRelative){
  const records=fs.readFileSync(file,'utf8').trim().split('\n').map(JSON.parse);
  const rows=[],methods=new Set(),caps=new Map(),finalized=new Set();
  const fail=reason=>{throw Error('Incomplete/corrupt lifecycle trace: '+reason);};
  if(records.some(r=>r.error||r.message?.error))fail('protocol/framing error');
  const find=(from,predicate)=>{const i=records.findIndex((r,i)=>i>from&&predicate(r));if(i<0)fail('missing ordered event after '+from);return i;};
  const client=method=>r=>r.direction==='client'&&r.message?.method===method;
  const request=find(-1,r=>client('initialize')(r)&&r.message.id!==undefined);
  const init=find(request,r=>r.direction==='server'&&r.message?.id===records[request].message.id&&r.message.result?.capabilities);
  function flatten(value,pointer){
    if(value&&typeof value==='object'&&Object.keys(value).length)for(const [k,v]of Object.entries(value))flatten(v,pointer+'/'+k);
    else caps.set(pointer,value);
  }
  flatten(records[init].message.result.capabilities,'');
  const opened=find(init,r=>client('textDocument/didOpen')(r)&&typeof r.message.params?.textDocument?.text==='string');
  const doc=records[opened].message.params.textDocument;
  if(!doc.uri||!Number.isInteger(doc.version))fail('open URI/version');
  let previous=opened,version=doc.version,text=doc.text;
  const phases=[];
  for(let phase=0;phase<4;phase++){
    const start=previous,currentVersion=version,status=phase===2?4:5;
    const feedback=find(start,r=>r.direction==='server'&&r.message?.method==='dafny/textDocument/symbolStatus'&&
      r.message.params?.uri===doc.uri&&r.message.params.version===currentVersion&&
      r.message.params.namedVerifiables?.length>0&&r.message.params.namedVerifiables.every(s=>status===5?s.status===5:[4,5].includes(s.status))&&r.message.params.namedVerifiables.some(s=>s.status===status));
    if(status===4){
      const diagnostic=find(start,r=>r.direction==='server'&&r.message?.method==='textDocument/publishDiagnostics'&&
        r.message.params?.uri===doc.uri&&r.message.params.version===currentVersion&&r.message.params.diagnostics?.some(d=>d.severity===1&&d.source==='Verifier'));
      previous=Math.max(feedback,diagnostic);
    }else previous=feedback;
    phases.push({version:currentVersion,text,status});
    if(phase<3){
      const changed=find(previous,r=>client('textDocument/didChange')(r)&&r.message.params?.textDocument?.uri===doc.uri);
      const p=records[changed].message.params;
      if(!Number.isInteger(p.textDocument.version)||p.textDocument.version<=version||p.contentChanges?.length!==1||p.contentChanges[0].range||typeof p.contentChanges[0].text!=='string')fail('versioned full-buffer phase change required');
      version=p.textDocument.version;text=p.contentChanges[0].text;
      if(text===phases[phase].text)fail('phase did not edit source');previous=changed;
    }
  }
  const saved=find(previous,r=>client('textDocument/didSave')(r)&&r.message.params?.textDocument?.uri===doc.uri);
  const closed=find(saved,r=>client('textDocument/didClose')(r)&&r.message.params?.textDocument?.uri===doc.uri);
  const shutdown=find(closed,r=>client('shutdown')(r)&&r.message.id!==undefined);
  const acknowledged=find(shutdown,r=>r.direction==='server'&&r.message?.id===records[shutdown].message.id&&Object.hasOwn(r.message,'result'));
  const exited=find(acknowledged,client('exit'));
  for(let i=0;i<records.length;i++){
    const r=records[i],m=r.message;
    if(r.framingFinalized&&i>exited&&['client','server'].includes(r.direction))finalized.add(r.direction);
    if(m?.method?.startsWith('dafny/'))methods.add(m.method);
    if(r.direction==='server'&&m?.method==='client/registerCapability')for(const registration of m.params?.registrations||[]){
      if(!registration.method)fail('malformed dynamic capability');
      rows.push({id:`dynamic-capability:${registration.method}:${rows.length}`,kind:'live-dynamic-capability',detail:registration});
    }
  }
  if(finalized.size!==2)fail('missing client/server finalization');
  rows.push(...[...caps].map(([pointer,value])=>({id:'capability:'+pointer,kind:'live-capability',detail:{pointer,value}})),
    ...[...methods].sort().map(method=>({id:'live-method:'+method,kind:'live-custom-method',detail:{method}})));
  return rows.map(r=>({...r,upstream:[],trace:repoRelative,traceSha256:hash(fs.readFileSync(file))}));
}
const requiredScenarios=[
  ...['open','edit','save','configuration-change','server-crash'].map(x=>'lifecycle:'+x),
  ...['open','first-feedback','verified','proof-broken','proof-fixed'].flatMap(phase=>['gutter','squiggles','status-bar','hover','code-lenses','colours','icons'].map(aspect=>'visual:'+phase+':'+aspect)),
  ...['rapid-edits','cancellation','stale-diagnostics','restarts','multi-file','configuration-changes','parallel-verification','benchmark-median','benchmark-p95','benchmark-cold','benchmark-warm','benchmark-worker-scaling'].map(x=>'scenario:'+x),
  ...["lookup-migration-incomplete-edit", "lookup-migration-foreign-dependency", "lookup-utf16-multichange", "lookup-conservative-invalidation", "lookup-proof-edit-isolation", "lookup-close-reopen-config", "lookup-cancel-stale-generation", "lookup-lexical-context-invalidation", "lookup-metadata-overhead"].map(x=>'scenario:'+x),
  ...["lookup-structural-provenance", "lookup-moved-block-binding", "lookup-overload-expression-provenance", "lookup-declaration-header-invalidation", "lookup-receiver-shadow-provenance", "lookup-same-depth-brace-identity", "lookup-nested-metadata-overhead"].map(x=>'scenario:'+x),
  ...["startup-missing-runtime", "startup-unexecutable-runtime", "startup-missing-backend", "startup-supported-runtime-contract", "startup-unknown-runtime-version", "startup-unknown-server-version", "startup-initialize-failure-recovery", "startup-runtime-probe-timeout", "startup-probe-cancellation", "startup-trust-boundary", "startup-config-folder-isolation", "startup-ownerless-error-retirement", "startup-close-reopen-action", "startup-shared-client-ownership-epoch", "startup-stale-workspace-symbols", "startup-version-status-lifetime", "startup-cold-warm-benchmark"].map(x=>'scenario:'+x),
  ...["version-native-producer-order", "version-early-known", "version-missing-fallback", "version-malformed-notification", "version-late-duplicate", "version-transport-failure", "version-disposal-cleanup", "version-close-reopen-scoped-recovery", "version-cross-folder-isolation", "version-request-readiness-cancellation", "version-workspace-readiness-cancellation", "version-restart-barrier-cancellation", "version-early-metadata-bounds", "notification-registration-disposal", "notification-close-handler-release", "version-matrix-failure-cleanup"].map(x=>'scenario:'+x),
  ...["status-summary-mixed-outcomes", "status-summary-empty-and-skipped", "status-summary-direct-check-boundary", "status-summary-entry-audit-qualification", "status-summary-native-status-validation", "status-summary-running-queued-names", "status-summary-failure-names-counts", "status-native-outcome-metadata", "status-document-job-progress-scope", "status-source-hash-guard", "status-synchronization-reopen-guard", "status-invalid-open-no-mutation", "status-picker-document-ownership", "status-picker-epoch-and-active-aba", "status-picker-current-progress-delivery", "status-issue-draft-version-privacy", "status-contextual-local-output", "status-native-compiler-failure-recovery", "status-stale-aborted-analysis", "status-pinned-source-comparison", "status-native-background-scope-disposal"].map(x=>'scenario:'+x),
  ...["testing-automatic-terminal", "testing-automatic-queued-running", "testing-automatic-document-job-boundary", "testing-automatic-classification", "testing-automatic-entry-audit", "testing-automatic-companion-idempotence", "testing-automatic-manual-overlap", "testing-automatic-multi-file", "testing-automatic-source-guard", "testing-automatic-session-reopen", "testing-automatic-edit-invalidation", "testing-automatic-cancel-retry", "testing-automatic-config-restart", "testing-automatic-crash", "testing-automatic-visibility-stop", "testing-automatic-disposal-end-once", "testing-automatic-compiler-recovery", "testing-automatic-report-errors", "testing-automatic-malformed-status", "testing-automatic-duration", "testing-automatic-pinned-source-comparison"].map(x=>'scenario:'+x),
  ...["testing-hierarchy-current-symbols", "testing-hierarchy-fallback-contracts", "testing-hierarchy-overloaded-identities", "testing-hierarchy-inherited-context", "testing-hierarchy-no-parent-proof-results", "testing-hierarchy-parent-exclusions", "testing-hierarchy-parent-deduplication", "testing-hierarchy-recursive-removal", "testing-hierarchy-historical-rejection", "testing-hierarchy-unmatched-symbols", "testing-hierarchy-missing-locations", "testing-hierarchy-stale-async-source", "testing-hierarchy-reopen-session", "testing-hierarchy-config-restart", "testing-hierarchy-visibility-disposal", "testing-hierarchy-automatic-manual-overlap", "testing-hierarchy-documented-collection-api", "testing-hierarchy-native-compiler-provenance", "testing-hierarchy-pinned-comparison", "contributions-truthful-context-menu", "contributions-trusted-resource-scope", "contributions-cli-contract-gap"].map(x=>'scenario:'+x),
  ...["retention-worker-close-confirmation", "retention-cancel-replacement-capacity", "retention-directory-lifetime", "retention-reset-admission-barrier", "retention-invalid-reset-atomic", "retention-reset-unique-paths", "retention-queued-original-deadline", "retention-server-crash-frozen-worker", "retention-worker-crash-descendant", "retention-owned-process-registration", "retention-owned-process-refusal", "retention-build-admission-ack", "retention-build-deadline-refusal", "retention-manager-per-key-barrier", "retention-manager-failure-poison", "retention-manager-bounded-failure", "retention-client-shutdown-deadline", "retention-native-ten-edits", "retention-native-thread-readback", "retention-native-scoped-recovery", "retention-native-close-reopen", "retention-native-process-quiescence", "retention-zombie-readback-boundary", "retention-raw-stdio-group-cleanup", "rpc-cancel-write-settlement", "rpc-timeout-write-settlement", "retention-legacy-owner-capability", "retention-native-compiler-latency", "retention-resource-guard"].map(x=>'scenario:'+x),
  ...["concurrency-cached-analysis-preflight", "concurrency-dependency-preflight", "concurrency-shared-analysis-caller-cancel", "concurrency-shared-verification-callers", "concurrency-workspace-multiroot-snapshot", "concurrency-workspace-caller-cancel", "concurrency-workspace-outer-reopen", "concurrency-workspace-outer-dependency", "concurrency-diagnostic-session-provenance", "concurrency-late-compiler-save-storm", "concurrency-native-three-document-open", "concurrency-native-final-current-error", "concurrency-native-query-edit", "concurrency-native-cold-warm-boundaries", "concurrency-upstream-skipped-resolution"].map(x=>'scenario:'+x),
  ...["large-file-native-1000-declarations", "large-file-native-100-accepted-prepends", "large-file-native-symbol-range-shift", "large-file-native-stale-query-ownership", "large-file-native-current-error-fix", "large-file-native-cancel-quiescence", "large-file-native-disposal", "large-file-cold-warm-scheduling-boundaries", "large-file-invalid-attempt-retention", "managed-request-source-delivery", "managed-request-cancel-delivery", "managed-request-retirement-source", "managed-workspace-cancel-delivery", "large-file-evidence-mutant-rejection"].map(x=>'scenario:'+x),
  ...["hover-exact-service-assertion", "hover-markdown-declaration-signatures", "hover-compiler-documentation", "hover-lexical-shadowing-and-scope-exit", "hover-unknown-invocation-null", "hover-incremental-utf16-ranges", "hover-foreign-dependency-update", "hover-parse-recovery-difference", "hover-type-recovery-difference", "hover-nested-header-braces", "hover-provider-markup", "hover-provider-plaintext-escaping", "hover-native-reopen-session", "hover-native-config-restart-isolation", "hover-native-cancel-late-delivery", "hover-native-owned-disposal"].map(x=>'scenario:'+x),
  ...["concrete-build-compiler-artifact", "concrete-run-typed-model", "concrete-test-exact-cases", "concrete-command-resource-lifecycle"].map(x=>'scenario:'+x),
  ...['native-build-keybinding','native-build-dirty-crlf-utf16'].map(x=>'scenario:'+x),
  // Independently exercised recovery scenarios remain separate judged obligations.
  ...["compiler-secondary-locations", "compiler-foreign-related-locations", "diagnostics-migrate-incremental", "diagnostics-selective-reverification", "diagnostics-dependency-invalidation", "hover-shared-analysis-cancellation", "hover-before-verification-completes", "testing-overlapping-includes", "testing-parent-exclusions", "testing-native-run-cancellation", "testing-profile-cancellation", "testing-command-cancellation", "testing-disposal", "testing-multi-file-identity", "testing-stale-selection", "testing-overlapping-runs", "reference-diagnostic-migration", "diagnostic-close-reopen", "hover-close-reopen", "hover-config-retirement", "diagnostics-foreign-range-isolation", "testing-visibility-toggle", "diagnostics-invalid-old-location"].map(x=>'scenario:'+x)
];
function staticRows(extension){return [...contributions(extension),...callsites(extension),...requiredScenarios.map(id=>({id,kind:id.split(':')[0],upstream:[],detail:{scope:id}}))];}
module.exports={hash,callsites,contributions,traceRows,staticRows,requiredScenarios};
