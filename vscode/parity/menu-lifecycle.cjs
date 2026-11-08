// Native contribution observations. These checks certify recorded endpoints,
// not raster glyphs, hidden mutations, macOS or command execution.
'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),{createHash}=require('node:crypto');
const phases=['source','unrelated','untitled','tab','restored'];
function forbidden(events){return events.filter(e=>e.kind==='terminal.start'||e.kind==='clipboard.write'||e.kind==='command.start'&&/^(dafny|solidityLean)\.(build|buildCustomArgs|run|test|verify|showVerificationTrace|hideVerificationTrace|copyVerificationTrace)$/.test(e.data?.id));}
async function preparation(task,deadline,now=Date.now){const remaining=deadline-now();if(remaining<=0)throw Error('Original3s menu readiness exhausted');let timer;try{const value=await Promise.race([task(),new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error('Original3s menu readiness exhausted')),remaining);})]);if(now()>=deadline)throw Error('Late menu readiness response refused');return value;}finally{clearTimeout(timer);}}
function menuErrors(value,runId,target,workspace){
 const errors=[];if(value?.runId!==runId||value?.target!==target)errors.push('foreign menu run/target');
 if(JSON.stringify(value?.phases?.map(p=>p.phase))!==JSON.stringify(phases))errors.push('missing/reordered menu phases');
 for(const row of value?.phases||[]){const b=row.binding,m=row.capture?.capture?.contributionMenu,kind=row.phase==='tab'?'tab':'editor';
  if(!b||typeof b.uri!=='string'||!b.session||!Number.isSafeInteger(b.version)||!/^[a-f0-9]{64}$/.test(b.sourceHash||'')||JSON.stringify(row.after)!==JSON.stringify(b))errors.push('source/session changed');
  const visible=row.phase==='source'||row.phase==='restored'||row.phase==='untitled'&&target==='dafny';
  const sourcePhase=['source','tab','restored'].includes(row.phase),expectedLanguage=row.phase==='unrelated'?'plaintext':target==='local'?'solidity':'dafny';
  const expectedText=row.phase==='unrelated'?'Menu language isolation.\n':require('./workloads.cjs').workload(target,1);
  if(b?.sourceHash!==createHash('sha256').update(expectedText).digest('hex')||b?.language!==expectedLanguage||b?.scheme!==(row.phase==='untitled'?'untitled':'file')||b?.trusted!==true)errors.push('wrong source/language/scope');
  if(workspace&&row.phase!=='untitled'){const expectedUri=require('node:url').pathToFileURL(path.join(workspace,row.phase==='unrelated'?'unrelated.txt':'menus.'+(target==='local'?'sol':'dfy'))).href;if(b?.uri!==expectedUri)errors.push('wrong resource');}
  const label=target==='local'?'Solidity Lean':'Dafny',custom=target==='local'?'Build Compiler Artifact with Import Options':'Build with Custom Arguments';
  if(m?.kind!==kind||!!m?.before?.items?.some(i=>i.label===label)!==visible||visible&&!m?.before?.items?.some(i=>i.label.includes(custom))||row.capture?.runId!==runId||row.capture?.phase!=='menus-'+row.phase||row.capture?.metadataHash!==createHash('sha256').update(JSON.stringify({binding:b,target,kind,visible})).digest('hex'))errors.push('wrong menu/phase ownership');
  if(sourcePhase&&JSON.stringify(b)!==JSON.stringify(value?.phases?.[0]?.binding))errors.push('source lifetime changed');
  if(!m?.before?.items?.every(i=>typeof i.label==='string'&&Object.hasOwn(i,'ariaDisabled')&&[null,'true','false'].includes(i.ariaDisabled)&&Object.hasOwn(i,'className')&&i.withinViewport===true&&['left','top','right','bottom'].every(k=>Number.isFinite(i.bounds?.[k]))&&i.bounds.right>i.bounds.left&&i.bounds.bottom>i.bounds.top))errors.push('incomplete/clipped raw menu state');
  if(row.error||row.capture?.error||row.capture?.status!=='captured')errors.push('failed menu phase');
  if(!Array.isArray(row.events)||!Number.isSafeInteger(row.eventStart)||!Number.isSafeInteger(row.eventEnd)||row.eventStart<0||row.eventEnd<row.eventStart||!Array.isArray(value.events)||row.eventEnd>value.events.length||JSON.stringify(row.events)!==JSON.stringify(value.events.slice(row.eventStart,row.eventEnd))||forbidden(row.events||[]).length)errors.push('missing/forbidden raw events');
  if(!m||m.binding?.session!==b?.session||JSON.stringify(m.binding)!==JSON.stringify(b)||m.before?.activeUri!==b?.uri||JSON.stringify(m.before)!==JSON.stringify(m.after)||!m.before?.items?.length||m.submenuVisible!==visible||!row.capture?.capture?.captured||!row.capture.capture.screenshot)errors.push('missing/stale/menu capture');
 }
 if(!Array.isArray(value?.events)||!Array.isArray(value?.forbiddenActions)||value.forbiddenActions.length||forbidden(value?.events||[]).length||JSON.stringify(value.forbiddenActions)!==JSON.stringify(forbidden(value.events||[])))errors.push('command side effects or missing audit');
 return errors;
}
function trustErrors(value,runId,target,expected=['initial','grant','deny','lost','restore','restored']){
 const errors=[],t=value?.trust,steps=t?.steps;
 if(t?.mode!=='native-workspace-trust'||t.settings?.enabled!==true||t.settings?.startupPrompt!=='never'||t.settings?.enabledUserValue!==true||JSON.stringify(steps?.map(s=>s.phase))!==JSON.stringify(expected))return ['missing native trust launch/transitions'];
 let identity;
 for(const row of steps){
  const b=row.binding,{trusted,...source}=b||{},isMenu=['initial','lost','restored'].includes(row.phase),desired=['grant','restore','restored'].includes(row.phase);
  if(!b||trusted!==(isMenu?desired:!desired)||!b.session||!Number.isSafeInteger(b.version)||!/^file:/.test(b.uri||'')||b.sourceHash!==createHash('sha256').update(require('./workloads.cjs').workload(target,1)).digest('hex')||b.language!==(target==='local'?'solidity':'dafny')||b.scheme!=='file')errors.push('wrong trust/source binding');
  if(!identity)identity=source;else if(JSON.stringify(source)!==JSON.stringify(identity))errors.push('trust source lifetime changed');
  const expectedAfter={...b,trusted:isMenu?trusted:desired};if(JSON.stringify(row.after)!==JSON.stringify(expectedAfter))errors.push('unconfirmed public trust transition');
  const phase=isMenu?'menus-trust-'+row.phase:'menus-trust-control-'+row.phase,metadata=isMenu?{binding:b,target,kind:'editor',trustObservation:true}:{binding:b,desired};
  if(row.error||row.capture?.error||row.capture?.status!=='captured'||row.capture.runId!==runId||row.capture.phase!==phase||row.capture.metadataHash!==createHash('sha256').update(JSON.stringify(metadata)).digest('hex')||!row.capture.capture?.captured||!row.capture.capture.screenshot)errors.push('failed/foreign trust capture');
  if(!Array.isArray(row.events)||!Number.isSafeInteger(row.eventStart)||!Number.isSafeInteger(row.eventEnd)||row.eventStart<0||row.eventEnd<row.eventStart||row.eventEnd>value.events?.length||JSON.stringify(row.events)!==JSON.stringify(value.events?.slice(row.eventStart,row.eventEnd))||forbidden(row.events||[]).length)errors.push('missing/forbidden trust events');
  if(isMenu){const m=row.capture?.capture?.contributionMenu;
   if(JSON.stringify(m?.binding)!==JSON.stringify(b)||m?.before?.activeUri!==b.uri||JSON.stringify(m?.before)!==JSON.stringify(m?.after)||!m?.before?.items?.length||m.submenuVisible!==m.before.items.some(i=>i.label===(target==='local'?'Solidity Lean':'Dafny'))||m.kind!=='editor')errors.push('wrong trust menu endpoint');
   if(target==='local'&&m?.submenuVisible!==trusted)errors.push('local trust predicate violated');
   if(m?.submenuVisible&&!m.before.items.some(i=>i.label.includes(target==='local'?'Build Compiler Artifact with Import Options':'Build with Custom Arguments')))errors.push('trust submenu action missing');
   if(!m?.before?.items?.every(i=>typeof i.label==='string'&&Object.hasOwn(i,'ariaDisabled')&&[null,'true','false'].includes(i.ariaDisabled)&&typeof i.className==='string'&&i.withinViewport===true&&['left','top','right','bottom'].every(k=>Number.isFinite(i.bounds?.[k]))&&i.bounds.right>i.bounds.left&&i.bounds.bottom>i.bounds.top))errors.push('incomplete trust menu attributes');
  }else{const c=row.capture?.capture?.trustControl,label=desired?'Trust':"Don't Trust",opposite=desired?"Don't Trust":'Trust';
   if(c?.nativeMouse!==true||c.desired!==desired||JSON.stringify(c.binding)!==JSON.stringify(b)||!c.before?.visible||!c.after?.visible||JSON.stringify(c.beforeCaptured)!==JSON.stringify(c.before)||JSON.stringify(c.afterCaptured)!==JSON.stringify(c.after)||c.before.buttons.filter(x=>x.label===label&&x.disabled!=='true').length!==1||!c.after.buttons.some(x=>x.label===opposite))errors.push('missing real trust button transition');
  }
 }
 const lifetimes=[];
 for(const row of value.phases||[]){const m=row.capture?.capture?.contributionMenu;lifetimes.push(m?.before?.rendererLifetime,m?.after?.rendererLifetime);}
 for(const row of steps){const c=row.capture?.capture;if(['initial','lost','restored'].includes(row.phase)){lifetimes.push(c?.contributionMenu?.before?.rendererLifetime,c?.contributionMenu?.after?.rendererLifetime);}else{for(const k of ['before','after','beforeCaptured','afterCaptured'])lifetimes.push(c?.trustControl?.[k]?.rendererLifetime);}}
 const first=lifetimes[0];if(!first||!Number.isFinite(first.timeOrigin)||first.timeOrigin<=0||!String(first.url).startsWith('vscode-file:')||lifetimes.some(x=>JSON.stringify(x)!==JSON.stringify(first)))errors.push('renderer restarted or missing lifetime evidence');
 const main=value.phases?.[0]?.binding,{trusted:mainTrust,...mainSource}=main||{};if(main&&JSON.stringify(mainSource)!==JSON.stringify(identity))errors.push('legacy/trust source mismatch');
 return errors;
}
function validate(value,runId,target,workspace,trustMode){try{return [...menuErrors(value,runId,target,workspace),...(trustMode?trustErrors(value,runId,target):[])];}catch(error){return ['Malformed native menu observation: '+error.message];}}
async function run({vscode,config,events,sessionFor,requestPhase=require('./phase-capture.cjs').requestPhase}){
 if(config.menuTrust==='recovery')return runRecovery({vscode,config,events,sessionFor,requestPhase});
 const begin=events.length,target=config.target,language=target==='local'?'solidity':'dafny',source=require('./workloads.cjs').workload(target,1),file=path.join(config.workspace,'menus.'+(target==='local'?'sol':'dfy'));
 fs.writeFileSync(file,source);const doc=await vscode.workspace.openTextDocument(file),rows=[];
 const binding=d=>({uri:d.uri.toString(),version:d.version,sourceHash:createHash('sha256').update(d.getText()).digest('hex'),session:sessionFor(d),language:d.languageId,scheme:d.uri.scheme,trusted:vscode.workspace.isTrusted});
 const result={status:'partial',runId:config.runId,target,phases:rows,untrusted:{status:'missing',reason:'Existing pinned runner disables workspace trust UI; this launch cannot evidence an untrusted window.'},scope:'Actual Linux menu endpoint/AX/PNG observations only; no command, proof, raster/ABA or macOS equivalence.'};
 if(config.menuTrust)result.trust={mode:'native-workspace-trust',settings:{enabled:vscode.workspace.getConfiguration('security.workspace.trust').get('enabled'),startupPrompt:vscode.workspace.getConfiguration('security.workspace.trust').get('startupPrompt'),enabledUserValue:vscode.workspace.getConfiguration('security.workspace.trust').inspect('enabled')?.globalValue},steps:[]};
 const save=()=>fs.writeFileSync(path.join(config.dir,'menu-observations.json'),JSON.stringify(result,null,2));
 async function capture(phase,d,kind='editor'){
  await vscode.window.showTextDocument(d,{preview:false});await vscode.commands.executeCommand('workbench.action.focusActiveEditorGroup');
  const before=binding(d);assert.equal(vscode.window.activeTextEditor?.document,d);
  const start=events.length,row={phase,binding:before,eventStart:start-begin};rows.push(row);save();
  try{row.capture=await requestPhase(config.dir,config.runId,'menus-'+phase,{binding:before,target,kind,visible:phase==='source'||phase==='restored'||phase==='untitled'&&target==='dafny'},config.operationTimeoutMs);row.after=binding(d);assert.deepEqual(row.after,before);row.eventEnd=events.length-begin;row.events=events.slice(start);save();}
  catch(error){row.error=error.message;error.observation=result;throw error;}
  finally{row.eventEnd=events.length-begin;row.events=events.slice(start);save();}
 }
 async function trustStep(phase,desired){
  const isMenu=desired===undefined,before=binding(doc),start=events.length,row={phase,binding:before,eventStart:start-begin};result.trust.steps.push(row);save();
  try{
   if(isMenu){await vscode.window.showTextDocument(doc,{preview:false});await vscode.commands.executeCommand('workbench.action.focusActiveEditorGroup');}
   else await vscode.commands.executeCommand('workbench.trust.manage');
   const metadata=isMenu?{binding:before,target,kind:'editor',trustObservation:true}:{binding:before,desired};
   row.capture=await requestPhase(config.dir,config.runId,isMenu?'menus-trust-'+phase:'menus-trust-control-'+phase,metadata,config.operationTimeoutMs);
   if(!isMenu){const until=Date.now()+config.operationTimeoutMs;while(vscode.workspace.isTrusted!==desired&&Date.now()<until)await new Promise(r=>setTimeout(r,20));assert.equal(vscode.workspace.isTrusted,desired,'public workspace trust did not confirm');}
   row.after=binding(doc);assert.equal(doc.getText(),source);assert.equal(fs.readFileSync(file,'utf8'),source);
  }catch(error){row.error=error.message;error.observation=result;throw error;}
  finally{row.eventEnd=events.length-begin;row.events=events.slice(start);save();}
 }
 try{if(config.menuTrust){assert.equal(vscode.workspace.isTrusted,false,'native initial workspace must be untrusted');await trustStep('initial');await trustStep('grant',true);}
  await capture('source',doc);const textFile=path.join(config.workspace,'unrelated.txt');fs.writeFileSync(textFile,'Menu language isolation.\n');const unrelated=await vscode.workspace.openTextDocument(textFile);await capture('unrelated',unrelated);
  const untitled=await vscode.workspace.openTextDocument({language,content:source});await capture('untitled',untitled);await capture('tab',doc,'tab');await capture('restored',doc);
  if(config.menuTrust){await trustStep('deny',false);await trustStep('lost');await trustStep('restore',true);await trustStep('restored');result.untrusted={status:'partial',reason:'Native trust UI/API/menu endpoints only; full parity and reload/matrix coverage remain open.'};}
  assert.equal(doc.getText(),source);assert.equal(fs.readFileSync(file,'utf8'),source);result.events=events.slice(begin);result.forbiddenActions=forbidden(result.events);assert.deepEqual(validate(result,config.runId,target,config.workspace,config.menuTrust),[]);save();return result;
 }catch(error){error.observation=result;throw error;}
 finally{result.events=events.slice(begin);result.forbiddenActions=forbidden(result.events);save();}
}
// Explicit new-session companion. Never substitutes for the failed same-session run.
function recoveryPrefixErrors(observation,rawEvents,runId,target,workspace){try{if(rawEvents?.[0]?.kind!=='scenario.start'||rawEvents[0].data?.id!=='native-contribution-menus')return ['missing original scenario event boundary'];const value={...observation,events:rawEvents.slice(1),forbiddenActions:forbidden(rawEvents.slice(1))};const errors=validate(value,runId,target,workspace,false);if(JSON.stringify(value.trust?.steps?.map(r=>r.phase))!==JSON.stringify(['initial','grant','deny']))errors.push('wrong retained trust prefix');const deny=value.trust?.steps?.[2];if(deny?.capture!==undefined||deny?.after!==undefined||JSON.stringify(deny?.binding)!==JSON.stringify(value.phases?.[0]?.binding))errors.push('not an incomplete owned deny phase');const prefix={...value,trust:{...value.trust,steps:value.trust?.steps?.slice(0,2)}};return [...errors,...trustErrors(prefix,runId,target,['initial','grant'])];}catch(error){return ['malformed predecessor prefix: '+error.message];}}
function recoveryPredecessor(root,target){
 const dir=path.resolve(root,`${target}-w1-none-0`),receipt=name=>{const file=path.join(dir,name),bytes=fs.readFileSync(file);return{file,sha256:createHash('sha256').update(bytes).digest('hex'),value:name.endsWith('.jsonl')?bytes.toString().trim().split('\n').filter(Boolean).map(line=>JSON.parse(line)):JSON.parse(bytes)};};
 const reportFile=path.join(root,'report.json'),reportBytes=fs.readFileSync(reportFile),report=JSON.parse(reportBytes),run=report.runs?.find(r=>r.target===target&&path.resolve(r.artifacts)===dir),config=receipt('config.json'),observation=receipt('menu-observations.json'),hosts=receipt('host-lifecycle.jsonl'),resources=receipt('resources.json'),events=receipt('events.jsonl'),denyRequest=receipt('phases/menus-trust-control-deny/request.json');
 assert.equal(run?.status,'broken','recovery requires retained failed run');assert.equal(run.result,undefined);assert.equal(config.value.target,target);assert.equal(observation.value.runId,config.value.runId);assert.equal(observation.value.target,target);assert.equal(run.partialMenuEvidence?.status,'failed-partial');assert.equal(run.partialMenuEvidence?.sha256,observation.sha256);assert.deepEqual(run.partialMenuEvidence?.observation,observation.value);assert.deepEqual(recoveryPrefixErrors(observation.value,events.value,config.value.runId,target,config.value.workspace),[]);const deny=observation.value.trust.steps[2];assert.equal(denyRequest.value.runId,config.value.runId);assert.equal(denyRequest.value.phase,'menus-trust-control-deny');assert.deepEqual(denyRequest.value.metadata,{binding:deny.binding,desired:false});
 assert.deepEqual(observation.value.phases?.map(r=>r.phase),phases);assert.deepEqual(observation.value.trust?.steps?.map(r=>r.phase),['initial','grant','deny']);
 const binding=observation.value.phases[0].binding;assert.equal(binding.uri,require('node:url').pathToFileURL(path.join(config.value.workspace,'menus.'+(target==='local'?'sol':'dfy'))).href);
 const bytes=fs.readFileSync(require('node:url').fileURLToPath(binding.uri));assert.equal(createHash('sha256').update(bytes).digest('hex'),binding.sourceHash);assert.equal(bytes.toString(),require('./workloads.cjs').workload(target,1));
 for(const row of observation.value.phases){if(row.phase!=='unrelated'&&row.phase!=='untitled')assert.deepEqual(row.binding,binding);assert.equal(row.capture?.status,'captured');}
 const start=hosts.value.filter(r=>r.event==='host.start'),exit=hosts.value.filter(r=>r.event==='host.exit');assert.equal(start.length,1);assert.equal(exit.length,1);for(const row of [start[0],exit[0]]){assert.equal(row.runId,config.value.runId);assert.equal(row.target,target);assert.equal(row.hostSession,start[0].hostSession);assert.equal(row.pid,start[0].pid);assert.equal(row.birth,start[0].birth);}assert.ok(exit[0].wallTime>=start[0].wallTime);
 assert.deepEqual(resources.value.cleanup?.remaining,[]);assert.deepEqual(resources.value.cleanup?.identityRefusals,[]);
 return{status:'retained-failed-same-session',target,runId:config.value.runId,workspace:config.value.workspace,binding,host:start[0],exit:exit[0],receipts:[{file:reportFile,sha256:createHash('sha256').update(reportBytes).digest('hex')},...[config,observation,hosts,resources,events,denyRequest].map(({file,sha256})=>({file,sha256}))],failure:{status:run.status,error:run.error,exitCode:run.exitCode,exitSignal:run.exitSignal}};
}
function verifyRecoveryReceipts(prior){for(const receipt of prior.receipts){assert.equal(createHash('sha256').update(fs.readFileSync(receipt.file)).digest('hex'),receipt.sha256,'Recovery predecessor receipt mutated');}assert.equal(createHash('sha256').update(fs.readFileSync(require('node:url').fileURLToPath(prior.binding.uri))).digest('hex'),prior.binding.sourceHash,'Recovery source mutated');}
function recoveryErrors(value,runId,target,expected){try{
 const errors=[],prior=value?.predecessor,host=value?.host,steps=value?.steps;
 if(value?.mode!=='separate-new-session-recovery'||value.runId!==runId||value.target!==target||JSON.stringify(prior)!==JSON.stringify(expected)||prior?.status!=='retained-failed-same-session')return ['missing/foreign recovery predecessor'];
 if(value.settings?.enabled!==true||value.settings?.startupPrompt!=='never'||value.settings?.enabledUserValue!==true)errors.push('missing native recovery trust settings');
 if(!host?.hostSession||host.hostSession===prior.host?.hostSession||host.pid===prior.host?.pid&&host.birth===prior.host?.birth||host.runId!==runId||host.target!==target||!Number.isSafeInteger(host.pid)||host.pid<=0||host.trusted!==false||host.previousHostRecorded!==false||!Number.isFinite(host.wallTime)||host.wallTime<prior.exit.wallTime||process.platform==='linux'&&!/^\d+$/.test(host.birth||''))errors.push('missing/new-host identity');
 if(JSON.stringify(steps?.map(r=>r.phase))!==JSON.stringify(['initial','restore','restored']))return [...errors,'missing/reordered recovery phases'];
 const source=steps[0]?.binding;
 if(!source?.session||source.session===prior.binding.session)errors.push('document session not renewed');
 for(const row of steps){const {session,trusted,...old}=prior.binding||{}, {session:newSession,trusted:newTrust,...current}=row.binding||{};if(JSON.stringify(old)!==JSON.stringify(current)||newSession!==source?.session||newTrust!==(row.phase==='restored')||JSON.stringify(row.after)!==JSON.stringify({...row.binding,trusted:row.phase!=='initial'}))errors.push('wrong recovery source/version/session/trust');
  const menu=row.phase!=='restore',metadata=menu?{binding:row.binding,target,kind:'editor',trustObservation:true}:{binding:row.binding,desired:true},phase=menu?'menus-trust-recovery-'+row.phase:'menus-trust-control-recovery';
  if(row.error||row.capture?.error||row.capture?.status!=='captured'||row.capture.runId!==runId||row.capture.phase!==phase||row.capture.metadataHash!==createHash('sha256').update(JSON.stringify(metadata)).digest('hex')||!row.capture.capture?.captured||!row.capture.capture.screenshot)errors.push('failed/foreign recovery capture');
  const c=row.capture?.capture;if(menu){const m=c?.contributionMenu;if(JSON.stringify(m?.binding)!==JSON.stringify(row.binding)||m?.kind!=='editor'||m.before?.activeUri!==row.binding.uri||JSON.stringify(m.before)!==JSON.stringify(m.after)||!m.before?.items?.length||m.submenuVisible!==m.before.items.some(i=>i.label===(target==='local'?'Solidity Lean':'Dafny'))||target==='local'&&m.submenuVisible!==newTrust||m.submenuVisible&&!m.before.items.some(i=>i.label.includes(target==='local'?'Build Compiler Artifact with Import Options':'Build with Custom Arguments'))||!m.before?.items?.every(i=>typeof i.label==='string'&&Object.hasOwn(i,'ariaDisabled')&&[null,'true','false'].includes(i.ariaDisabled)&&typeof i.className==='string'&&i.withinViewport===true&&['left','top','right','bottom'].every(k=>Number.isFinite(i.bounds?.[k]))&&i.bounds.right>i.bounds.left&&i.bounds.bottom>i.bounds.top))errors.push('wrong recovery menu');}
  else{const t=c?.trustControl;if(t?.nativeMouse!==true||t.desired!==true||JSON.stringify(t.binding)!==JSON.stringify(row.binding)||!t.before?.visible||!t.after?.visible||JSON.stringify(t.before)!==JSON.stringify(t.beforeCaptured)||JSON.stringify(t.after)!==JSON.stringify(t.afterCaptured)||t.before.buttons.filter(b=>b.label==='Trust'&&b.disabled!=='true').length!==1||!t.after.buttons.some(b=>b.label==="Don't Trust"))errors.push('missing recovery native trust transition');}
  if(!Array.isArray(row.events)||!Number.isSafeInteger(row.eventStart)||!Number.isSafeInteger(row.eventEnd)||row.eventStart<0||row.eventEnd<row.eventStart||row.eventEnd>value.events?.length||JSON.stringify(row.events)!==JSON.stringify(value.events?.slice(row.eventStart,row.eventEnd))||forbidden(row.events).length)errors.push('missing/forbidden recovery events');
 }
 const lifetimes=steps.flatMap(row=>row.phase==='restore'?['before','after','beforeCaptured','afterCaptured'].map(k=>row.capture?.capture?.trustControl?.[k]?.rendererLifetime):['before','after'].map(k=>row.capture?.capture?.contributionMenu?.[k]?.rendererLifetime)),first=lifetimes[0];if(!first||!Number.isFinite(first.timeOrigin)||first.timeOrigin<=0||!String(first.url).startsWith('vscode-file:')||lifetimes.some(l=>JSON.stringify(l)!==JSON.stringify(first)))errors.push('recovery renderer restarted');
 if(!Array.isArray(value.events)||!Array.isArray(value.forbiddenActions)||value.forbiddenActions.length||forbidden(value.events||[]).length||JSON.stringify(value.forbiddenActions)!==JSON.stringify(forbidden(value.events||[])))errors.push('missing/forbidden recovery audit');return errors;
 }catch(error){return ['malformed recovery: '+error.message];}}
async function runRecovery({vscode,config,events,sessionFor,requestPhase}){
 const prior=config.menuRecovery,target=config.target,begin=events.length,doc=await vscode.workspace.openTextDocument(require('node:url').fileURLToPath(prior.binding.uri)),binding=()=>({uri:doc.uri.toString(),version:doc.version,sourceHash:createHash('sha256').update(doc.getText()).digest('hex'),session:sessionFor(doc),language:doc.languageId,scheme:doc.uri.scheme,trusted:vscode.workspace.isTrusted});
 const result={status:'partial',mode:'separate-new-session-recovery',runId:config.runId,target,predecessor:prior,host:config.menuRecoveryHost,settings:{enabled:vscode.workspace.getConfiguration('security.workspace.trust').get('enabled'),startupPrompt:vscode.workspace.getConfiguration('security.workspace.trust').get('startupPrompt'),enabledUserValue:vscode.workspace.getConfiguration('security.workspace.trust').inspect('enabled')?.globalValue},steps:[],scope:'New-host companion only; original same-session failure retained, not repaired or waived.'},save=()=>{result.events=events.slice(begin);result.forbiddenActions=forbidden(result.events);fs.writeFileSync(path.join(config.dir,'menu-observations.json'),JSON.stringify(result,null,2));};
 try{verifyRecoveryReceipts(prior);const {session, trusted,...before}=binding(),{session:oldSession,trusted:oldTrust,...expected}=prior.binding;assert.deepEqual(before,expected);assert.notEqual(session,oldSession);assert.equal(vscode.workspace.isTrusted,false,'recovery must start publicly untrusted');for(const phase of ['initial','restore','restored']){const before=binding(),start=events.length,row={phase,binding:before,eventStart:start-begin};result.steps.push(row);save();try{if(phase==='restore')await vscode.commands.executeCommand('workbench.trust.manage');else{await vscode.window.showTextDocument(doc,{preview:false});await vscode.commands.executeCommand('workbench.action.focusActiveEditorGroup');}
 const metadata=phase==='restore'?{binding:before,desired:true}:{binding:before,target,kind:'editor',trustObservation:true};row.capture=await requestPhase(config.dir,config.runId,phase==='restore'?'menus-trust-control-recovery':'menus-trust-recovery-'+phase,metadata,config.operationTimeoutMs);
 if(phase==='restore'){const deadline=Date.now()+config.operationTimeoutMs;await preparation(async()=>{while(!vscode.workspace.isTrusted){if(Date.now()>=deadline)throw Error('Recovery trust confirmation deadline');await new Promise(r=>setTimeout(r,20));}},deadline);}
 row.after=binding();assert.equal(fs.readFileSync(require('node:url').fileURLToPath(prior.binding.uri),'utf8'),doc.getText());
 }catch(error){row.error=error.message;throw error;}finally{row.eventEnd=events.length-begin;row.events=events.slice(start);save();}}
 assert.deepEqual(recoveryErrors(result,config.runId,target,prior),[]);return result;
 }catch(error){error.observation=result;throw error;}finally{save();}
}
// Failure transport only: never substitute this partial snapshot for a host result.
function partialEvidence(directory,runId,target){
 const file=path.join(directory,'menu-observations.json');let bytes;
 const diagnostics=[];let diagnosticError;
 try{const root=fs.realpathSync(directory),candidates=[path.join(directory,'host-lifecycle.jsonl')],phaseRoot=path.join(directory,'phases');if(fs.existsSync(phaseRoot))for(const name of fs.readdirSync(phaseRoot))if(name.startsWith('menus-'))candidates.push(path.join(phaseRoot,name,'cdp-timing.jsonl'));for(const candidate of candidates){if(!fs.existsSync(candidate))continue;const real=fs.realpathSync(candidate);if(!real.startsWith(root+path.sep))throw Error('Escaping partial diagnostic');const content=fs.readFileSync(real);diagnostics.push({file:candidate,bytes:content.length,sha256:createHash('sha256').update(content).digest('hex')});}}catch(error){diagnosticError=error.message;}

 try{bytes=fs.readFileSync(file);const observation=JSON.parse(bytes);if(observation.runId!==runId||observation.target!==target)throw Error('Foreign partial menu identity');return{status:'failed-partial',file,diagnostics,diagnosticError,sha256:createHash('sha256').update(bytes).digest('hex'),observation};}
 catch(error){return{status:'unavailable',file,diagnostics,diagnosticError,...(bytes?{sha256:createHash('sha256').update(bytes).digest('hex')}:{}),error:error.message};}
}
module.exports={phases,validate,run,preparation,trustErrors,partialEvidence,recoveryPredecessor,recoveryErrors,verifyRecoveryReceipts,recoveryPrefixErrors};
