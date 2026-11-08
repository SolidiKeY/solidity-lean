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
function trustErrors(value,runId,target){
 const errors=[],t=value?.trust,steps=t?.steps,expected=['initial','grant','deny','lost','restore','restored'];
 if(t?.mode!=='native-workspace-trust'||t.settings?.enabled!==true||t.settings?.startupPrompt!=='never'||t.settings?.enabledUserValue!==true||JSON.stringify(steps?.map(s=>s.phase))!==JSON.stringify(expected))return ['missing native trust launch/transitions'];
 let identity;
 for(const row of steps){
  const b=row.binding,{trusted,...source}=b||{},isMenu=['initial','lost','restored'].includes(row.phase),desired=['grant','restore','restored'].includes(row.phase);
  if(!b||trusted!==(isMenu?desired:!desired)||!b.session||!Number.isSafeInteger(b.version)||!/^file:/.test(b.uri||'')||b.sourceHash!==createHash('sha256').update(require('./workloads.cjs').workload(target,1)).digest('hex')||b.language!==(target==='local'?'solidity':'dafny')||b.scheme!=='file')errors.push('wrong trust/source binding');
  if(!identity)identity=source;else if(JSON.stringify(source)!==JSON.stringify(identity))errors.push('trust source lifetime changed');
  const expectedAfter={...b,trusted:isMenu?trusted:desired};if(JSON.stringify(row.after)!==JSON.stringify(expectedAfter))errors.push('unconfirmed public trust transition');
  const phase=isMenu?'menus-trust-'+row.phase:'menus-trust-control-'+row.phase,metadata=isMenu?{binding:b,target,kind:'editor',trustObservation:true}:{binding:b,desired};
  if(row.error||row.capture?.status!=='captured'||row.capture.runId!==runId||row.capture.phase!==phase||row.capture.metadataHash!==createHash('sha256').update(JSON.stringify(metadata)).digest('hex')||!row.capture.capture?.captured||!row.capture.capture.screenshot)errors.push('failed/foreign trust capture');
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
// Failure transport only: never substitute this partial snapshot for a host result.
function partialEvidence(directory,runId,target){
 const file=path.join(directory,'menu-observations.json');let bytes;
 const diagnostics=[];let diagnosticError;
 try{const root=fs.realpathSync(directory),candidates=[path.join(directory,'host-lifecycle.jsonl')],phaseRoot=path.join(directory,'phases');if(fs.existsSync(phaseRoot))for(const name of fs.readdirSync(phaseRoot))if(name.startsWith('menus-'))candidates.push(path.join(phaseRoot,name,'cdp-timing.jsonl'));for(const candidate of candidates){if(!fs.existsSync(candidate))continue;const real=fs.realpathSync(candidate);if(!real.startsWith(root+path.sep))throw Error('Escaping partial diagnostic');const content=fs.readFileSync(real);diagnostics.push({file:candidate,bytes:content.length,sha256:createHash('sha256').update(content).digest('hex')});}}catch(error){diagnosticError=error.message;}

 try{bytes=fs.readFileSync(file);const observation=JSON.parse(bytes);if(observation.runId!==runId||observation.target!==target)throw Error('Foreign partial menu identity');return{status:'failed-partial',file,diagnostics,diagnosticError,sha256:createHash('sha256').update(bytes).digest('hex'),observation};}
 catch(error){return{status:'unavailable',file,diagnostics,diagnosticError,...(bytes?{sha256:createHash('sha256').update(bytes).digest('hex')}:{}),error:error.message};}
}
module.exports={phases,validate,run,preparation,trustErrors,partialEvidence};
