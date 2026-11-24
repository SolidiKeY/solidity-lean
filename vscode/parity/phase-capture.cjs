// Fresh-launch, acknowledged phase screenshots. A callback success without image bytes is insufficient.
'use strict';
const fs=require('node:fs'),path=require('node:path'),{randomUUID,createHash}=require('node:crypto');
const phases=['menus-trust-recovery-initial','menus-trust-control-recovery','menus-trust-recovery-restored','menus-trust-initial','menus-trust-lost','menus-trust-restored','menus-trust-control-grant','menus-trust-control-deny','menus-trust-control-restore',...['source','unrelated','untitled','tab','restored'].map(p=>'menus-'+p),...['visible','hidden','restored'].map(p=>'testing-symbols-'+p),...['open','f7','f8','config','edited','switched','reopened'].map(p=>'trace-unavailable-'+p),...['open','first-feedback','verified','proof-broken','proof-fixed'].flatMap(phase=>[phase,phase+'-hover']),'trace-shown','trace-copied','trace-hidden','trace-lifecycle-shown','trace-edited','trace-switched','trace-returned','trace-custom-color','trace-reopened-observed','trace-reopened-shown','trace-reopened-hidden','trace-hide-inflight','trace-cleanup','trace-close-inflight','trace-beforeclose','trace-visibility-shown','trace-tab-reopened','trace-light','trace-light-hidden','trace-light-explicit','trace-light-explicit-hidden','proof-help-menu-guide','proof-help-guide','proof-help-menu-index','proof-help-index','proof-help-hover','output-channel','compiler-output-default','compiler-output-relative','compiler-output-absolute','dafny-output-default','dafny-output-relative','dafny-output-absolute','dafny-command-build','dafny-command-run','dafny-command-test','diagnostics-problems-duplicate','diagnostics-problems-shifted','diagnostics-problems-fixed'];
function terminal(state){return !!state&&(['complete','error','cancelled'].includes(state.state)||state.namedVerifiables?.length>0&&state.namedVerifiables.every(s=>s.status>=4));}
function outcome(state){
  if(state?.namedVerifiables?.length){const statuses=state.namedVerifiables.map(s=>s.status);return statuses.every(s=>s===5)?'proved':statuses.every(s=>[4,5].includes(s))&&statuses.includes(4)?'failed':null;}
  if(state?.state!=='complete'||!state.functions?.length)return null;
  const statuses=state.functions.map(f=>f.status);
  return statuses.every(s=>s==='proved')?'proved':statuses.every(s=>['proved','pending','refuted'].includes(s))&&statuses.some(s=>['pending','refuted'].includes(s))?'failed':null;
}
function phaseObserved(phase,before,after){
  if(phase==='open')return !before&&!after;
  if(phase==='first-feedback')return !!before&&!!after&&!terminal(before)&&!terminal(after);
  const expected=phase==='proof-broken'?'failed':'proved';
  return outcome(before)===expected&&outcome(after)===expected&&JSON.stringify(before.functions||before.namedVerifiables)===JSON.stringify(after.functions||after.namedVerifiables);
}
const {assertPngContainer}=require('./png-container.cjs');
function captureAcknowledged(value){return value?.captured===true&&value.screenshot===true&&value.error===undefined;}
function imageEntry(file){try{return fs.lstatSync(file,{bigint:true});}catch(error){if(error.code==='ENOENT')return null;throw error;}}
function regularImage(stat){return !!stat&&stat.isFile()&&stat.nlink===1n;}
function sameImage(a,b){return regularImage(a)&&regularImage(b)&&['dev','ino','size','mtimeNs','ctimeNs'].every(key=>a[key]===b[key]);}
function readImage(file){
  const before=imageEntry(file);if(!regularImage(before))throw Error('Visual phase screenshot is not a single-link regular file');
  const fd=fs.openSync(file,fs.constants.O_RDONLY|(fs.constants.O_NOFOLLOW||0)|(fs.constants.O_NONBLOCK||0));
  try{
    const opened=fs.fstatSync(fd,{bigint:true});if(!sameImage(before,opened))throw Error('Visual phase screenshot changed before read');
    const bytes=fs.readFileSync(fd),after=fs.fstatSync(fd,{bigint:true});
    if(!sameImage(opened,after)||!sameImage(after,imageEntry(file))||after.size!==BigInt(bytes.length))throw Error('Visual phase screenshot changed during read');
    return bytes;
  }finally{fs.closeSync(fd);}
}
function paths(directory,phase){if(!phases.includes(phase))throw Error('Unknown visual phase '+phase);const dir=path.join(directory,'phases',phase);return{dir,request:path.join(dir,'request.json'),reply:path.join(dir,'reply.json')};}
function json(file,value){const tmp=file+'.tmp';fs.writeFileSync(tmp,JSON.stringify(value,null,2)+'\n');fs.renameSync(tmp,file);}
async function requestPhase(directory,runId,phase,metadata,timeoutMs){
  const deadline=Date.now()+timeoutMs;
  const p=paths(directory,phase);fs.mkdirSync(p.dir,{recursive:true});const request={runId,phase,requestId:randomUUID(),requested:Date.now(),metadata};const metadataHash=createHash('sha256').update(JSON.stringify(metadata)).digest('hex');
  // Preserve each attempt; atomically claim this one-request phase channel.
  const attempt=path.join(p.dir,'request-attempt-'+request.requestId+'.json');json(attempt,request);fs.linkSync(attempt,p.request);
  while(Date.now()<deadline){
    if(fs.existsSync(p.reply)){
      const reply=JSON.parse(fs.readFileSync(p.reply));
      if(reply.runId===runId&&reply.requestId===request.requestId&&reply.phase===phase){
        if(reply.metadataHash!==metadataHash)throw Error('Visual phase source metadata mismatch');
        if(reply.error!==undefined||reply.status!=='captured')throw Error('Visual phase '+phase+' failed: '+reply.error);
        if(!captureAcknowledged(reply.capture))throw Error('Visual phase '+phase+' failed: Invalid renderer acknowledgement');
        const bytes=readImage(path.join(p.dir,'screenshot.png'));
        assertPngContainer(bytes);
        if(reply.imageBytes!==bytes.length||reply.imageSha256!==createHash('sha256').update(bytes).digest('hex'))throw Error('Visual phase image byte binding mismatch');
        if(Date.now()>=deadline)break;
        return reply;
      }
    }
    await new Promise(r=>setTimeout(r,20));
  }
  throw Object.assign(Error('Timed out capturing visual phase '+phase),{code:'TIMEOUT'});
}
async function servePhases(directory,runId,capture,seen){
  for(const phase of phases){
    const p=paths(directory,phase);if(!fs.existsSync(p.request))continue;
    const request=JSON.parse(fs.readFileSync(p.request));
    if(request.runId!==runId||request.phase!==phase||typeof request.requestId!=='string'||seen.has(request.requestId))continue;
    seen.add(request.requestId);const reply={runId,phase,requestId:request.requestId,status:'failed',requested:request.requested,metadataHash:createHash('sha256').update(JSON.stringify(request.metadata??null)).digest('hex')};
    try{if(imageEntry(path.join(p.dir,'screenshot.png')))throw Error('Existing phase screenshot must be preserved; choose a fresh capture directory');
        reply.capture=await capture(p.dir,request);reply.status=captureAcknowledged(reply.capture)?'captured':'failed';
        if(reply.status!=='captured')reply.error=typeof reply.capture?.error==='string'&&reply.capture.error?reply.capture.error:'Renderer did not capture a screenshot';
        else{const bytes=readImage(path.join(p.dir,'screenshot.png'));assertPngContainer(bytes);reply.imageBytes=bytes.length;reply.imageSha256=createHash('sha256').update(bytes).digest('hex');}}
    catch(e){reply.status='failed';reply.error=e.message;}
    reply.finished=Date.now();json(p.reply,reply);
  }
}
module.exports={atomicJson:json,phases,paths,requestPhase,servePhases,phaseObserved};
