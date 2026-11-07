'use strict';
const {spawn,execFile}=require('node:child_process');
const {promisify}=require('node:util');
const {performance}=require('node:perf_hooks');
const execute=promisify(execFile);
const {inspectNative}=require('./native-plugin.cjs');
const {pathToFileURL}=require('node:url');
const {join}=require('node:path');
const {writeFileSync,mkdirSync}=require('node:fs');
const {RpcPeer}=require('./rpc.cjs');
const {terminateTree}=require('./backend.cjs');
const {trackChild,waitForClose}=require('./child-lifetime.cjs');

/** One persistent Lean document retains its import environment between versions.
 * The parent owns and terminates this worker's entire process tree on cancellation. */
class LeanSession {
  constructor(root,directory){this.root=root;this.directory=directory;this.version=0;this.messages=[];}
  async start(timeoutMs=60000){
    if(this.retiring)throw new Error('Lean session is retiring');
    if(this.initialized&&this.peer&&!this.peer.closed)return;
    const deadline=performance.now()+timeoutMs;
    const remaining=()=>{const ms=Math.floor(deadline-performance.now());if(ms<=0)throw new Error('Lean startup timed out');return ms;};
    this.initialized=false;this.version=0;this.messages=[];
    if(this.child)terminateTree(this.child);
    const {lakeCommand}=await import(pathToFileURL(join(this.root,'scripts/lake-command.mjs')).href);
    if(this.retiring)throw new Error('Lean session is retiring');
    const lake=lakeCommand(),selection=this.nativeDisabled?{reason:this.nativeDisabled}:inspectNative(this.root);
    this.native={active:false,reason:selection.reason||'runtime-mismatch'};
    let plugin=[];
    if(selection.path){
      try{
        const probe=execute(lake,['env','lean','--githash'],{cwd:this.root,timeout:Math.min(remaining(),10000),windowsHide:true});
        const child=probe.child;this.startupProbe={child,closed:trackChild(child)};
        let stdout;try{({stdout}=await probe);}finally{if(this.startupProbe?.child===child)this.startupProbe=null;}
        if(stdout.trim()===selection.leanCommit){
          plugin=['--plugin='+selection.path];
          this.native={active:true,sha256:selection.sha256,optimization:selection.optimization,probe:selection.probe};
        }
      }catch{this.native={active:false,reason:'runtime-unavailable'};}
    }
    remaining();if(this.retiring)throw new Error('Lean session is retiring');
    this.child=spawn(lake,['serve','--','--tstack=131072','-Dserver.reportDelayMs=0',...plugin],{cwd:this.root,stdio:['pipe','pipe','pipe'],windowsHide:true});
    const child=this.child;this.closed=trackChild(child);
    this.stderr='';this.child.stderr.on('data',chunk=>{this.stderr=(this.stderr+chunk).slice(-12000);});
    const peer=this.peer=new RpcPeer(this.child.stdout,this.child.stdin);
    this.child.on('error',error=>peer.close(error));
    this.child.on('exit',code=>peer.close(new Error(`Lean server exited ${code}: ${this.stderr}`)));
    this.peer.onNotification('textDocument/publishDiagnostics',params=>{if(params.uri===this.uri&&(params.version===undefined||params.version===this.version))this.messages=params.diagnostics;});
    this.peer.onRequest('workspace/configuration',params=>params.items.map(()=>null));
    this.peer.onRequest('client/registerCapability',()=>null);
    try{await this.peer.request('initialize',{processId:process.pid,rootUri:pathToFileURL(this.root).href,
      capabilities:{textDocument:{publishDiagnostics:{versionSupport:true}}}},{timeoutMs:remaining()});
    if(this.retiring)throw new Error('Lean session is retiring');
    this.peer.notify('initialized',{});this.initialized=true;
    }catch(error){peer.close(error);terminateTree(child);throw error;}
    mkdirSync(this.directory,{recursive:true});this.file=join(this.directory,'Worker.lean');this.uri=pathToFileURL(this.file).href;
  }
  async check(text,timeoutMs=60000){
    const deadline=performance.now()+timeoutMs;
    const remaining=()=>{const ms=Math.floor(deadline-performance.now());if(ms<=0)throw new Error('Lean verification timed out');return ms;};
    const check=async()=>{
      await this.start(remaining());if(this.retiring)throw new Error('Lean session is retiring');this.messages=[];
      writeFileSync(this.file,text);const version=++this.version;
      if(version===1)this.peer.notify('textDocument/didOpen',{textDocument:{uri:this.uri,languageId:'lean4',version,text}});
      else this.peer.notify('textDocument/didChange',{textDocument:{uri:this.uri,version},contentChanges:[{text}]});
      const result=await this.peer.request('textDocument/waitForDiagnostics',{uri:this.uri,version},{timeoutMs:remaining()});
      return Array.isArray(result?.diagnostics)?result.diagnostics:this.messages;
    };
    try{return await check();}
    catch(error){
      if(!this.native?.active||error.code===-32800||!this.peer?.closed)throw error;
      this.nativeDisabled='native-process-failed';this.initialized=false;
      this.dispose();return check();
    }
  }
  /** Terminal cooperative retirement: Lean's shutdown reaps its file workers.
   * The original force-dispose path remains available for immediate cancellation. */
  finishDispose({deadline=Date.now()+1000}={}){
    if(this.retirement)return this.retirement;this.retiring=true;
    const child=this.child,peer=this.peer,closed=this.closed,probe=this.startupProbe;this.child=null;this.initialized=false;
    this.retiringChild=child;
    this.retirement=(async()=>{
      try{
        if(probe){terminateTree(probe.child);await waitForClose(probe.child,{closed:probe.closed,deadline});}
        if(!child)return;
        if(peer&&!peer.closed){
          const remaining=deadline-Date.now();if(remaining<=0)throw Error('Lean retirement deadline exhausted');
          await peer.request('shutdown',null,{timeoutMs:remaining});peer.notify('exit',null);
        }else terminateTree(child);
        await waitForClose(child,{closed,deadline});
      }catch(error){if(child)terminateTree(child);throw error;}
      finally{peer?.close();this.retiringChild=null;}
    })();this.retirement.catch(()=>{});return this.retirement;
  }
  dispose(){if(this.startupProbe)terminateTree(this.startupProbe.child);const child=this.child||this.retiringChild;if(child){terminateTree(child);this.peer?.close();this.child=null;}}

}
module.exports={LeanSession};
