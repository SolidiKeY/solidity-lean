'use strict';
const {spawn}=require('node:child_process');
const {pathToFileURL}=require('node:url');
const {join}=require('node:path');
const {writeFileSync,mkdirSync}=require('node:fs');
const {RpcPeer}=require('./rpc.cjs');
const {terminateTree}=require('./backend.cjs');

/** One persistent Lean document retains its import environment between versions.
 * The parent owns and terminates this worker's entire process tree on cancellation. */
class LeanSession {
  constructor(root,directory){this.root=root;this.directory=directory;this.version=0;this.messages=[];}
  async start(timeoutMs){
    if(this.initialized&&this.peer&&!this.peer.closed)return;
    this.initialized=false;this.version=0;this.messages=[];
    if(this.child)terminateTree(this.child);
    const {lakeCommand}=await import(pathToFileURL(join(this.root,'scripts/lake-command.mjs')).href);
    this.child=spawn(lakeCommand(),['serve','--','--tstack=131072','-Dserver.reportDelayMs=0'],{cwd:this.root,stdio:['pipe','pipe','pipe'],windowsHide:true});
    this.stderr='';this.child.stderr.on('data',chunk=>{this.stderr=(this.stderr+chunk).slice(-12000);});
    const peer=this.peer=new RpcPeer(this.child.stdout,this.child.stdin);
    this.child.on('error',error=>peer.close(error));
    this.child.on('exit',code=>peer.close(new Error(`Lean server exited ${code}: ${this.stderr}`)));
    this.peer.onNotification('textDocument/publishDiagnostics',params=>{if(params.uri===this.uri&&(params.version===undefined||params.version===this.version))this.messages=params.diagnostics;});
    this.peer.onRequest('workspace/configuration',params=>params.items.map(()=>null));
    this.peer.onRequest('client/registerCapability',()=>null);
    try{await this.peer.request('initialize',{processId:process.pid,rootUri:pathToFileURL(this.root).href,
      capabilities:{textDocument:{publishDiagnostics:{versionSupport:true}}}},{timeoutMs});
    this.peer.notify('initialized',{});this.initialized=true;
    }catch(error){this.peer.close(error);terminateTree(this.child);throw error;}
    mkdirSync(this.directory,{recursive:true});this.file=join(this.directory,'Worker.lean');this.uri=pathToFileURL(this.file).href;
  }
  async check(text,timeoutMs){
    await this.start(timeoutMs);this.messages=[];
    writeFileSync(this.file,text);const version=++this.version;
    if(version===1)this.peer.notify('textDocument/didOpen',{textDocument:{uri:this.uri,languageId:'lean4',version,text}});
    else this.peer.notify('textDocument/didChange',{textDocument:{uri:this.uri,version},contentChanges:[{text}]});
    const result=await this.peer.request('textDocument/waitForDiagnostics',{uri:this.uri,version},{timeoutMs});
    // Lean returns the authoritative diagnostics as well as publishing them.
    return Array.isArray(result?.diagnostics)?result.diagnostics:this.messages;
  }
  dispose(){if(this.child){terminateTree(this.child);this.peer?.close();this.child=null;}}
}
module.exports={LeanSession};
