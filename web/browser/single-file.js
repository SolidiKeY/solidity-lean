/* A closed asset namespace shared by the page and every nested worker. */
function installEmbeddedAssets(assets){
  const nativeFetch=globalThis.fetch.bind(globalThis),NativeWorker=globalThis.Worker,NativeXHR=globalThis.XMLHttpRequest;
  // file: workers have distinct opaque origins. Clone Blob handles into each
  // worker and create its URLs locally; a parent's blob:null URLs cannot be
  // imported or fetched from that worker.
  const urls=Object.create(null);
  function resolve(input){
    const value=String(input instanceof Request?input.url:input);
    if(value.startsWith('blob:'))return value;
    const path=new URL(value,'https://embedded.invalid/').pathname;
    if(!assets[path])throw new Error('Missing embedded asset: '+path);
    return urls[path]??=URL.createObjectURL(assets[path]);
  }
  globalThis.fetch=(input,init)=>{try{return nativeFetch(input instanceof Request?new Request(resolve(input),input):resolve(input),init);}catch(error){return Promise.reject(error);}};
  if(globalThis.importScripts){const nativeImport=globalThis.importScripts.bind(globalThis);globalThis.importScripts=(...urls)=>nativeImport(...urls.map(resolve));}
  globalThis.XMLHttpRequest=class extends NativeXHR{open(method,url,...args){super.open(method,resolve(url),...args);}};
  globalThis.Worker=class extends NativeWorker{
    constructor(url,options){
      if(options?.type==='module')throw new Error('Embedded workers must use the bundled classic format');
      const entry=new URL(String(url),'https://embedded.invalid/').pathname;
      if(!assets[entry])throw new Error('Missing embedded worker: '+entry);
      const source=`onmessage=async event=>{const queued=[];onmessage=event=>queued.push(event);try{const {assets,entry}=event.data;(${installEmbeddedAssets.toString()})(assets);const source=await assets[entry].text();onmessage=null;(0,eval)(source);for(const message of queued)dispatchEvent(message);}catch(error){setTimeout(()=>{throw error;},0);}};`;
      const bootstrap=URL.createObjectURL(new Blob([source],{type:'text/javascript'}));
      super(bootstrap,options);this.postMessage({assets,entry});URL.revokeObjectURL(bootstrap);
    }
  };
  return resolve;
}

/* The builder emits small data blocks followed immediately by capture().
 * Removing each node bounds DOM memory while IndexedDB stores Blobs on disk.
 * No service worker, HTTP resource, backend or installed SDK is required. */
function prepareSingleFile(build,expected){
  const entries=[],transientBlobs=new Set(),started=performance.now();let reuse=false,failure;
  let compilerStarted,compilerFailed;
  const compilerReady=new Promise((resolve,reject)=>{compilerStarted=resolve;compilerFailed=reject;});compilerReady.catch(()=>{});
  const database=new Promise((resolve,reject)=>{
    const request=indexedDB.open('solidity-lean-single-file-v1-'+build,1);
    request.onupgradeneeded=()=>request.result.createObjectStore('assets');
    request.onerror=()=>reject(request.error);
    request.onblocked=()=>reject(new Error('Close other IDE tabs to prepare offline storage'));
    request.onsuccess=()=>{
      const db=request.result,tx=db.transaction('assets','readwrite'),store=tx.objectStore('assets'),meta=store.get('@complete');
      meta.onsuccess=()=>{reuse=meta.result?.build===build&&meta.result?.count===expected;};
      tx.oncomplete=()=>resolve(db);tx.onabort=()=>reject(tx.error);
    };
  });
  // Keep a rejected storage promise handled even while the HTML is parsing.
  database.catch(error=>{failure=error;});
  let writes=database;
  function status(text){const node=document.querySelector('#editor .loading');if(node)node.textContent=text;}
  globalThis.singleFileIDE={build,expected,compilerReady,compilerStarted,runtimeFailure(error){singleFileIDE.invalidate();compilerFailed(error);},capture(){
    const node=document.currentScript.previousElementSibling;
    const key=node.dataset.asset,type=node.dataset.mime;
    entries.push(key);
    // All data is base64, so it cannot terminate a script element or execute.
    let text=reuse?'':node.textContent;node.remove();document.currentScript.remove();
    if(reuse||failure)return;
    // Decode, construct and commit only one asset at a time. In particular,
    // do not queue a full runtime's decoded ArrayBuffers during HTML parsing.
    writes=writes.then(db=>{
      let bytes;
      if(Uint8Array.fromBase64)bytes=Uint8Array.fromBase64(text);
      else{const binary=atob(text);bytes=Uint8Array.from(binary,c=>c.charCodeAt(0));}
      text='';const blob=new Blob([bytes],{type});bytes=undefined;transientBlobs.add(blob);
      return new Promise((resolve,reject)=>{
        const tx=db.transaction('assets','readwrite');tx.objectStore('assets').put(blob,key);
        tx.oncomplete=()=>{transientBlobs.delete(blob);resolve(db);};tx.onabort=()=>{transientBlobs.delete(blob);reject(new Error('Cannot store '+key+': '+tx.error?.message));};
      });
    });
    writes.catch(error=>{failure=error;});
    if(entries.length%50===0)status(`Preparing embedded offline tools… ${entries.length}/${expected}`);
  },async finish(){
    if(entries.length!==expected||new Set(entries).size!==expected)throw new Error('The HTML download is incomplete or contains duplicate assets');
    status('Opening embedded offline tools…');const db=await writes;
    if(failure)throw failure;
    const assets=Object.create(null);
    await new Promise((resolve,reject)=>{
      const tx=db.transaction('assets'),store=tx.objectStore('assets');
      for(const key of entries){const get=store.get(key);get.onsuccess=()=>{if(get.result instanceof Blob)assets[key]=get.result;};}
      tx.oncomplete=resolve;tx.onabort=()=>reject(tx.error);
    });
    if(Object.keys(assets).length!==expected)throw new Error('Offline storage is incomplete. Reload the HTML to prepare it again.');
    db.close();
    const assetURL=installEmbeddedAssets(assets);Object.assign(singleFileIDE,{assetURL,preparationMs:+(performance.now()-started).toFixed(1),reused:reuse});
    globalThis.MonacoEnvironment={getWorker:()=>new Worker('/monaco-worker.js')};
    for(const file of ['/monaco.css','/styles.css']){
      const style=document.createElement('style');style.textContent=await (await fetch(file)).text();document.head.append(style);
    }
    for(const file of ['/monaco.js','/browser-connection.js','/app.js'])await new Promise((resolve,reject)=>{
      const script=document.createElement('script');script.src=assetURL(file);script.onload=resolve;script.onerror=()=>reject(new Error('Cannot execute embedded asset: '+file));document.head.append(script);
    });
    await singleFileIDE.bootPromise;await compilerReady;
    await new Promise((resolve,reject)=>{const request=indexedDB.open('solidity-lean-single-file-v1-'+build);request.onerror=()=>reject(request.error);request.onsuccess=()=>{const db=request.result,tx=db.transaction('assets','readwrite');tx.objectStore('assets').put({build,count:expected},'@complete');tx.oncomplete=()=>{db.close();resolve();};tx.onabort=()=>{db.close();reject(tx.error);};};});
  },invalidate(){
    const request=indexedDB.open('solidity-lean-single-file-v1-'+build);
    request.onsuccess=()=>{const db=request.result;if(!db.objectStoreNames.contains('assets')){db.close();return;}const tx=db.transaction('assets','readwrite');tx.objectStore('assets').delete('@complete');tx.oncomplete=tx.onabort=()=>db.close();};
  },fail(error){singleFileIDE.invalidate();const node=document.querySelector('#editor');if(node)node.textContent='Unable to prepare the offline IDE: '+error.message+'. Check free disk space and allow browser storage, then reopen the HTML.';console.error(error);}};
}
