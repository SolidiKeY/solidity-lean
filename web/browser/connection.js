'use strict';
// WebSocket-shaped event adapter for the existing UI. No network connection is
// constructed: requests and source buffers move only through postMessage.
class BrowserConnection {
  constructor(){this.readyState=0;this.worker=new Worker('/browser-worker.js');this.worker.onmessage=event=>{if(event.data.method==='workerReady'){this.readyState=1;this.onopen?.();return;}this.onmessage?.({data:JSON.stringify(event.data)});};this.worker.onerror=event=>{this.worker.terminate();this.readyState=3;try{this.onerror?.(event);}finally{this.onclose?.();}};}
  send(message){if(this.readyState!==1)throw new Error('Browser compiler is not ready');this.worker.postMessage(JSON.parse(message));}
  close(){this.worker.terminate();this.readyState=3;this.onclose?.();}
}
globalThis.BrowserConnection=BrowserConnection;
