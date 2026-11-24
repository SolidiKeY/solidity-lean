// Shared byte framing; the existing header budget includes its delimiter.
'use strict';
const {EventEmitter}=require('node:events');
const HEADER_LIMIT=8192;

class LspFrames extends EventEmitter {
  constructor(limit=32*1024*1024){super();this.limit=limit;this.buffer=Buffer.alloc(0);}
  push(chunk){
    this.buffer=Buffer.concat([this.buffer,chunk]);
    while(this.buffer.length){
      const end=this.buffer.indexOf('\r\n\r\n');
      if(end<0){if(this.buffer.length>HEADER_LIMIT)throw new Error('Oversize LSP header');return;}
      if(end+4>HEADER_LIMIT)throw new Error('Oversize LSP header');
      const lengths=[...this.buffer.subarray(0,end).toString('ascii').matchAll(/^Content-Length:\s*(\d+)\s*$/gim)];
      if(lengths.length!==1)throw new Error('Invalid LSP Content-Length');
      const length=Number(lengths[0][1]);
      if(!Number.isSafeInteger(length)||length>this.limit)throw new Error('Oversize LSP body');
      if(this.buffer.length<end+4+length)return;
      const body=this.buffer.subarray(end+4,end+4+length);this.buffer=this.buffer.subarray(end+4+length);
      this.emit('message',JSON.parse(body.toString('utf8')));
    }
  }
  end(){if(this.buffer.length)throw new Error('Truncated LSP frame');}
}
module.exports={LspFrames};
