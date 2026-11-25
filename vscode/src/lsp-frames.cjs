// Shared byte framing; the existing header budget includes its delimiter.
'use strict';
const {EventEmitter}=require('node:events');
const HEADER_LIMIT=8192;
// Preserve BOM handling by JSON.parse while refusing malformed source/URI bytes.
const utf8=new (require('node:util').TextDecoder)('utf-8',{fatal:true,ignoreBOM:true});

class LspFrames extends EventEmitter {
  constructor(limit=32*1024*1024){super();this.limit=limit;this.buffer=Buffer.alloc(0);}
  push(chunk){
    this.buffer=Buffer.concat([this.buffer,chunk]);
    while(this.buffer.length){
      const end=this.buffer.indexOf('\r\n\r\n');
      if(end<0){if(this.buffer.length>HEADER_LIMIT)throw new Error('Oversize LSP header');return;}
      if(end+4>HEADER_LIMIT)throw new Error('Oversize LSP header');
      const header=this.buffer.subarray(0,end);
      // Buffer's ASCII decoder clears bit7; inspect bytes before field parsing.
      if(header.some(byte=>byte>0x7f))throw new Error('Non-ASCII LSP header');
      const text=header.toString('ascii'),fields=[...text.matchAll(/^Content-Length:/gim)];
      const lengths=[...text.matchAll(/^Content-Length:[ \t]*(\d+)[ \t]*\r?$/gim)];
      if(fields.length!==1||lengths.length!==1)throw new Error('Invalid LSP Content-Length');
      const length=Number(lengths[0][1]);
      if(!Number.isSafeInteger(length)||length>this.limit)throw new Error('Oversize LSP body');
      if(this.buffer.length<end+4+length)return;
      const body=this.buffer.subarray(end+4,end+4+length);this.buffer=this.buffer.subarray(end+4+length);
      this.emit('message',JSON.parse(utf8.decode(body)));
    }
  }
  end(){if(this.buffer.length)throw new Error('Truncated LSP frame');}
}
module.exports={LspFrames};
