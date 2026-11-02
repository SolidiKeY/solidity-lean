import {initSync,BrotliDecStream} from 'brotli-dec-wasm/web';

export const prepareBrotli=module=>initSync({module});

// A whole-module Rust Vec leaves its peak allocation in Wasm linear memory.
// Bound decoder input/output buffers instead; only the returned library bytes
// and the bounded filesystem cache remain resident between imports.
export function inflateBrotli(compressed,size){
  const decoder=new BrotliDecStream(),parts=[];
  const output=size===undefined?null:new Uint8Array(size);
  let inputOffset=0,outputOffset=0;
  try{
    for(;;){
      const row=decoder.dec(compressed.subarray(inputOffset,inputOffset+65536),1048576);
      let code,consumed,part;
      try{code=row.code;consumed=row.input_offset;part=row.buf;}finally{row.free();}
      inputOffset+=consumed;
      if(output){if(outputOffset+part.length>size)throw new Error('Brotli asset exceeds its declared size');output.set(part,outputOffset);}else parts.push(part);
      outputOffset+=part.length;
      if(code===1){if(inputOffset!==compressed.length)throw new Error('Trailing Brotli asset data');break;}
      if(consumed===0&&part.length===0||code===2&&inputOffset===compressed.length)throw new Error('Truncated Brotli asset');
    }
  }finally{decoder.free();}
  if(output){if(outputOffset!==size)throw new Error('Invalid Brotli asset size');return output;}
  const result=new Uint8Array(outputOffset);let offset=0;
  for(const part of parts){result.set(part,offset);offset+=part.length;}return result;
}
