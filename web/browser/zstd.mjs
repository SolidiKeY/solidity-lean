import {ZSTDDecoder} from 'zstddec';

// The pinned decoder exposes the upstream ABI in _init. Use its embedded
// module, but check frame sizes and ZSTD_isError before copying output. Its
// convenience decode() does not check error codes or bound inferred sizes.
let runtime;
class AssetDecoder extends ZSTDDecoder{
  _init(result){runtime=result.instance.exports;super._init(result);}
}
const decoder=new AssetDecoder();
export const prepareZstd=async()=>{await decoder.init();return runtime;};
export function inflateZstd(compressed,size){
  if(!Number.isSafeInteger(size)||size<0||size>256*1024*1024)throw new Error('Invalid Zstandard asset size');
  if(!runtime)throw new Error('Zstandard decoder is not ready');
  const input=runtime.malloc(Math.max(1,compressed.length));let output;
  if(!input)throw new Error('Cannot allocate Zstandard input');
  try{
    new Uint8Array(runtime.memory.buffer).set(compressed,input);
    if(runtime.ZSTD_findDecompressedSize(input,compressed.length)!==BigInt(size))throw new Error('Invalid Zstandard frame size or stream');
    output=runtime.malloc(Math.max(1,size));if(!output)throw new Error('Cannot allocate Zstandard output');
    const actual=runtime.ZSTD_decompress(output,size,input,compressed.length);
    if(runtime.ZSTD_isError(actual)||actual!==size)throw new Error('Invalid Zstandard asset size or stream');
    return new Uint8Array(runtime.memory.buffer).slice(output,output+size);
  }finally{if(output)runtime.free(output);runtime.free(input);}
}
