// PNG container integrity only. No inflate, pixel decoding, glyph or native-rendering claim.
'use strict';
const signature=Buffer.from([137,80,78,71,13,10,26,10]);
const table=Uint32Array.from({length:256},(_,value)=>{for(let i=0;i<8;i++)value=value&1?0xedb88320^(value>>>1):value>>>1;return value>>>0;});
function crc(bytes){let value=0xffffffff;for(const byte of bytes)value=table[(value^byte)&255]^(value>>>8);return(value^0xffffffff)>>>0;}
function invalid(message){throw Error('Visual phase has no PNG evidence: '+message);}
function assertPngContainer(bytes){
 if(!Buffer.isBuffer(bytes)||bytes.length<8||!bytes.subarray(0,8).equals(signature))invalid('signature');
 let offset=8,header=false,data=false,endedData=false,palette=false,dataBytes=0,width,height,color,depth;
 while(offset<bytes.length){
  if(bytes.length-offset<12)invalid('truncated chunk');
  const length=bytes.readUInt32BE(offset),type=bytes.toString('latin1',offset+4,offset+8);
  if(length>0x7fffffff||length>bytes.length-offset-12)invalid('chunk length');
  if(!/^[A-Za-z]{4}$/.test(type)||type[2]!==type[2].toUpperCase())invalid('chunk type');
  if(crc(bytes.subarray(offset+4,offset+8+length))!==bytes.readUInt32BE(offset+8+length))invalid('chunk CRC');
  if(!header&&type!=='IHDR')invalid('IHDR must be first');
  if(type==='IHDR'){
   if(header||length!==13)invalid('IHDR count/length');header=true;
   width=bytes.readUInt32BE(offset+8);height=bytes.readUInt32BE(offset+12);depth=bytes[offset+16];color=bytes[offset+17];
   if(!width||!height||width>0x7fffffff||height>0x7fffffff||!({0:[1,2,4,8,16],2:[8,16],3:[1,2,4,8],4:[8,16],6:[8,16]}[color]||[]).includes(depth)||bytes[offset+18]!==0||bytes[offset+19]!==0||![0,1].includes(bytes[offset+20]))invalid('IHDR fields');
  }else if(type==='PLTE'){
   if(palette||data||!length||length%3||length>768||color===3&&length/3>2**depth||[0,4].includes(color))invalid('PLTE');palette=true;
  }else if(type==='IDAT'){
   if(endedData||color===3&&!palette)invalid('IDAT order');data=true;dataBytes+=length;
  }else if(type==='IEND'){
   if(length||!data||!dataBytes||offset+12!==bytes.length)invalid('IEND/data/trailing bytes');return{width,height};
  }else if(type[0]===type[0].toUpperCase())invalid('unknown critical chunk');
  if(data&&type!=='IDAT')endedData=true;
  offset+=length+12;
 }
 invalid('missing IEND');
}
module.exports={assertPngContainer};
