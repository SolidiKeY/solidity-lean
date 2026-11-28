/** Seeded, bounded instruction IR. Labels are assembled after shrinking. */
export const binary = ['ADD','MUL','SUB','DIV','SDIV','MOD','SMOD','LT','GT','SLT','SGT','EQ','AND','OR','XOR','SHL','SHR','SAR'];
export const unary = ['ISZERO','NOT'];
export const opcodes = {STOP:0,ADD:1,MUL:2,SUB:3,DIV:4,SDIV:5,MOD:6,SMOD:7,SIGNEXTEND:11,LT:16,GT:17,SLT:18,SGT:19,EQ:20,ISZERO:21,AND:22,OR:23,XOR:24,NOT:25,BYTE:26,SHL:27,SHR:28,SAR:29,CALLDATALOAD:53,CALLDATASIZE:54,CALLDATACOPY:55,POP:80,MLOAD:81,MSTORE:82,JUMP:86,JUMPI:87,JUMPDEST:91,RETURN:243,REVERT:253};
const W=1n<<256n;
export function random(seed) {
  if (!Number.isSafeInteger(seed)||seed<0||seed>0xffffffff) throw Error('seed must be uint32');
  let s=BigInt(seed);
  return () => {s=(1664525n*s+1013904223n)&0xffffffffn;let z=s; z=((z^(z>>16n))*0x45d9f3bn)&0xffffffffn; z=((z^(z>>16n))*0x45d9f3bn)&0xffffffffn; return Number(z^(z>>16n));};
}
export function generate(seed, count) {
  if (!Number.isSafeInteger(count)||count<1||count>1000000) throw Error('invalid count');
  const next=random(seed), pick=a=>a[next()%a.length];
  const word=()=> {if(next()%3===0)return pick([0n,1n,31n,32n,255n,256n,W-1n,1n<<255n]);let n=0n;for(let i=0;i<8;i++)n=n*2n**32n+BigInt(next());return n;};
  return Array.from({length:count},(_,index)=> {
    const instructions=[], push=n=>instructions.push({op:'PUSH',value:String(n)});
    for(let j=0,n=1+next()%8;j<n;j++) {
      push(word()); push(word()); instructions.push({op:pick(binary)});
      if(next()%2)instructions.push({op:pick(unary)});
      push(BigInt(next()%4*32));instructions.push({op:'MSTORE'});
      push(BigInt(next()%4*32));instructions.push({op:'MLOAD'});
    }
    const target='exit';
    push(BigInt(next()%2));instructions.push({op:'JUMPI',target});
    push(word());instructions.push({op:'POP'});
    instructions.push({op:'JUMP',target},{op:'JUMPDEST',label:target});
    push(BigInt(next()%97));push(BigInt(next()%4*32));
    instructions.push({op:pick(['RETURN','REVERT'])});
    return {schema:1,seed,index,calldata:'',instructions};
  });
}
export function assemble(record) {
  const labels=new Map(); let pc=0;
  const size=i=>i.op==='PUSH'?33:['JUMP','JUMPI'].includes(i.op)?4:1;
  for(const i of record.instructions) {if(i.label){if(labels.has(i.label))throw Error('duplicate label');labels.set(i.label,pc);}pc+=size(i);}
  if(pc>65535)throw Error('program too large');
  const chunks=[];
  for(const i of record.instructions) {
    if(i.op==='PUSH') {const n=BigInt(i.value);if(n<0n||n>=W)throw Error('invalid word');chunks.push('7f'+n.toString(16).padStart(64,'0'));}
    else if(['JUMP','JUMPI'].includes(i.op)) {
      const dest=labels.get(i.target);
      if(dest===undefined||!record.instructions.some(x=>x.label===i.target&&x.op==='JUMPDEST'))throw Error('invalid target');
      chunks.push('61'+dest.toString(16).padStart(4,'0')+opcodes[i.op].toString(16));
    } else {if(!Object.hasOwn(opcodes,i.op))throw Error('unknown opcode');chunks.push(opcodes[i.op].toString(16).padStart(2,'0'));}
  }
  return chunks.join('');
}
