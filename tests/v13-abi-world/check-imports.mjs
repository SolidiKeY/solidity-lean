import {readFileSync, existsSync} from 'node:fs';
import {loadGraph, reach} from '../../scripts/import-fanout.mjs';
const {graph}=loadGraph();
const owned=[...graph.keys()].filter(x=>x.startsWith('Solidity.Backend.AbiWorld.'));
const forbidden=/^Solidity\.(Frontend|Evm|Tools)\.|^Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)|^Solidity\.Calculus\.(Print|Surface|Quote|NamedTerm|TacticSyntax)/;
const expected=['ErrorLayout','ErrorRoundtrip','ErrorControls','ErrorEmission','WorldFrames','Controls','PublishedCallControls','PublishedLayout','PublishedLayoutControls','CatchTransport','CatchControls','CompiledMemoryCalls','ReturnedBytes','ReturnedBytesPrefix','ReturnedBytesControls','LibraryFrameTransport','LibraryFrameControls','EntryTransport','EntryControls','PacketEmission','EnumEntry','EnumControls','WordArrayPacket','WordArrayControls','CallerPacket','MixedPacket','ArrayPairPacket','NestedUintPacket','CanonicalReadback','NestedReadback','BytesReadback','TupleReadback','EntryComposition','BytesArrayReadback','BodyComposition','TripleReadback','WordListReadback','StaticAggregateReadback','DynamicListReadback','DynamicAggregateReadback','ByteSequenceReadback','NestedByteReadback','NestedByteListReadback','RecursiveLayout','RecursiveReadback','RecursiveEntry','LocationPeak','SiblingReadback','ReferenceFields','RawEntryTransport','SeqPrefix','RawFreeTransport'].map(x=>'Solidity.Backend.AbiWorld.'+x);
let bad=0;
if(owned.length!==expected.length || expected.some(x=>!owned.includes(x))){console.log('Missing or unexpected owned module set');bad++;}
for(const m of owned){const file=m.replaceAll('.','/')+'.lean';for(const hit of readFileSync(file,'utf8').matchAll(/^import (Solidity\.[A-Za-z0-9_.]+)$/gm)){if(!existsSync(hit[1].replaceAll('.','/')+'.lean')){console.log(`${file}: unresolved ${hit[1]}`);bad++;}}}
// Only the assigned compiled/array/caller consumers may reach the actual compiler closure.
// CallerPacket additionally consumes sealed V12 declarations in a private combined tree;
// this does not establish publication or permit elaborators.
// Existing modules keep their old Evm exclusion; elaborators stay forbidden everywhere.
const consumers=new Set(['CompiledMemoryCalls','ReturnedBytes','ReturnedBytesPrefix','ReturnedBytesControls','WordArrayPacket','WordArrayControls','CallerPacket','MixedPacket','ArrayPairPacket','NestedUintPacket','CanonicalReadback','NestedReadback','BytesReadback','TupleReadback','EntryComposition','BytesArrayReadback','BodyComposition','TripleReadback','WordListReadback','StaticAggregateReadback','DynamicListReadback','DynamicAggregateReadback','ByteSequenceReadback','NestedByteReadback','NestedByteListReadback','RecursiveLayout','RecursiveReadback','RecursiveEntry','LocationPeak','SiblingReadback','ReferenceFields','RawEntryTransport','SeqPrefix','RawFreeTransport'].map(x=>'Solidity.Backend.AbiWorld.'+x));
const published=new Set(['Solidity.Evm.Compiler',...reach(graph,'Solidity.Evm.Compiler')]);
for(const m of owned) for(const x of reach(graph,m)) if(forbidden.test(x)){
  if(consumers.has(m) && x.startsWith('Solidity.Evm.') && published.has(x)) continue;
  console.log(`${m} reaches ${x}`);bad++;
}
console.log(`${owned.length} owned modules, ${bad} forbidden imports`);
process.exit(bad?1:0);
