import {writeFileSync} from 'node:fs';
import {compiler} from '../../scripts/evm-reference/generated.mjs';
import {replayFrameCalldata} from './frame-calldata-reference.mjs';
const [pin,output]=process.argv.slice(2);if(!pin||!output)throw Error('pinned compiler and output required');
const compile=compiler(pin),asts=[];
const captured=input=>{const out=compile(input);asts.push(out.sources?.['FrameCalldata.sol']?.ast??null);writeFileSync(output+'.ast-pipelines.json',JSON.stringify(asts,null,2)+'\n');return out;};
const report=await replayFrameCalldata(captured,v=>writeFileSync(output+'.viaIR-'+v.viaIR+'.json',JSON.stringify(v,null,2)+'\n'));writeFileSync(output,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({status:report.status,pipelines:report.variants.length,orderedCalls:report.variants.reduce((n,v)=>n+(v.observed?.length??0),0)}));if(report.status!=='working')process.exitCode=1;
