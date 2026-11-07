import {writeFileSync} from 'node:fs';
import {compiler} from '../../scripts/evm-reference/generated.mjs';
import {replayDeclarationPacking} from './declaration-packing-reference.mjs';
const [pin,output]=process.argv.slice(2);if(!pin||!output)throw Error('pinned compiler and output required');
const report=await replayDeclarationPacking(compiler(pin),v=>writeFileSync(output+'.viaIR-'+v.viaIR+'.json',JSON.stringify(v,null,2)+'\n'));writeFileSync(output,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({status:report.status,pipelines:report.variants.length,orderedCalls:report.variants.reduce((s,x)=>s+(x.observed?.length??0),0)}));if(report.status!=='working')process.exitCode=1;
