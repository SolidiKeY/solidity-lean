import {createFinalizationSession,parseAddress,parseWord,parseBytes,type Host1Session,type CommittedEngineSubstate,type FinalizedMessageReceipt} from '../../scripts/host1-finalization/index.mjs';
const a=parseAddress('0x'+'00'.repeat(20)),b=parseBytes('0x'),w=parseWord('0x'+'00'.repeat(32));
async function consumer(s:Host1Session){const r:FinalizedMessageReceipt=await s.execute({id:'typed',kind:'call',to:a,data:b});
 // @ts-expect-error Receipts are not mutable state.
 r.ordinal=1;
 // @ts-expect-error Missing target is not a typed CALL.
 await s.execute({id:'wrong',kind:'call',data:b});
 // @ts-expect-error A CREATE has no external target.
 await s.execute({id:'wrong',kind:'create',to:a,data:b});
 // @ts-expect-error Static calls cannot transfer value.
 await s.execute({id:'wrong',kind:'static',to:a,data:b,value:1n});
 // @ts-expect-error Bare strings cannot bypass canonical byte parsing.
 await s.execute({id:'wrong',kind:'create',data:'0x'});
 // @ts-expect-error Addresses and slots have distinct brands.
 const slot:typeof w=a;
 // @ts-expect-error A finite observed domain is not a total Ethereum world.
 const assumed=r.post[a].nonce;
 return r.environment.transactionEnvelope satisfies false;}
void consumer;void createFinalizationSession;

function actualEngineSubstate(s:CommittedEngineSubstate){s.createdAddresses.has(a);s.selfdestruct.get(a);return s;}
void actualEngineSubstate;
