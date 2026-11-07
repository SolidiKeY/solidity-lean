/** Typed external finite-observation contract. Not an intrinsic Source state,
 * Source adequacy theorem or signed-transaction/runTx result. */
import type {EVMResult} from '../evm-reference/node_modules/@ethereumjs/evm/dist/esm/index.js';
declare const addressTag: unique symbol,wordTag: unique symbol,bytesTag: unique symbol;
export type AddressHex=`0x${string}` & {readonly [addressTag]:true};
export type WordHex=`0x${string}` & {readonly [wordTag]:true};
export type BytesHex=`0x${string}` & {readonly [bytesTag]:true};
export declare function parseAddress(value:unknown):AddressHex;
export declare function parseWord(value:unknown):WordHex;
export declare function parseBytes(value:unknown):BytesHex;
export type CommittedEngineSubstate=Required<Pick<EVMResult['execResult'],'selfdestruct'|'createdAddresses'>>;
export declare const CALLER:AddressHex;
export declare const SCOPE:string;
export interface RequestCommon {readonly id:string;readonly data:BytesHex;}
export type MessageRequest=RequestCommon & (
 {readonly kind:'call';readonly to:AddressHex;readonly value?:bigint} |
 {readonly kind:'create';readonly to?:never;readonly value?:bigint} |
 {readonly kind:'static';readonly to:AddressHex;readonly value?:0n});
export interface ObservedAccount {readonly exists:boolean;readonly nonce:string|null;readonly balance:string|null;readonly code:BytesHex;readonly codeSha256:string;readonly codeHash:WordHex|null;readonly persistent:Readonly<Partial<Record<WordHex,WordHex>>>;readonly transient:Readonly<Partial<Record<WordHex,WordHex>>>;}
export type World=Readonly<Partial<Record<AddressHex,ObservedAccount>>>;
export interface DomainEntry {readonly address:AddressHex;readonly persistent:readonly WordHex[];readonly transient:readonly WordHex[];}
export interface FullLog {readonly emitter:AddressHex;readonly topics:readonly WordHex[];readonly data:BytesHex;}
export type LogCapture={readonly status:'captured';readonly logs:readonly FullLog[]} | {readonly status:'not-provided';readonly logs:null};
export interface MemoryRegion {readonly step:number;readonly pc:number;readonly opcode:string;readonly phase:'before-opcode';readonly offset:string;readonly length:string;readonly allocatedBytes:number;readonly bytes:BytesHex;}
export type MemoryCapture={readonly status:'captured';readonly phase:'after-interpreter';readonly allocatedBytes:number;readonly bytes:BytesHex}|{readonly status:'not-executed'};
export type ReturnDataCapture={readonly status:'captured';readonly bytes:BytesHex}|{readonly status:'not-executed'};
export interface Frame {readonly id:number;readonly parent:number|null;readonly depth:number;readonly caller:AddressHex;readonly to:AddressHex|null;readonly kind:'call'|'create';readonly delegatecall:boolean;readonly messageCodeAddress:AddressHex|null;readonly messageFinalCodeAddress:AddressHex|null;readonly executionAddress:AddressHex|null;readonly codeAddress:AddressHex|null;readonly invocationOpcode:string;readonly lastOpcode:string|null;readonly value:string;readonly data:BytesHex;readonly static:boolean;readonly pre:World;readonly steps:number;readonly regions:readonly MemoryRegion[];readonly output:LogCapture & {readonly bytes:BytesHex;readonly exception:string|null};readonly memory:MemoryCapture;readonly lastCallReturnData:ReturnDataCapture;readonly createdAddress:AddressHex|null;readonly post:World;}
export interface EngineReceipt {readonly inputSha256:string;readonly base:string;readonly engine:'@ethereumjs/evm@10.1.3';readonly hardfork:'osaka';readonly messageGas:'100000000';readonly stepLimit:5000000;}
export interface Destruction {readonly address:AddressHex;readonly beneficiary:AddressHex;}
export interface FinalizedMessageReceipt {
 readonly schema:1;readonly scope:string;readonly ordinal:number;
 readonly request:{readonly id:string;readonly kind:MessageRequest['kind'];readonly to:AddressHex|null;readonly data:BytesHex;readonly value:string;readonly caller:AddressHex;readonly origin:AddressHex};readonly requestSha256:string;
 readonly engine:EngineReceipt;
 readonly environment:{readonly hardfork:'osaka';readonly chainId:'1';readonly messageGas:'100000000';readonly stepLimit:5000000;readonly caller:AddressHex;readonly origin:AddressHex;readonly gasPrice:'0';readonly block:{readonly number:string;readonly coinbase:AddressHex;readonly timestamp:string;readonly difficulty:string;readonly prevRandao:WordHex;readonly gasLimit:string;readonly baseFeePerGas:string|null;readonly slotNumber:string|null;readonly blobGasPrice:string|null};readonly unlimitedCodeAndInitcodeSize:true;readonly transactionEnvelope:false;readonly feeAccounting:false};
 readonly domain:readonly DomainEntry[];readonly pre:World;readonly messagePost:World;readonly post:World;
 readonly frames:readonly Frame[];readonly trace:readonly {readonly kind:'enter'|'exit';readonly frame:number}[];
 readonly operations:readonly {readonly ordinal:number;readonly phase:'message'|'finalization';readonly frame:number|null;readonly kind:string;readonly address:AddressHex|null;readonly slot:WordHex|null;readonly value:null|BytesHex|{readonly nonce:string;readonly balance:string}}[];
 readonly message:LogCapture & {readonly bytes:BytesHex;readonly exception:string|null;readonly createdAddress:AddressHex|null;readonly selfdestruct:readonly Destruction[];readonly createdAddresses:readonly AddressHex[];readonly executionGasUsed:string;readonly gasRefund:string|null;readonly metrics:{readonly steps:number;readonly maxStack:number}};
 readonly finalization:{readonly kind:'explicit-osaka-message-finalization';readonly eligible:readonly Destruction[];readonly retained:readonly Destruction[];readonly deletedAccounts:readonly AddressHex[];readonly transientBefore:Readonly<Record<AddressHex,Readonly<Record<WordHex,BytesHex>>>>;readonly transientAfter:Readonly<Record<string,never>>;readonly actions:readonly {readonly ordinal:number;readonly kind:'delete'|'journal-cleanup'|'transient-clear'|'state-commit';readonly reason?:'selfdestruct'|'eip161';readonly address?:AddressHex}[];readonly originalStorageCache:'cleared by shared factory at next message boundary'};
}
export interface SetupSeed {readonly address:AddressHex;readonly nonce:bigint;readonly balance:bigint;readonly code:BytesHex;readonly storage:Readonly<Record<WordHex,WordHex>>;}
export interface Host1Session {readonly engine:EngineReceipt;readonly caller:AddressHex;execute(request:MessageRequest):Promise<FinalizedMessageReceipt>;snapshot():Promise<World>;}
export declare class Host1Blocked extends Error {}
export declare function createFinalizationSession(options?:{readonly seeds?:readonly SetupSeed[];readonly watch?:readonly DomainEntry[]}):Promise<Host1Session>;
/** Requires independent request identity and ordinal, not values read from the receipt. */
export declare function validateFinalizedMessage(value:unknown,request:MessageRequest,ordinal:number):asserts value is FinalizedMessageReceipt;
export declare function verifyEngine(read?:(path:string)=>Uint8Array):EngineReceipt;
export declare function sha(value:Uint8Array|string):string;

export declare function readObservedAccount(receipt:FinalizedMessageReceipt,phase:'pre'|'messagePost'|'post',address:AddressHex):ObservedAccount;
export declare function readObservedSlot(receipt:FinalizedMessageReceipt,phase:'pre'|'messagePost'|'post',address:AddressHex,bank:'persistent'|'transient',slot:WordHex):WordHex;
