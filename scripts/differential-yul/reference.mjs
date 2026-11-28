/** Reference loading is shared with scripts/differential, not a new EVM oracle. */
import {createHash} from 'node:crypto';
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
const bytes = hex => {
  if (typeof hex !== 'string' || !/^0x(?:[0-9a-f]{2})*$/.test(hex)) throw Error('invalid hex bytes');
  return Uint8Array.from(Buffer.from(hex.slice(2), 'hex'));
};

export async function loadCompiler(path) {
  const {compiler} = await import('../evm-reference/generated.mjs');
  return compiler(path);
}

export function compileSource(compile, source, {optimizer = true} = {}) {
  if (typeof source !== 'string' || !source.length || typeof optimizer !== 'boolean')
    throw Error('invalid compilation request');
  const input = {language:'Solidity', sources:{'generated.sol':{content:source}}, settings:{
    viaIR:true, optimizer:{enabled:optimizer,runs:200}, evmVersion:'osaka',
    metadata:{appendCBOR:false}, outputSelection:{'*':{'*':['ir','irOptimized',
      'storageLayout','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}
  }};
  const output = compile(input);
  const diagnostics = output.errors ?? [];
  if (diagnostics.some(d => d.severity === 'error'))
    throw Error('solc rejected source: ' + diagnostics.filter(d=>d.severity==='error').map(d=>d.formattedMessage??d.message).join('\n'));
  const artifact = output.contracts?.['generated.sol']?.Generated;
  if (!artifact || !artifact.ir || !artifact.irOptimized) throw Error('missing Generated IR artifact');
  for (const code of [artifact.evm?.bytecode?.object, artifact.evm?.deployedBytecode?.object])
    if (typeof code !== 'string' || !/^(?:[0-9a-f]{2})+$/.test(code))
      throw Error('missing or unlinked bytecode');
  const layout = artifact.storageLayout;
  if (!Array.isArray(layout?.storage) || layout.storage.length !== 2 ||
      layout.storage.some((entry,i) => entry.label !== ['x','y'][i] || entry.slot !== String(i) ||
        entry.offset !== 0 || layout.types?.[entry.type]?.label !== 'uint256' ||
        layout.types?.[entry.type]?.encoding !== 'inplace' || layout.types?.[entry.type]?.numberOfBytes !== '32'))
    throw Error('unhandled storage layout: expected uint256 x/y at slots 0/1');
  return {artifact,input,diagnostics};
}

/** Deploy once, execute one transaction, and observe committed storage after
 * rollback. Non-revert exceptional halts and engine limits are blocked, never
 * counted as agreement with a Lean revert. The generator owns slot coverage. */
export async function executeArtifact(artifact, {calldata, signature='run()', slots=['0','1']} = {}, deps) {
  if (!Array.isArray(slots) || !slots.length || new Set(slots).size !== slots.length ||
      slots.some(s=>typeof s!=='string'||!/^(0|[1-9][0-9]*)$/.test(s)||BigInt(s)>=2n**256n))
    throw Error('invalid storage slots');
  if (calldata === undefined) {
    const selector = artifact.evm?.methodIdentifiers?.[signature];
    if (!/^[0-9a-f]{8}$/.test(selector??'')) throw Error('missing canonical selector');
    calldata = '0x'+selector;
  }
  const payload = bytes(calldata);
  const runtime = bytes('0x'+artifact.evm.deployedBytecode.object);
  const creation = bytes('0x'+artifact.evm.bytecode.object);
  const {machine, observation, creationObservation} = deps ?? await import('../evm-reference/replay.mjs');
  const vm = await machine();
  const deployed = await vm.call({data:creation});
  const deployment = creationObservation(deployed.result.execResult, 'constructor', deployed.metrics);
  const address = deployed.result.createdAddress;
  if (deployment.failed || !address) throw Error('reference deployment failed');
  if (deployment.runtimeCodeSha256 !== sha(runtime)) throw Error('deployed runtime hash differs');
  const executed = await vm.call({to:address,data:payload});
  const run = observation(executed.result.execResult, signature, executed.metrics);
  if (run.exception !== null && run.exception !== 'revert') throw Error('reference exceptional halt: '+run.exception);
  const storage = [];
  for (const slot of slots) {
    const value = await vm.evm.stateManager.getStorage(address, bytes('0x'+BigInt(slot).toString(16).padStart(64,'0')));
    storage.push(value.length ? BigInt('0x'+Buffer.from(value).toString('hex')).toString() : '0');
  }
  return {failed:run.failed,returnData:run.returnData,exception:run.exception,storage,slots,
    calldata,deployment,metrics:executed.metrics};
}

/** The fixed grammar has exactly two physical words, x/y at slots 0/1. */
export function compareObservations(lean, reference) {
  for (const value of [lean,reference]) {
    if (typeof value?.failed !== 'boolean' || typeof value.returnData !== 'string' ||
        !/^0x(?:[0-9a-f]{2})*$/.test(value.returnData) || !Array.isArray(value.storage) ||
        value.storage.length !== 2 || !Array.isArray(value.slots) || value.slots.length !== 2 ||
        value.slots[0] !== '0' || value.slots[1] !== '1' ||
        value.storage.some(s=>typeof s!=='string'||!/^(0|[1-9][0-9]*)$/.test(s)||BigInt(s)>=2n**256n))
      throw Error('invalid observation');
  }
  if (reference.exception !== null && reference.exception !== 'revert') throw Error('unadapted reference halt');
  if (reference.failed !== (reference.exception === 'revert')) throw Error('inconsistent reference halt');
  return lean.failed === reference.failed && lean.returnData === reference.returnData &&
    lean.storage.length === reference.storage.length && lean.storage.every((s,i)=>s===reference.storage[i]);
}
