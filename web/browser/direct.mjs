import {VerifierWorker} from './verifier-worker.mjs';
import {requestFor,decorate} from '../../vscode/src/direct-model.cjs';
let transport,ready,unavailable=false;
export async function prepareDirect(progress){
  if(unavailable)return null;
  transport??=new VerifierWorker('/direct-worker.js',progress);
  const owned=transport;
  try{
    ready??=owned.boot();const result=await ready;
    if(transport!==owned)throw Object.assign(new Error('Verification cancelled'),{code:'CANCELLED'});
    if(result.kind!=='generated-c-wasm')throw new Error('Direct verifier is not installed');
    return result;
  }catch(error){
    if(error.code==='CANCELLED'||transport!==owned)throw error;
    owned.dispose();transport=undefined;ready=undefined;unavailable=true;
    progress?.({method:'log',message:'Using the general verifier: '+error.message});return null;
  }
}
export async function checkDirect(contract,options,timeoutMs){
  if(!transport||unavailable)return null;
  const input=requestFor(contract,options);if(!input)return null;
  const owned=transport;let result;
  try{result=await owned.request('check',input,timeoutMs);}
  catch(error){
    if(error.code==='CANCELLED'||error.code==='TIMEOUT')throw error;
    owned.dispose();if(transport===owned){transport=undefined;ready=undefined;unavailable=true;}
    return null;
  }
  return decorate(contract,result);
}

export function cancelDirect(reason){transport?.dispose(reason);transport=undefined;ready=undefined;unavailable=false;}
export function abandonDirect(reason){transport?.abandon(reason);}
