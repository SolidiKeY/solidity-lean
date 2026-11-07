// Native observation resource admission; sampling is not an aggregate cgroup.
'use strict';
const fs=require('node:fs');
function resourceState(text=fs.readFileSync('/proc/meminfo','utf8')){
 const bytes=name=>{const match=text.match(new RegExp('^'+name+':\\s+(\\d+) kB$','m'));if(!match)throw Error('Missing resource field '+name);const value=Number(match[1])*1024;if(!Number.isSafeInteger(value))throw Error('Invalid resource field '+name);return value;};
 return {availableBytes:bytes('MemAvailable'),swapTotalBytes:bytes('SwapTotal')};
}
function resourcesAllowed(state,options={},rssBytes=0){return Number.isSafeInteger(state?.availableBytes)&&state.availableBytes>=(options.memoryReserveMiB??12288)*1024**2&&state.swapTotalBytes===0&&Number.isSafeInteger(rssBytes)&&rssBytes>=0&&rssBytes<=(options.memoryMaxMiB??4096)*1024**2;}
module.exports={resourceState,resourcesAllowed};
