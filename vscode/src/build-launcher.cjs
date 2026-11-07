// Dedicated build session: the parent transfers ownership before sending the existing command.
'use strict';
const {spawn}=require('node:child_process'),{terminateTree}=require('./backend.cjs'),{trackChild}=require('./child-lifetime.cjs');
let child,started=false;
process.on('message',message=>{if(started)return;started=true;if(typeof message?.command!=='string'||!Array.isArray(message.args)||message.args.some(arg=>typeof arg!=='string'))process.exit(1);
 child=spawn(message.command,message.args,{cwd:process.cwd(),stdio:['ignore','inherit','inherit'],windowsHide:true,shell:false});trackChild(child);
 child.once('error',error=>{process.stderr.write(error.message+'\n');process.exit(1);});child.once('close',code=>process.exit(code===0?0:1));
});
const stop=()=>{if(child)terminateTree(child);process.exit(1);};process.on('disconnect',stop);for(const signal of ['SIGTERM','SIGINT'])process.on(signal,stop);process.send?.({ready:true});
