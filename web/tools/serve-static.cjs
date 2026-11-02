'use strict';
// Development/QA asset server only. The deployed website consists of these
// files; there is no compiler endpoint, language server, shell or WebSocket.
const http=require('node:http'),fs=require('node:fs'),path=require('node:path');
const types={'.html':'text/html; charset=utf-8','.js':'text/javascript','.css':'text/css','.json':'application/json','.svg':'image/svg+xml','.wasm':'application/wasm','.ttf':'font/ttf'};
function createStaticServer({root=path.resolve(__dirname,'../dist'),port=4173}={}){
  const headerFile=path.join(root,'_headers');
  const security=fs.existsSync(headerFile)?Object.fromEntries(fs.readFileSync(headerFile,'utf8').split('\n').flatMap(line=>{const match=/^  ([\w-]+): (.*)$/.exec(line);return match?[[match[1],match[2]]]:[];})):{};
  const server=http.createServer((req,res)=>{
    const headers={'Cache-Control':'no-cache','X-Content-Type-Options':'nosniff','Cross-Origin-Opener-Policy':'same-origin','Cross-Origin-Embedder-Policy':'require-corp',...security};
    const reply=(status,text)=>{res.writeHead(status,{...headers,'Content-Type':'text/plain'});res.end(text);};
    if(!['GET','HEAD'].includes(req.method))return reply(405,'Static assets only');
    try{const name=decodeURIComponent(new URL(req.url,'http://localhost').pathname);const file=path.resolve(root,'.'+(name==='/'?'/index.html':name));
      if(!file.startsWith(root+path.sep)||!fs.statSync(file).isFile())return reply(404,'Not found');
      res.writeHead(200,{...headers,'Content-Type':types[path.extname(file)]||'application/octet-stream'});if(req.method==='HEAD')res.end();else fs.createReadStream(file).pipe(res);
    }catch{reply(404,'Not found');}
  });
  return {server,async listen(){await new Promise((resolve,reject)=>{server.once('error',reject);server.listen(port,'127.0.0.1',resolve);});return 'http://127.0.0.1:'+server.address().port;},async close(){await new Promise(resolve=>{
    server.close(resolve);
    // Offline QA deliberately stops the host while the browser remains open.
    // Do not let a retained HTTP connection postpone that disconnection.
    server.closeAllConnections();
  });}};
}
if(require.main===module){const app=createStaticServer({port:Number(process.env.PORT||4173),...(process.argv.includes('--single')?{root:path.resolve(__dirname,'../single-file')}:{} )});app.listen().then(url=>console.log('Browser-only website: '+url)).catch(error=>{console.error(error);process.exitCode=1;});for(const signal of ['SIGINT','SIGTERM'])process.once(signal,async()=>{await app.close();process.exit();});}
module.exports={createStaticServer};
