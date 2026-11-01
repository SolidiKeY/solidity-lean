'use strict';
const fs=require('node:fs');
const path=require('node:path');
const {PNG}=require('pngjs');
async function main(){
  const [referencePath,webPath,output=path.resolve(__dirname,'../artifacts')]=process.argv.slice(2);
  if(!referencePath||!webPath)throw new Error('Usage: node test/compare.cjs REFERENCE.png WEB.png [OUTPUT_DIRECTORY]');
  const reference=PNG.sync.read(fs.readFileSync(referencePath)),web=PNG.sync.read(fs.readFileSync(webPath));
  if(reference.width!==web.width||reference.height!==web.height)throw new Error('Capture both workbenches at identical viewport sizes');
  const pixelmatch=(await import('pixelmatch')).default;
  const diff=new PNG({width:web.width,height:web.height});
  const pixels=pixelmatch(reference.data,web.data,diff.data,web.width,web.height,{threshold:0.1});
  // Compare the code area separately, so large uniform sidebar/panel regions
  // cannot conceal a visibly different editor.
  const region={x:348,y:88,width:Math.min(1000,web.width-348),height:Math.min(540,web.height-88)};
  function crop(png){const result=new PNG({width:region.width,height:region.height});PNG.bitblt(png,result,region.x,region.y,region.width,region.height,0,0);return result;}
  const a=crop(reference),b=crop(web);const codePixels=pixelmatch(a.data,b.data,null,region.width,region.height,{threshold:0.1});
  const comparison={reference:path.basename(referencePath),web:path.basename(webPath),width:web.width,height:web.height,threshold:0.1,ignoreAntialiasing:true,differentPixels:pixels,differentPercent:+(100*pixels/(web.width*web.height)).toFixed(2),codeRegion:region,codeDifferentPercent:+(100*codePixels/(region.width*region.height)).toFixed(2),note:'Pixel similarity measures these screenshots only; it is not evidence of full VS Code feature parity.'};
  fs.mkdirSync(output,{recursive:true});fs.writeFileSync(path.join(output,'visual-diff.png'),PNG.sync.write(diff));fs.writeFileSync(path.join(output,'visual-comparison.json'),JSON.stringify(comparison,null,2)+'\n');
  // A plain side-by-side artifact remains useful without a JavaScript viewer.
  const sideBySide=new PNG({width:web.width*2,height:web.height});PNG.bitblt(reference,sideBySide,0,0,web.width,web.height,0,0);PNG.bitblt(web,sideBySide,0,0,web.width,web.height,web.width,0);fs.writeFileSync(path.join(output,'side-by-side.png'),PNG.sync.write(sideBySide));
  console.log(JSON.stringify(comparison,null,2));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
