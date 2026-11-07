// Refuse DOM-resident but clipped/occluded readiness, and observed capture-interval ABA.
// Geometry is not a raster glyph proof: compositor-only changes remain unobserved.
'use strict';
function probe(expected,stop=false){
 if(stop){const w=window.__solidityParityOutputWatch;if(w){w.observer.disconnect();document.removeEventListener('scroll',w.scroll,true);window.removeEventListener('resize',w.scroll);delete window.__solidityParityOutputWatch;}return true;}
 const panel=document.querySelector('.output-view');if(!panel)return null;
 const key='__solidityParityOutputWatch';let watch=window[key];
 if(!watch||watch.panel!==panel){watch?.observer.disconnect();if(watch){document.removeEventListener('scroll',watch.scroll,true);window.removeEventListener('resize',watch.scroll);}watch={panel,epoch:0,id:crypto.randomUUID(),changes:[]};watch.record=records=>{watch.epoch+=records.length;for(const r of records)if(watch.changes.length<128)watch.changes.push({type:r.type,attribute:r.attributeName,tag:r.target?.nodeName});};watch.observer=new MutationObserver(records=>watch.record(records));watch.observer.observe(document.documentElement,{subtree:true,childList:true,characterData:true,attributes:true});watch.scroll=()=>watch.epoch++;document.addEventListener('scroll',watch.scroll,true);window.addEventListener('resize',watch.scroll);window[key]=watch;}
 watch.record(watch.observer.takeRecords());
 const rect=r=>({left:r.left,top:r.top,right:r.right,bottom:r.bottom}),viewport=rect((panel.querySelector('.overflow-guard')||panel).getBoundingClientRect()),lines=[...panel.querySelectorAll('.view-line')],nodes=[],chars=[];let text='';
 for(const line of lines){const walker=document.createTreeWalker(line,NodeFilter.SHOW_TEXT);let node;while((node=walker.nextNode())){for(let offset=0;offset<node.length;offset++){nodes.push({node,offset});text+=node.data[offset].replace(/\u00a0/g,' ');}}}
 const start=text.indexOf(expected),end=start+expected.length;
 if(start>=0)for(let i=start;i<end;i++){
  const {node,offset}=nodes[i],range=document.createRange();range.setStart(node,offset);range.setEnd(node,offset+1);const boxes=[...range.getClientRects()].map(rect);let clip={left:Math.max(0,viewport.left),top:Math.max(0,viewport.top),right:Math.min(innerWidth,viewport.right),bottom:Math.min(innerHeight,viewport.bottom)},styled=true;
  const styles=[];for(let e=node.parentElement;e;e=e.parentElement){const s=getComputedStyle(e),r=e.getBoundingClientRect();styles.push({tag:e.nodeName,visibility:s.visibility,display:s.display,opacity:s.opacity,overflowX:s.overflowX,overflowY:s.overflowY,rect:rect(r)});if(s.visibility!=='visible'||s.display==='none'||Number(s.opacity)!==1)styled=false;if(/hidden|clip|auto|scroll/.test(s.overflowX)){clip.left=Math.max(clip.left,r.left);clip.right=Math.min(clip.right,r.right);}if(/hidden|clip|auto|scroll/.test(s.overflowY)){clip.top=Math.max(clip.top,r.top);clip.bottom=Math.min(clip.bottom,r.bottom);}}
  const describe=e=>{if(!e)return null;watch.elements??=new WeakMap();watch.nextElement??=0;if(!watch.elements.has(e))watch.elements.set(e,++watch.nextElement);return{id:watch.elements.get(e),tag:e.nodeName,classes:typeof e.className==='string'?e.className:null,role:e.getAttribute?.('role')??null};};
  const points=boxes.map(r=>[[.1,.1],[.9,.1],[.5,.5],[.1,.9],[.9,.9]].map(([x,y])=>{const point={x:r.left+x*(r.right-r.left),y:r.top+y*(r.bottom-r.top)},hit=document.elementFromPoint(point.x,point.y),matches=!!hit&&(hit===node.parentElement||node.parentElement.contains(hit));return{...point,matches,hit:describe(hit),expected:describe(node.parentElement),hitAncestors:[hit?.parentElement,hit?.parentElement?.parentElement].map(describe)};}));
  const inClip=r=>r.right>r.left&&r.bottom>r.top&&r.left>=clip.left&&r.right<=clip.right&&r.top>=clip.top&&r.bottom<=clip.bottom;
  const covered=styled&&boxes.length>0&&boxes.every((r,index)=>inClip(r)&&points[index].every(p=>p.matches));
  const diagnostic=covered?null:{reasons:[...(!styled?['computed-style']:[]),...(!boxes.length?['no-range-box']:[]),...(boxes.some(r=>!inClip(r))?['clip-or-empty-box']:[]),...(points.some(ps=>ps.some(p=>!p.matches))?['hit-ownership']:[])],points,styles:styles.slice(0,24),stylesTruncated:styles.length>24};
  chars.push({unit:expected[i-start],boxes,clip,covered,range:{outputOffset:i,requiredOffset:i-start,nodeOffset:offset},diagnostic});
 }
 const select=[...panel.closest('.part').querySelectorAll('select.monaco-select-box')].filter(e=>e.getClientRects().length).map(e=>e.selectedOptions[0]?.textContent.trim());
 return{watchId:watch.id,epoch:watch.epoch,changes:watch.changes.slice(),clock:performance.now(),expected,text,start,characters:chars,viewport,channel:select.length===1?select[0]:null,scroll:[...panel.querySelectorAll('.monaco-scrollable-element')].map(e=>({left:e.scrollLeft,top:e.scrollTop,transform:e.style.transform}))};
}
function errors(before,after,expected,channel){
 const errors=[];if(!expected||!channel||before?.channel!==channel||after?.channel!==channel)errors.push('foreign/empty required text or channel');for(const [label,s]of [['before',before],['after',after]])if(!s||s.expected!==expected||s.start<0||s.characters?.length!==expected.length||!s.characters.every((c,i)=>c.unit===expected[i]&&c.covered&&c.boxes?.length))errors.push(label+' missing/clipped/occluded character');
 if(!before?.watchId||before.watchId!==after?.watchId||before.epoch!==after?.epoch||!(after.clock>=before.clock)||!before.channel||before.channel!==after?.channel||before.text!==after?.text||JSON.stringify(before.viewport)!==JSON.stringify(after?.viewport)||JSON.stringify(before.scroll)!==JSON.stringify(after?.scroll)||JSON.stringify(before.characters)!==JSON.stringify(after?.characters))errors.push('capture interval changed');return errors;
}
// Preparation samples are not screenshot brackets. Keep the observer epoch intact and
// retain every sample, including refusals. Exactly one screenshot bracket follows.
async function prepare({read,inspect,valid,expected,channel,deadline,now,delay,record}){
 let previous=null;
 while(now()<deadline){
  const visible=await read();if(now()>=deadline){await record({at:now(),visible,glyph:null,refusals:['visible read completed at capture deadline']});break;}
  const glyph=await inspect();const sample={at:now(),visible,glyph};
  const refusals=previous?errors(previous.glyph,glyph,expected,channel):['first preparation sample'];
  if(!valid(visible)||previous&&!valid(previous.visible)||previous&&previous.visible.continuousText!==visible.continuousText)refusals.push('source/channel text not stable');
  if(now()>=deadline)refusals.push('inspection completed at capture deadline');sample.refusals=refusals;await record(sample);
  if(now()>=deadline)break;
  if(previous&&!refusals.length)return{visible,glyph};
  previous=sample;await delay(Math.min(50,Math.max(0,deadline-now())));
 }
 throw Object.assign(Error('Output preparation exhausted original capture deadline'),{code:'TIMEOUT'});
}
module.exports={probe,errors,prepare};
