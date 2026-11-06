// Display-only diagnostic relocation. Migrated diagnostics are never verification results or cache entries.
'use strict';
const {offset,position,applyChanges}=require('./language-services.cjs');
function migrateRange(range,text,change){
  if(!change.range)return null;
  const from=offset(text,change.range.start),to=offset(text,change.range.end);
  let start,end;try{start=offset(text,range.start);end=offset(text,range.end);}catch{return null;}
  if(end<start)return null;
  const next=applyChanges(text,[change]),delta=change.text.length-(to-from);
  let a=start,b=end;
  if(start===from&&end===to&&to>from)return null;
  if(end<=from){} // End affinity stays before an insertion.
  else if(start>=to){a+=delta;b+=delta;}
  else if(start<from&&end>to){b+=delta;}
  else return null; // An edit crossing an edge makes that old location unreliable.
  return {start:position(next,a),end:position(next,b)};
}
function migrateDiagnostics(items,sourceUri,editedUri,text,changes){
  let result=items;
  for(const change of changes){
    result=result.flatMap(item=>{
      const range=sourceUri===editedUri?migrateRange(item.range,text,change):item.range;if(!range)return [];
      let affected=sourceUri===editedUri;
      const relatedInformation=item.relatedInformation?.flatMap(info=>{
        if(info.location.uri!==editedUri)return [info];affected=true;
        const related=migrateRange(info.location.range,text,change);
        return related?[{...info,location:{...info.location,range:related}}]:[];
      });
      const migrated={...item,range,...(relatedInformation?{relatedInformation}:{})};
      if(affected){migrated.severity=item.severity===1?2:item.severity;migrated.message=item.message.startsWith('Outdated: ')?item.message:'Outdated: '+item.message;}
      return [migrated];
    });
    text=applyChanges(text,[change]);
  }
  return result;
}
function incrementalChange(before,after){
  let start=0;while(start<before.length&&start<after.length&&before[start]===after[start])start++;
  const split=(text,i)=>i>0&&i<text.length&&(text[i-1]==='\r'&&text[i]==='\n'||/[\uD800-\uDBFF]/.test(text[i-1])&&/[\uDC00-\uDFFF]/.test(text[i]));
  while(split(before,start)||split(after,start))start--;
  let oldEnd=before.length,newEnd=after.length;
  while(oldEnd>start&&newEnd>start&&before[oldEnd-1]===after[newEnd-1]){oldEnd--;newEnd--;}
  while(split(before,oldEnd)||split(after,newEnd)){oldEnd++;newEnd++;}
  return {range:{start:position(before,start),end:position(before,oldEnd)},text:after.slice(start,newEnd)};
}
module.exports={migrateRange,migrateDiagnostics,incrementalChange};
