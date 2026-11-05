'use strict';

/** Lossless tokens: strings and comments are indivisible, including imports. */
function tokens(text){
  const result=[];let i=0;
  while(i<text.length){
    if(/\s/.test(text[i])){i++;continue;}
    const start=i;let kind='punct';
    if(text.startsWith('//',i)){kind='comment';i=text.indexOf('\n',i);if(i<0)i=text.length;}
    else if(text.startsWith('/*',i)){kind='comment';const end=text.indexOf('*/',i+2);i=end<0?text.length:end+2;}
    else if(text[i]==='"'||text[i]==="'"||/^(?:hex|unicode)["']/.test(text.slice(i))){kind='string';const prefix=/^(?:hex|unicode)(?=["'])/.exec(text.slice(i));if(prefix)i+=prefix[0].length;const quote=text[i++];while(i<text.length){if(text[i]==='\\'){i+=2;continue;}if(text[i++]===quote)break;}}
    else if(/\d/.test(text[i])||text[i]==='.'&&/\d/.test(text[i+1]??'')){kind='number';const literal=/^(?:0[xX][0-9a-fA-F_]+|(?:\d[\d_]*(?:\.[\d_]+)?|\.[\d_]+)(?:[eE][+-]?[\d_]+)?)/.exec(text.slice(i));i+=literal[0].length;}
    else if(/[\w$]/.test(text[i])){kind='word';while(i<text.length&&/[\w$]/.test(text[i]))i++;}
    else {const op=['>>=','<<=','**','++','--','=>','==','!=','<=','>=','&&','||','+=','-=','*=','/=','%=','<<','>>','&=','|=','^='].find(x=>text.startsWith(x,i));i+=op?.length||1;}
    result.push({text:text.slice(start,i),start,end:i,kind});
  }
  return result;
}
function imports(text){
  const ts=tokens(text).filter(t=>t.kind!=='comment'),result=[];
  for(let i=0;i<ts.length;i++)if(ts[i].text==='import'){
    let path;while(++i<ts.length&&ts[i].text!==';')if(ts[i].kind==='string')path=ts[i].text.slice(1,-1);
    if(path)result.push(path);
  }
  return result;
}

/** Whitespace-only formatting. Verify token equality before returning edits. */
function format(text,{tabSize=2,insertSpaces=true}={}){
  const ts=tokens(text);let output='',line='',depth=0,parens=0;
  const indent=()=>insertSpaces?' '.repeat(Math.min(16,Math.max(1,tabSize))*Math.max(0,depth)):'\t'.repeat(Math.max(0,depth));
  const flush=()=>{if(line.trim())output+=indent()+line.trimEnd()+'\n';line='';};
  const put=(s,space=true)=>{if(space&&line&&!/[\s.(\[]$/.test(line))line+=' ';line+=s;};
  for(let i=0;i<ts.length;i++){
    const t=ts[i],s=t.text,previous=ts[i-1]?.text;
    if(t.kind==='comment'){if(s.startsWith('//')){put(s);flush();}else{flush();put(s,false);flush();}continue;}
    if(s==='{'){put(s);flush();depth++;}
    else if(s==='}'){flush();depth=Math.max(0,depth-1);put(s,false);if(![';',',',')',']','else','catch'].includes(ts[i+1]?.text))flush();}
    else if(s===';'){put(s,false);if(parens===0)flush();else line+=' ';}
    else if(s==='('){put(s,['if','while','for','switch','catch'].includes(previous));parens++;}
    else if(s===')'){line=line.trimEnd();put(s,false);parens=Math.max(0,parens-1);}
    else if(s==='['||s==='.'||s===']'){line=line.trimEnd();put(s,false);}
    else if(s===','){line=line.trimEnd();put(s,false);line+=' ';}
    else if(['++','--'].includes(s)){put(s,false);}
    else put(s);
  }
  flush();
  if(JSON.stringify(tokens(output).map(t=>t.text))!==JSON.stringify(ts.map(t=>t.text)))throw new Error('Formatting changed Solidity tokens');
  return output;
}
module.exports={tokens,imports,format};
