// H68 fixture migration only: no AST translation or fabricated metadata.
export function retainCompilerMetadata(result) {
 const walk=(n,f)=>{if(!n||typeof n!=="object")return;f(n);for(const v of Object.values(n))if(Array.isArray(v))v.forEach(x=>walk(x,f));else if(v&&typeof v==="object")walk(v,f);};
 const key=n=>JSON.stringify([n.nodeType,n.src]);
 const raw=new Map();
 walk(result.rawAst,n=>{if(!n.nodeType)return;const k=key(n);const xs=raw.get(k)??[];xs.push(n);raw.set(k,xs);});
 const fixture=structuredClone(result.fixture);let fields=0;
 walk(fixture.ast,n=>{if(!n.nodeType)return;const candidates=(raw.get(key(n))??[]).filter(x=>n.id===undefined||x.id===n.id);if(!candidates.length)throw new Error("normalized node lacks compiler identity: "+key(n));
  const source=candidates[0];const metadata=x=>JSON.stringify([x.typeDescriptions,x.tryCall]);if(candidates.some(x=>metadata(x)!==metadata(source)))throw new Error("ambiguous compiler metadata identity");
  if(typeof source.typeDescriptions?.typeIdentifier==="string"&&!n.typeDescriptions)throw new Error("normalized node lost required typeDescriptions");
  if(n.typeDescriptions&&typeof source.typeDescriptions?.typeIdentifier==="string"){
   if(n.typeDescriptions.typeString!==source.typeDescriptions.typeString)throw new Error("compiler type metadata mismatch");
   if(n.typeDescriptions.typeIdentifier!==undefined&&n.typeDescriptions.typeIdentifier!==source.typeDescriptions.typeIdentifier)throw new Error("conflicting typeIdentifier");
   if(n.typeDescriptions.typeIdentifier===undefined)fields++;
   n.typeDescriptions.typeIdentifier=source.typeDescriptions.typeIdentifier;
  }
  if(typeof source.tryCall==="boolean"){
   if(n.tryCall!==undefined&&n.tryCall!==source.tryCall)throw new Error("conflicting tryCall");
   if(n.tryCall===undefined)fields++;
   n.tryCall=source.tryCall;
  }
 });
 const strip=x=>{const copy=structuredClone(x);walk(copy,n=>{if(n.typeDescriptions)delete n.typeDescriptions.typeIdentifier;delete n.tryCall;});return copy;};
 if(JSON.stringify(strip(fixture.ast))!==JSON.stringify(strip(result.annotationAst)))throw new Error("metadata retention changed normalized syntax or annotations");
 return {fixture,fields};
}
