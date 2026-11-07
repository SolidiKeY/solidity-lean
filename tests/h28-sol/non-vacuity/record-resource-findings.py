#!/usr/bin/env python3
"""Keep unqueried representation/resource field instances visible, not excluded."""
import fcntl,hashlib,json,pathlib
here=pathlib.Path(__file__).resolve().parent;root=here.parents[2]
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
rows=[
('ROOM-LOOP','MemoryLoopCompile.lean',78,80,'Positive reached loop allocation Demand is not exercised by scalar require(true); current Room uses nonallocating cost-zero branch.'),
('ROOM-SCOPE','MemoryLoopScope.lean',129,132,'Positive reached scoped-loop allocation Demand is not exercised by scalar require(true).'),
('CALLCOPY-COST','MemoryGrowResult.lean',36,39,'Calls and storage-copy clients use cost=0; their positive allocation-capacity branch is unexercised. Primitive memory allocation separately constructs a positive branch.'),
('OBJECT-COST','MemoryObjectAllocator.lean',109,112,'Copy-construction client uses cost=0. Construction allocation and near-end rejection separately inhabit/check positive allocator cost.'),
('COPY-EXTENT','Compiler.lean',207,219,'MemoryCopy/fixed/copyConstruction clients satisfy copyBoundProg=0 <= 1. A positive copied extent has no witness here.'),
('FIXED-LIVE','MemoryFixedStorageCopy.lean',21,26,'Shared heap contains a dynamic uint array; fixed-array HRef objects and their element observations are not instantiated.'),
('REFARRAY-LIVE','MemoryRefArray.lean',134,145,'Rebinding a primitive uint array does not instantiate a reference-element array or its child pointer observations.'),
('DISTINCT-OWNERS','MemoryObjects.lean',48,53,'Single-object heap leaves the distinct-ID separation antecedent empty; no distinct pair is constructed.'),
('STRUCT-LIVE','MemoryObjects.lean',86,91,'No actual struct object is present in this allocated-uint-array heap; struct representation fields are not queried.'),
('REF-FIELDS','MemoryRefs.lean',14,18,'No actual struct reference field is present; reference-field observations are not instantiated.')]
out=[]
for suffix,file,start,end,obligation in rows:
 path='Solidity/Evm/'+file;raw=(root/path).read_bytes();text='\n'.join(raw.decode().splitlines()[start-1:end])
 out.append(dict(id='H28-RESOURCE-'+suffix,status='durable-open',theorem_falsity=False,source=path,start_line=start,end_line=end,text=text,source_sha256=hashlib.sha256(raw).hexdigest(),text_sha256=hashlib.sha256(text.encode()).hexdigest(),missing_constructive_obligation=obligation,interpretation='Unexercised field instance, not global Input inconsistency, theorem falsity, an exclusion, or a producer audit.'))
(here/'resource-findings.json').write_text(json.dumps({'status':'incomplete field-instance coverage','findings':out},indent=2)+'\n')
print(len(out),'source-bound resource/representation limitations retained')
