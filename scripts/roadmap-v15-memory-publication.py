#!/usr/bin/env python3
"""Source/provenance accounting only. Never certifies Lean or EVM semantics."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
PUBLICATION="93920309f5c800c9ce4809bc74700ed4fde65fb2"
BLOBS={
 "Memory":"8961ccd08702db09c51036c9d4e2327ab41f5907",
 "MemoryBytes":"8727dfb5cc985cf0ffe0e6d3be3587361100b0e6",
 "MemoryRefinement":"1253ed73d0ca43af9634d303551199c646694d6f",
 "MemoryComposition":"1cce99c1b9660f0d8da58fb1e1be443b5a32cbb5"}
CONSUMERS=("reference_big_reader reference_array_reader reference_encoding_bytes "
 "reference_encoding_array reference_encoding_scalar reference_encoding_nat_modulo "
 "reference_encoding_injective reference_scalar_immediate reference_signed_observation "
 "reference_unsigned_observation reference_typed_abi_bytes reference_unsigned_cleanup "
 "reference_signed_cleanup reference_encoding_sequence reference_complete_observation").split()
CONDITIONAL={"MemoryBytes":["serialize_eq","serialize","write_inbounds","readback","write_readback"],
 "MemoryRefinement":["lookup_represents","store_preserves","load_refines","store_refines","store_lookup_same","store_lookup_other"],
 "MemoryComposition":["stored_represents","populated_lookup","populated_composition_values"]}
def git_blob(text):
 b=text.encode();return hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
def published_sources(root=ROOT):
 # Decode raw UTF-8 without universal-newline translation: provenance is bytes.
 return {m:(root/"Bridge/SolidityBridge/ExternalEvm"/(m+".lean")).read_bytes().decode("utf-8") for m in BLOBS}
def consumer_source(root=ROOT):
 # Readers have a narrow actual UInt256 import; encoding retains memory imports.
 # This concatenation validates all original names, never kernel certification.
 directory=root/"Bridge/SolidityBridge/RoadmapV15"
 return "\n".join((directory/(m+".lean")).read_bytes().decode("utf-8")
   for m in ["ReferenceReader","ReferenceEncoding"])
def verify_blobs(sources):
 if set(sources)!=set(BLOBS):raise ValueError("missing/duplicate publication module")
 for m,s in sources.items():
  if git_blob(s)!=BLOBS[m]:raise ValueError("published source drift: "+m)
def declaration(text,name):
 match=re.search(r"^(?:theorem|def|structure) "+re.escape(name)+r"(?=\s|\()",text,re.M)
 if not match:raise ValueError("missing declaration: "+name)
 tail=text[match.start():]
 end=re.search(r"\n(?:private |theorem |def |structure |end )",tail)
 return tail[:end.start()] if end else tail
def header(text,name):return declaration(text,name).split(":=",1)[0]
def require(condition,message):
 if not condition:raise ValueError(message)
def classify_sources(sources,consumer):
 pure=header(sources["MemoryBytes"],"encoding_spec");flat=" ".join(pure.split())
 require("PaddingCorrect" not in pure,"encoding_spec gained allocator premise")
 require("(v : EvmYul.UInt256)" in flat and "(encoding v).size = 32" in flat and
   "EvmYul.fromByteArrayBigEndian (encoding v) = v.toNat" in flat,"pure exact32 reader contract changed")
 enc=declaration(sources["MemoryBytes"],"encoding")
 require("ffi." not in enc and "v.toByteArray" not in enc,"pure encoding replaced with FFI serialization")
 conditional=[]
 for module,names in CONDITIONAL.items():
  for name in names:
   h=header(sources[module],name)
   # In-bounds byte operations require the length-zero allocator equation.
   allocator="PaddingCorrect" if name not in ("write_inbounds","readback","write_readback") else "ffi.ByteArray.zeroes"
   require(allocator in h,"omitted allocator clause: "+name)
   conditional.append(dict(module=module,declaration=name,allocatorClause=allocator,status="open; no allocator witness"))
 bounded=declaration(sources["Memory"],"Bounded")
 require("32 * cells < EvmYul.UInt256.size" in bounded and "32 * cells < 2 ^ 64" in bounded,"missing nonwrapping capacity bounds")
 run=declaration(sources["Memory"],"run")
 require("EvmYul.EVM.step 1 0 (some op)" in run,"runner no longer supplied-opcode/zero-charge")
 rep=declaration(sources["MemoryRefinement"],"Represents")
 for part in ["bounded : Bounded cells","s.activeWords.toNat = cells","s.memory.size = 32 * cells",
              "i < cells","m.mem i = .val (wmod v.toNat)","j < 32"]:
  require(part in rep,"missing numeric preallocation clause: "+part)
 for m,n in [("MemoryRefinement","load_preserves"),("MemoryRefinement","load_state_frame"),("MemoryComposition","populated_represents")]:
  require("PaddingCorrect" not in header(sources[m],n),"incorrectly added allocator premise to "+n)
 names=re.findall(r"^theorem ([A-Za-z0-9_]+)",consumer,re.M)
 require(names==CONSUMERS,"missing/duplicate/unexpected consumer declaration")
 for name in names:
  require("PaddingCorrect" not in header(consumer,name),"consumer assumes missing allocator witness")
 byte_header=" ".join(header(consumer,"reference_encoding_bytes").split())
 require("(encoding v).toList = (toBytesBE 32 v.toNat).toList" in byte_header,"ordered bytes weakened to numeric observation")
 require("Solidity.Evm.External.encode w.toFin" in header(consumer,"reference_encoding_scalar"),"reserved numeric adapter not consumed")
 return dict(publication=PUBLICATION,kind="source-boundary accounting, not a proof certificate",
  unconditionalPublishedSource=["encoding_spec","bytes_list","list_bytes"],conditionalResults=conditional,
  representation="preallocated numeric cells, bounded active/physical extent; no symbolic slots/growth",
  runner="supplied opcodes, positive evaluator fuel and zero charged gas; no fetched-bytecode/X driver",
  otherUnconditionalSource=["load_preserves (representation/index premises)","load_state_frame (representation/index premises)","populated_represents (pure initial representation only)"],
  consumers=[dict(name=n,localKernel="not certified by source accounting") for n in names],
  allocatorWitness="none supplied or assumed",driverDischarged=False,osakaDischarged=False,transactionDischarged=False)
def validate_report(report):
 require(report["allocatorWitness"]=="none supplied or assumed","invented allocator witness")
 require(all(not report[x] for x in ["driverDischarged","osakaDischarged","transactionDischarged"]),"false parent discharge")
 require([x["name"] for x in report["consumers"]]==CONSUMERS,"missing/duplicate consumer report")
 require(all(x["localKernel"]=="not certified by source accounting" for x in report["consumers"]),"source accounting promoted to kernel pass")
 expected={(m,n) for m,ns in CONDITIONAL.items() for n in ns}
 require({(x["module"],x["declaration"]) for x in report["conditionalResults"]}==expected,"omitted conditional producer")
 require(len(report["conditionalResults"])==len(expected),"duplicate conditional producer")
 for row in report["conditionalResults"]:
  expectedClause="ffi.ByteArray.zeroes" if row["declaration"] in ("write_inbounds","readback","write_readback") else "PaddingCorrect"
  require(row["allocatorClause"]==expectedClause and row["status"]=="open; no allocator witness","allocator obligation discharged/omitted/replaced")
if __name__=="__main__":
 sources=published_sources();verify_blobs(sources)
 consumer=consumer_source()
 report=classify_sources(sources,consumer);validate_report(report)
 print(json.dumps(report,indent=2))
