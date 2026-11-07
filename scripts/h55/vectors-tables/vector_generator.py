#!/usr/bin/env python3
"""Generate frozen finite Yul controls from operands and an integer oracle.

This is an external finite test oracle, not a universal Lean proof of opcode
agreement. All generated theorem statements are checked against frozen bytes.
"""
import argparse
import json
import re
from pathlib import Path
import vector_census as census
import vector_codec as codec

MOD=1 << 256
MASK=MOD-1

def signed(n): return n if n < (1 << 255) else n-MOD
def trunc_div(a,b):
    q=abs(a)//abs(b)
    return -q if (a<0) != (b<0) else q

def oracle(op, operands):
    if op not in codec.ARITY or len(operands)!=codec.ARITY[op]: raise ValueError("opcode or arity")
    if any(type(x) is not str or not re.fullmatch(codec.NAT,x) for x in operands): raise ValueError("operand schema")
    args=[int(x)&MASK for x in operands]; a=args[0]; b=args[1] if len(args)>1 else 0
    if op=="iszero": out=int(a==0)
    elif op=="not": out=MASK^a
    elif op=="clz": out=256-a.bit_length()
    elif op=="add": out=a+b
    elif op=="sub": out=a-b
    elif op=="mul": out=a*b
    elif op=="div": out=a//b if b else 0
    elif op=="mod": out=a%b if b else 0
    elif op=="sdiv": out=trunc_div(signed(a),signed(b)) if b else 0
    elif op=="smod":
        if not b: out=0
        else:
            magnitude=abs(signed(a))%abs(signed(b))
            out=-magnitude if signed(a)<0 else magnitude
    elif op=="exp": out=pow(a,b,MOD)
    elif op=="lt": out=int(a<b)
    elif op=="gt": out=int(a>b)
    elif op=="slt": out=int(signed(a)<signed(b))
    elif op=="sgt": out=int(signed(a)>signed(b))
    elif op=="eq": out=int(a==b)
    elif op=="and": out=a&b
    elif op=="or": out=a|b
    elif op=="xor": out=a^b
    elif op=="byte": out=b.to_bytes(32,"big")[a] if a<32 else 0
    elif op=="shl": out=(b<<a) if a<256 else 0
    elif op=="shr": out=(b>>a) if a<256 else 0
    elif op=="sar": out=(signed(b)>>a) if a<256 else (-1 if signed(b)<0 else 0)
    elif op=="signextend":
        if a>=32: out=b
        else:
            sign=1<<(8*a+7); lowmask=(sign<<1)-1
            out=(b| (MASK^lowmask)) if b&sign else (b&lowmask)
    elif op=="addmod": out=(a+b)%args[2] if args[2] else 0
    elif op=="mulmod": out=(a*b)%args[2] if args[2] else 0
    else: raise ValueError("unhandled opcode")
    return str(out&MASK)

def inputs_from_sources():
    expected=json.loads(census.MANIFEST.read_text())
    if census.census(census.ROOT)!=expected["files"]: raise ValueError("frozen input differs")
    return {"schema":1,"files":{path:[{"name":r["name"],"op":r["op"],"args":r["args"]} for r in codec.extract(path,(census.ROOT/path).read_bytes())] for path in census.PATHS}}

def generate(data):
    if type(data) is not dict or set(data)!={"schema","files"} or type(data["schema"]) is not int or data["schema"]!=1 or type(data["files"]) is not dict or list(data["files"])!=census.PATHS: raise ValueError("file inventory or schema")
    output={}
    for path, rows in data["files"].items():
        if type(rows) is not list or not rows: raise ValueError("rows schema")
        calculated=[]
        for row in rows:
            if type(row) is not dict or set(row)!={"name","op","args"} or type(row["name"]) is not str or type(row["op"]) is not str or type(row["args"]) is not list: raise ValueError("row schema")
            calculated.append({**row,"result":oracle(row["op"],row["args"])})
        output[path]=codec.render(path,calculated)
    return output

def main():
    p=argparse.ArgumentParser(); p.add_argument("mode",choices=("extract","check","emit")); p.add_argument("data",type=Path); p.add_argument("--output",type=Path); a=p.parse_args()
    if (a.mode=="emit") != (a.output is not None): p.error("output required only for emit")
    if a.mode=="extract":
        dest=a.data.resolve()
        if dest.exists() or dest.is_relative_to(census.ROOT): raise ValueError("new external input file required")
        dest.write_text(json.dumps(inputs_from_sources(),separators=(",", ":"))+"\n"); return
    data=json.loads(a.data.read_text()); outputs=generate(data)
    expected=json.loads(census.MANIFEST.read_text())
    if census.census(census.ROOT)!=expected["files"]: raise ValueError("frozen source differs")
    for path in census.PATHS:
        if outputs[path]!=(census.ROOT/path).read_bytes(): raise ValueError(f"{path}: generated output differs")
    if a.mode=="emit":
        dest=a.output.resolve()
        if dest.exists() or dest.is_relative_to(census.ROOT): raise ValueError("new external output required")
        dest.mkdir(parents=True)
        for path,content in outputs.items():
            target=dest/path; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(content)
    print("PASS: integer oracle generated 6903 declarations matching all nine frozen modules")

if __name__=="__main__": main()
