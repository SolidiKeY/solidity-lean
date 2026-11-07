#!/usr/bin/env python3
"""Render explicit full-telescope witness candidates from the frozen kernel census.

No proof credit is awarded by this generator. Lean must check every module and
the independent exact-type/axiom census must match all 311 original declarations.
"""
import argparse
import json
from pathlib import Path
import re

SCALAR_PLANS = json.loads(r'''{"guarded_range_correct":["[pushWord 0]","[.op .ADD]","u0","u0","0","[99]","by decide +kernel","by decide +kernel"],"guarded_int_range_correct":["[pushWord 0]","[.op .ADD]","i0","i0","0","[99]","by decide +kernel","by decide +kernel"],"uint_div_body":["u0","u1","by decide +kernel","[99]"],"uint_mod_body":["u0","u1","by decide +kernel","[99]"],"int_div_body":["i0","i1","by decide +kernel","by decide +kernel","[99]"],"int_mod_body":["i0","i1","by decide +kernel","[99]"],"int_div_exception":["minimumInt","ineg1","rfl","rfl"],"zeroTest_correct":["⟨0, by decide⟩","[0,99]","0","rfl"],"guarded_zero":["⟨0, by decide⟩","[0,99]","0","[]","[]","rfl"],"guardedNext_zero":["⟨0, by decide⟩","[0,99]","0","[]","fun st => some (.ok st)","rfl"],"signedBitwise_read":["fun _ _ => 0","by intro _ _ _ _; exact (by decide : (0 : Nat) < 2^255)","0","0","by decide +kernel","by decide +kernel","0","rfl"],"uintBitwise_encoded":["fun _ _ => 0","u0","u0","0","rfl","[99]"],"duplicate_length":["0","[99]","[99,99]","rfl"],"exchange_length":["0","0","[99]","[0]","99","rfl"],"swap_length":["0","[7,3,99]","[3,7,99]","rfl"],"applyUnary_length":["id","[99]","[99]","rfl"],"applyBinary_length":["fun a _ => a","[7,3]","[7]","rfl"],"applyTernary_length":["fun a _ _ => a","[7,3,2]","[7]","rfl"],"numericStep_height":[".ISZERO","[0]","[1]","rfl"],"step_height":[".op .POP","[99]","[]","rfl"],"BinaryInvocation.decode_bytes":[".and",".bool","rfl","booleanAnd","true","true","[99]","⟨by decide +kernel⟩"],"BinaryInvocation.correct":[".and",".bool","rfl","booleanAnd","true","true","[99]","⟨by decide +kernel⟩"],"BinaryInvocation.prefix_safe":[".and",".bool","rfl","booleanAnd","true","true","[99]","⟨by decide +kernel⟩","[]","booleanAnd.code","rfl","[1,1,99]","rfl"],"CheckedInvocation.correct":[".add",".uint","rfl","checkedUintAdd","u255","u1","[99]","checkedAdditionWitness"],"CheckedInvocation.testPrefix_safe":[".add",".uint","rfl","checkedUintAdd","u255","u1","[99]","checkedAdditionWitness","[]","checkedUintAdd.test","rfl","[255,1,99]","rfl"],"ClosedInvocation.prefix_safe":["default","[]",".bool",".simple (.bool true)","boolLiteral true","[99]","⟨by decide +kernel⟩","[]","(boolLiteral (C := default) (Γ := []) true).code","rfl","[99]","rfl"],"SignedPowerInvocation.correct":["⟨-2, by decide⟩","u3","[99]","signedPowerWitness"],"bytesNarrow_intrinsic":["⟨1, by decide⟩","⟨0, by decide⟩","by decide +kernel","u0","[99]"],"run_append":["[.op .POP]","[.op .POP]","[7,3,99]"],"run_comp":["[.op .POP]","[.op .POP]","[7,3,99]","[3,99]","[99]","rfl","rfl"],"step_pushByte":["7","[99]"],"applyUnary_frame":["id","[7]","[7]","rfl","[99]"],"applyBinary_frame":["fun a _ => a","[7,3]","[7]","rfl","[99]"],"applyTernary_frame":["fun a _ _ => a","[7,3,2]","[7]","rfl","[99]"],"duplicate_frame":["0","[7]","[7,7]","rfl","[99]"],"exchange_frame":["3","0","[7]","[3]","7","rfl","[99]"],"swap_frame":["0","[7,3]","[3,7]","rfl","[99]"],"pop_frame":["[7]","[]","rfl","[99]"],"numericStep_frame":[".ISZERO","[0]","[1]","rfl","[99]"],"step_frame":[".op .POP","[7]","[]","rfl","[99]"],"run_frame":["[.op .POP]","[7]","[]","rfl","[99]"],"step_pushWord":["7","[99]"],"encode_pushWord":["7"]}''')

S = "Solidity.Backend.Scalar."
E = "Solidity.Backend.Environment."
PROOF = "by first | rfl | decide +kernel"

def choose(row, binder):
    head, ty, name = binder["type_head"], binder["type"], binder["name"]
    env = row["name"].startswith(E)
    short = row["name"].removeprefix(E if env else S)
    has_path = any(b["type_head"] == "Solidity.MPath" for b in row["binders"])
    if binder["instance_implicit"]: return "inferInstance"
    if head == E+"Represents": return "representedProof"
    if head == E+"Stable": return "stableSample"
    if head == E+"HashInput": return "heapHashInput" if has_path else "emptyHashInput"
    if head == E+"NamespaceInput": return "emptyNamespaceInput"
    if binder["is_proposition"]: return PROOF
    if head == "Solidity.Contract": return "default"
    if head == "Solidity.Ctx": return "bytesΓ" if has_path else "[]"
    if head == "Solidity.PrimTy": return ".uint" if short == "typed_literal_intrinsic" else ".bool"
    if head == "Solidity.PrimTy.Denote":
        if ".uint.Denote" in ty: return "u0"
        if ".int.Denote" in ty: return "i0"
        return "true"
    if head == "Solidity.State":
        if has_path: return "unsetBytesState" if "failure" in short else "bytesState"
        if any(b["type_head"] == E+"Represents" for b in row["binders"]): return "representedState"
        if "[Solidity.LTy.val Solidity.PrimTy.uint]" in ty: return "localState"
        return "state0"
    if head == "Solidity.Val":
        return ".simple (.bool false)" if "PrimTy.bool" in ty else ".simple (.lit 0 (by decide))"
    if head == "Solidity.RefTy": return "bytesR"
    if head == "Solidity.MPath": return "bytesPath"
    if head == "Solidity.HRef": return "bytesRef"
    if head == "Solidity.THalt": return ".revert"
    if head == "Solidity.TStep": return "failedStep" if short == "source_sequence_failure" else "identityStep"
    if head == "Solidity.Out": return "initialOut"
    if head == S+"BinaryCertificate": return "booleanAnd"
    if head == S+"UnaryCertificate": return "booleanNot"
    if head == "Solidity.BinOp": return ".and"
    if head == "Solidity.UnOp": return ".not"
    if head == "Solidity.HashKind": return ".keccak"
    if head == "Solidity.EnvKey": return ".msgSender"
    if head == "Solidity.Backend.Op": return ".GAS" if env else ".ISZERO"
    if head == "Solidity.Backend.Instr": return ".push ⟨0, by decide⟩ #v[]"
    if head == "Solidity.Backend.Program": return "[]"
    if head == S+"Stack": return "[99]"
    if head == S+"Word": return "0"
    if head == E+"Word": return "u0"
    if head == E+"Frame": return E+"sample"
    if head == E+"Slice": return "targetSlice"
    if head == E+"Memory": return "emptyMemory"
    if head == E+"Address": return E+"account u1" if short == "ledger_other" and name == "changed" else E+"account u0"
    if head == E+"W256" or head == "Fin": return "⟨0, by decide⟩"
    if head == "Solidity.ContractWorld.World": return "sampleWorld"
    if head == "Solidity.SourceFunction": return "resolvedDecl"
    if head == "Nat" and short == "writeBytes_frame" and name == "i": return "2"
    if head in ("Nat","Int"): return "0"
    if head == "Bool": return "false"
    if head == "UInt8": return "7"
    if head == "String": return '"AB"'
    if head == "List":
        if ty == "List "+E+"Word": return "[u99]"
        if ty == "List UInt8":
            return "[1]" if short == "writeBytes_at" else ("[]" if short == "namespace_source" else "[1,2]")
        if ty == "List (Fin 255)": return "[⟨0, by decide⟩]"
        return "[]"
    if head == "[anonymous]":
        if ty == "Type": return "Unit"
        if ty == "Prop": return "True"
        if ty.endswith("→ Solidity.Contract"): return "fun _ => default"
    raise ValueError(f"no explicit choice for {row['name']} binder {name}: {ty}")

def render(repo, source, kernel):
    names={r["name"]:r for r in source["theorems"] if r["visibility"] == "public"}
    rows={r["name"]:r for r in kernel}
    source_public=[r for r in source["theorems"] if r["visibility"] == "public"]
    if len(names) != len(source_public) or len(rows) != len(kernel): raise ValueError("duplicate census input names")
    if set(rows) != set(names): raise ValueError("kernel/source census sets differ")
    groups={}
    links={}
    for name, row in rows.items():
        env=name.startswith(E)
        short=name.removeprefix(E if env else S)
        args = SCALAR_PLANS.get(short) if not env else None
        if args is None: args=[choose(row,b) for b in row["binders"]]
        if len(args) != row["binder_count"]: raise ValueError(f"arity mismatch: {name}: {len(args)} != {row['binder_count']}")
        stem=Path(names[name]["path"]).stem
        prefix=("Environment" if env else "Scalar")+stem
        filename="SliceWitnesses" if not env and stem=="Slice" else prefix+"Witnesses"
        namespace="Solidity.Backend.Scalar.H62Audit"+("" if filename=="SliceWitnesses" else "."+prefix)
        local="witness_"+short.replace(".","_")
        links[name]=namespace+"."+local
        body=f"-- AUDIT-WITNESS: {name}\ntheorem {local} : jointType% {name} :=\n  jointProof% {name} ["
        body+=("\n    "+",\n    ".join("("+arg+")" for arg in args)+"\n  " if args else "")+"]\n"
        groups.setdefault((filename,namespace,names[name]["path"]),[]).append(body)
    targets=[]
    for (filename, namespace, path), bodies in sorted(groups.items()):
        module=path.removesuffix(".lean").replace("/",".")
        text="import tests.h62.item2.«audit-g25-scalar-lowering».WitnessCommand\nimport tests.h62.item2.«audit-g25-scalar-lowering».Fixtures\nimport "+module+"\n\n"
        text+="/-! Generated explicit candidate choices for the full frozen theorem telescopes.\nKernel checking and final exact-type/axiom census are required for proof credit. -/\n"
        text+="namespace "+namespace+"\nopen Solidity\nopen Solidity.Backend\nopen Solidity.Backend.Scalar\nopen Solidity.Backend.Environment\nopen Solidity.Backend.Scalar.H62Audit\nopen Solidity.Backend.Scalar.H62Audit.Fixtures\n\n"
        text+="\n".join(bodies)+"\nend "+namespace+"\n"
        target=repo/"tests/h62/item2/audit-g25-scalar-lowering"/(filename+".lean")
        target.write_text(text)
        targets.append("tests.h62.item2.«audit-g25-scalar-lowering»."+filename)
    verification = "\n#audit_verify \"/workspace/h62-audit-g25-artifacts/evidence/witness-verification-v424.json\" [\n  "
    verification += ",\n  ".join(rows)+"\n] [\n  "+",\n  ".join(links[name] for name in rows)+"\n]\n"
    (repo/"tests/h62/item2/audit-g25-scalar-lowering/AllWitnesses.lean").write_text("\n".join("import "+module for module in targets)+"\n"+verification)
    return len(rows),len(targets)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo",type=Path,default=Path.cwd())
    p.add_argument("--source",type=Path,required=True)
    p.add_argument("--kernel",type=Path,required=True)
    a=p.parse_args()
    count,modules=render(a.repo,json.loads(a.source.read_text()),json.loads(a.kernel.read_text()))
    print(f"{count} explicit witness candidates in {modules} modules; zero automatic proof credit")
if __name__=="__main__": main()
