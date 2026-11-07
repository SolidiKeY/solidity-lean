"""Guard regression: name-candidate origins are not exact linker attribution.

Replay only the unchanged producer final link with diagnostic map/trace flags.
A byte-identical ELF is required before attributing the original binary using
that replay map. No producer edit, Lean environment, verifier verdict or
semantic absence certification is involved.
"""
import hashlib
import json
import pathlib
import subprocess
import sys
import bisect
import re

if not __debug__:
    raise RuntimeError("Attribution requires ordinary Python checks")
def sha(path):
    with pathlib.Path(path).open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def load_map(path):
    lines = pathlib.Path(path).read_text().splitlines()
    assert lines[0].split() == ["VMA", "LMA", "Size", "Align", "Out", "In", "Symbol"]
    regions = []
    section = None
    for line in lines[1:]:
        match = re.match(r"^\s*([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+(\d+)\s+(\S.*)$", line)
        if not match:
            continue
        column = match.start(5)
        if column == 49:
            section = match[5]
        elif column == 57 and int(match[3], 16) > 0 and section in {".text", ".init", ".fini", "__lcxx_override", ".plt"}:
            start = int(match[1], 16)
            regions.append({"start": start, "end": start+int(match[3], 16), "input": match[5], "section": section})
    regions.sort(key=lambda row: row["start"])
    assert regions and all(a["end"] <= b["start"] for a,b in zip(regions, regions[1:])), "Overlapping map input sections"
    return regions

def attribute(rows, regions):
    starts = [r["start"] for r in regions]
    result = []
    for row in rows:
        address = int(row["address"], 16)
        index = bisect.bisect_right(starts, address)-1
        assert index >= 0 and address < regions[index]["end"], "Unattributed symbol: "+row["name"]
        size = int(row["size"], 16) if row["size"] else 0
        assert not size or address+size <= regions[index]["end"], "Symbol extent crosses input section"
        result.append(dict(row, replayInputSection=regions[index], extentKnown=size>0))
    return result

def main():
    repo, prefix, native, census, out = [pathlib.Path(p).resolve() for p in sys.argv[1:]]
    out.mkdir(parents=True, exist_ok=False)

    manifest = json.loads((native/"build.json").read_text())
    summary = json.loads((census/"summary.json").read_text())
    receipt = json.loads((repo/"tests/directruntime-20261104/memory-references/runtime-census-receipt.json").read_text())
    assert sha(census/"summary.json") == receipt["summary"]["sha256"]
    for filename in ["selected-modules.jsonl", "retained-link-input-fingerprints.jsonl", "build-input-fingerprints.jsonl", "defined-symbols.jsonl"]:
        expected = next(f["sha256"] for f in summary["files"] if f["path"] == filename)
        assert sha(census/filename) == expected
    baseline_inputs = {r["path"]:r["sha256"] for r in [json.loads(line) for line in (census/"build-input-fingerprints.jsonl").read_text().splitlines()]}
    assert manifest["buildInputs"] == baseline_inputs, "Incomplete or changed producer input domain"
    supplementary = {str(f):sha(f) for f in (prefix/"lib").rglob("*.o")}
    assert manifest["executable"] == summary["binarySha256"] == sha(native/"direct-check")
    for path, expected in manifest["buildInputs"].items():
        assert sha(path) == expected, path
    for row in [json.loads(line) for line in (census/"retained-link-input-fingerprints.jsonl").read_text().splitlines()]:
        assert sha(row["path"]) == row["sha256"]
    rows = [json.loads(line) for line in (census/"selected-modules.jsonl").read_text().splitlines()]
    assert len(rows) == manifest["closure"]["modules"] == 206
    for row in rows:
        assert sha(row["object"]) == row["objectSha256"]
    command = [str(prefix/"bin/leanc"), "-O2", "-ffunction-sections", "-fdata-sections", "-I"+str(prefix/"include"), "-DSOLIDITY_DIRECT_NATIVE", str(native/"bridge.o"), str(native/"initialize.c"), *[row["object"] for row in rows], "-Wl,--gc-sections", "-Wl,-Map="+str(out/"link.map"), "-Wl,--cref", "-Wl,--trace", "-v", "-save-temps=obj", "-o", str(out/"direct-check")]
    (out/"command.json").write_text(json.dumps(command, indent=2)+"\n")
    with (out/"driver.stdout").open("w") as stdout, (out/"driver.stderr").open("w") as stderr:
        run = subprocess.run(command, cwd=out, stdout=stdout, stderr=stderr)
    assert run.returncode == 0, run.returncode
    identical = sha(out/"direct-check") == manifest["executable"]
    result = {"originalSha256": manifest["executable"], "replaySha256": sha(out/"direct-check"), "byteIdentical": identical, "mapSha256": sha(out/"link.map"), "boundary": "Replay map applies to original only if entire ELF matches; provenance/attribution is not semantic absence certification."}
    (out/"identity.json").write_text(json.dumps(result, indent=2)+"\n")
    assert identical, "Diagnostic replay differs from original ELF; no exact attribution claimed"
    regions = load_map(out/"link.map")
    text_rows = [json.loads(line) for line in (census/"defined-symbols.jsonl").read_text().splitlines()]
    text_rows = [r for r in text_rows if r["type"] in "TtWwIi"]
    attributed = attribute(text_rows, regions)
    assert len(attributed) == summary["textELFSymbols"] == 8405
    (out/"text-attribution.jsonl").write_text("".join(json.dumps(r, sort_keys=True)+"\n" for r in attributed))
    # Attribute the selected section entries; zero-sized init/fini symbols also
    # retain all section contributions rather than pretending they end in crti.o.
    fingerprints = {}
    for region in regions:
        identifier = region["input"].rsplit(":(", 1)[0]
        if identifier in fingerprints:
            continue
        if identifier == "<internal>":
            fingerprints[identifier] = {"kind": "linker-synthesized", "linkerSha256": sha(prefix/"bin/ld.lld")}
        elif ".a(" in identifier and identifier.endswith(")"):
            archive, member = identifier.rsplit("(", 1)
            member = member[:-1]
            listing = subprocess.check_output(["ar", "t", archive], text=True).splitlines()
            assert listing.count(member) == 1, "Ambiguous archive member: "+identifier
            data = subprocess.check_output(["ar", "p", archive, member])
            fingerprints[identifier] = {"kind": "archive-member", "archive": archive, "archiveSha256": sha(archive), "member": member, "memberSha256": hashlib.sha256(data).hexdigest()}
        else:
            fingerprints[identifier] = {"kind": "object", "path": identifier, "sha256": sha(identifier)}
    (out/"input-fingerprints.json").write_text(json.dumps(fingerprints, indent=2)+"\n")
    roles = {"_start": "ELF startup: prepares ABI arguments and transfers main to __libc_start_main", "__do_init": "Guarded exception-frame registration through weak runtime hook", "__do_fini": "Guarded DSO finalization and exception-frame deregistration", "_init": "Platform init prologue and optional weak profiling hook; crtn supplies return tail", "_fini": "Platform fini prologue/return split across crti and crtn", "compact_initialize": "Generated dispatcher to206 producer-rewritten module initializers; returns IO success/error"}
    classifications = []
    for name, role in roles.items():
        asm = subprocess.check_output(["objdump", "-d", "--disassemble="+name, str(native/"direct-check")], text=True)
        (out/(name+".asm")).write_text(asm)
        matching = [r for r in attributed if r["name"] == name]
        assert len(matching) == 1
        region = matching[0]["replayInputSection"]
        contributions = [r for r in regions if r["section"] == region["section"]] if name in {"_init", "_fini"} else [region]
        classifications.append({"name": name, "role": role, "entry": matching[0], "sectionContributions": contributions, "disassemblySha256": sha(out/(name+".asm")), "boundary": "Body-level platform/data initialization classification, not whole-program semantic absence."})
    initializer = (native/"initialize.c").read_text()
    expected_init = ["initialize_"+r["module"].replace(".", "_") for r in rows]
    source_calls = re.findall(r"res=(initialize_\w+)\(1,lean_io_mk_world\(\)\);", initializer)
    assert source_calls == expected_init
    asm = (out/"compact_initialize.asm").read_text()
    actual_init = re.findall(r"\bcall\s+[^<\n]*<(initialize_[^>]+)>", asm)
    assert actual_init == expected_init
    (out/"six-classifications.json").write_text(json.dumps(classifications, indent=2)+"\n")
    for path, expected in manifest["buildInputs"].items(): assert sha(path) == expected
    for path, expected in supplementary.items(): assert sha(path) == expected
    result.update({"attributedTextRows": len(attributed), "unattributedTextRows": 0, "textInputSections": len(regions), "inputFingerprints": len(fingerprints), "classifiedNames": list(roles), "initializerCallsVerified": len(actual_init), "supplementaryObjectFingerprints": supplementary, "limitations": ["Exact input-section attribution of a byte-identical replay, not reconstruction of the historical link process.", "Zero-size init/fini function extents are not invented; full section contributions are retained.", "No whole-program semantic absence, source adequacy, browser acceptance or four-diamond certification."]})
    (out/"replay.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "supplementaryObjectFingerprints"}))

if __name__ == "__main__":
    main()
