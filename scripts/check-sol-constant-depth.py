#!/usr/bin/env python3
"""Scope-complete acceptance for the constant-depth lane: SOL-CB (G13 constant
depth) and its G35-INT-RAW-1105 refill (RawInt).

Reads tests/sol-constant-depth/manifest.json and checks, without Lean, for each
area (`Solidity/Frontend/ConstantDepth`, `Solidity/Backend/CalldataPackets/RawInt`):
- every listed module exists and is imported by the generated `Solidity.lean`;
  ConstantDepth's new modules have a row in the lane's module-map fragment, and
  every module has a row somewhere under docs/module-map/;
- every non-private theorem (attributes and `protected` allowed) has exactly
  one `#guard_msgs` pin in the area's pin file, with standard axioms only; the
  pin file pins nothing else;
- the pin file's block is exactly the block that closes the inline-pin module
  (so `lake build` checks the same pins);
- every headline theorem and every ConstantDepth control-family member exists;
- no `sorry`/`admit`/`native_decide`/`maxHeartbeats`/`unsafe` token and no
  `axiom` declaration in the area's Lean sources;
- the read-only inputs are byte-identical to their recorded sha256 pins.
Lean checks the pins themselves (MCP diagnostics of the pin files, or the build
of the inline-pin modules). Exit 0 = accepted, 1 = a check failed.
"""
import hashlib, json, pathlib, re, sys

root = pathlib.Path(__file__).resolve().parents[1]
man = json.loads((root / "tests/sol-constant-depth/manifest.json").read_text())
fail = []
roots = (root / "Solidity.lean").read_text().splitlines()
maps = "".join(f.read_text() for f in sorted((root / "docs/module-map").glob("*.md")))
frag = (root / man["module_map_fragment"]).read_text()
THM = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable)\s+)*theorem\s+(\S+)", re.M)
AXIOM = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|unsafe)\s+)*axiom\s", re.M)
PIN = re.compile(r"/-- info: '([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\]) -/\n"
                 r"#guard_msgs in #print axioms (\S+)")
MARK = "/-! Exact axiom pins (mirrored in"

def area(name, ns, directory, pin_file, inline_file, modules, headline, sub_of):
    for m in modules:
        if not (root / (m.replace(".", "/") + ".lean")).is_file(): fail.append(f"{name}: missing module {m}")
        if f"import {m}" not in roots: fail.append(f"{name}: not registered in Solidity.lean: {m}")
        row = "`" + m.removeprefix("Solidity.").replace(".", "/") + ".lean`"
        if row not in maps: fail.append(f"{name}: no module-map row {row}")
    decls = {}
    for p in sorted((root / directory).glob("*.lean")):
        text = p.read_text()
        for tok in ["sorry", "admit", "native_decide", "maxHeartbeats", "unsafe"]:
            if re.search(r"\b" + tok + r"\b", text): fail.append(f"{name}: forbidden token {tok!r} in {p.name}")
        if AXIOM.search(text): fail.append(f"{name}: axiom declaration in {p.name}")
        for mods, n in THM.findall(text):
            if "private" not in mods: decls[f"{ns}.{sub_of(p.stem)}{n}"] = p.stem
    pins = (root / pin_file).read_text()
    pinned = PIN.findall(pins)
    seen = {}
    for full, _, axioms, target in pinned:
        if full != target: fail.append(f"{name}: pin message {full} != target {target}")
        seen[full] = seen.get(full, 0) + 1
        bad = {a.strip() for a in axioms.split(",") if a.strip()} - {"propext", "Classical.choice", "Quot.sound"}
        if bad: fail.append(f"{name}: non-standard axioms for {full}: {sorted(bad)}")
    if pins.count("#print axioms") != len(pinned): fail.append(f"{name}: unparsed or unguarded #print axioms in {pin_file}")
    for d in decls:
        if seen.get(d, 0) != 1: fail.append(f"{name}: theorem {d} pinned {seen.get(d, 0)} times")
    for s in seen:
        if s not in decls: fail.append(f"{name}: pin for unknown theorem {s}")
    block = pins.split("-/\n\n", 1)[1]
    inline = (root / inline_file).read_text()
    if MARK not in inline or inline.split(MARK, 1)[1].split("-/\n\n", 1)[1] != block:
        fail.append(f"{name}: the pin block closing {inline_file} differs from {pin_file}")
    short = {d.split(".")[-1] for d in decls}
    for h in headline:
        if h not in short: fail.append(f"{name}: missing headline theorem {h}")
    print(f"{name}: modules {len(modules)}, theorems {len(decls)}, pins {len(pinned)}")
    return decls

cd = "Solidity.Frontend.ConstantDepth"
decls = area("ConstantDepth", cd, "Solidity/Frontend/ConstantDepth", man["axiom_pins"], man["inline_pins"],
             man["modules"], man["headline"], lambda stem: "Controls." if stem == "Controls" else "")
for m in man["new_modules"]:
    row = "`" + m.removeprefix("Solidity.").replace(".", "/") + ".lean`"
    if row not in frag: fail.append(f"ConstantDepth: no module-map fragment row {row}")
for fam, names in man["control_families"].items():
    for n in names:
        if f"{cd}.Controls.{n}" not in decls: fail.append(f"ConstantDepth: missing control {n} ({fam})")
r = man["rawint"]
area("RawInt", r["namespace"], r["dir"], r["axiom_pins"], r["inline_pins"], r["modules"], r["headline"],
     lambda stem: "Controls." if stem == "Controls" else "")
for path, digest in man["read_only_inputs"].items():
    if hashlib.sha256((root / path).read_bytes()).hexdigest() != digest:
        fail.append(f"read-only input changed: {path} (re-pin after review)")
print(f"control families {len(man['control_families'])}, inputs {len(man['read_only_inputs'])}")
for f in fail: print("FAIL", f)
print("ACCEPT" if not fail else f"REJECT ({len(fail)})")
sys.exit(1 if fail else 0)
