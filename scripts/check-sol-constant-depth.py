#!/usr/bin/env python3
"""Scope-complete acceptance for SOL-CB (G13 constant depth).

Reads tests/sol-constant-depth/manifest.json and checks, without Lean:
- every listed module exists, is imported by the generated `Solidity.lean`
  root, and has a row in the module-map fragment;
- the same pin block closes the inline-pin module (so `lake build` checks it);
- every theorem declared in `Solidity/Frontend/ConstantDepth/**` has exactly
  one `#guard_msgs` pin in tests/sol-constant-depth/Axioms.lean, recording
  only standard axioms, and the pin file pins nothing else;
- every headline theorem and every control of each family is declared;
- no forbidden token occurs in the lane's Lean sources (comments included);
- the read-only inputs are byte-identical to their recorded sha256 pins.
Lean checks the pins themselves (the MCP diagnostics of the pin file, or
`lake env lean tests/sol-constant-depth/Axioms.lean`).
Exit 0 = accepted, 1 = a check failed.
"""
import hashlib, json, pathlib, re, sys

root = pathlib.Path(__file__).resolve().parents[1]
man = json.loads((root / "tests/sol-constant-depth/manifest.json").read_text())
fail = []
ns = "Solidity.Frontend.ConstantDepth"
lane = root / "Solidity/Frontend/ConstantDepth"

roots = (root / "Solidity.lean").read_text().splitlines()
frag = (root / man["module_map_fragment"]).read_text()
base_map = "".join(f.read_text() for f in sorted((root / "docs/module-map").glob("*.md")))
for m in man["modules"]:
    p = root / (m.replace(".", "/") + ".lean")
    if not p.is_file(): fail.append(f"missing module {m}")
    if f"import {m}" not in roots: fail.append(f"not registered in Solidity.lean: {m}")
    row = "`" + m.removeprefix("Solidity.").replace(".", "/") + ".lean`"
    if m in man["new_modules"] and row not in frag: fail.append(f"no module-map fragment row: {row}")
    if row not in base_map: fail.append(f"no row in docs/module-map/*.md: {row}")

decls = {}
for p in sorted(lane.glob("*.lean")):
    text = p.read_text()
    for tok in man["forbidden"]:
        pat = (r"^\s*(private\s+)?axiom\s" if tok.strip() == "axiom" else r"\b" + re.escape(tok.strip()) + r"\b")
        if re.search(pat, text, re.M):
            fail.append(f"forbidden token {tok.strip()!r} in {p.relative_to(root)}")
    sub = "Controls." if p.stem == "Controls" else ""
    for n in re.findall(r"^(?:private )?theorem (\S+)", text, re.M):
        decls[f"{ns}.{sub}{n}"] = p.stem

pins = (root / man["axiom_pins"]).read_text()
pinned = re.findall(r"/-- info: '([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\]) -/\n#guard_msgs in #print axioms (\S+)", pins)
seen = {}
for name, _, axioms, target in pinned:
    if name != target: fail.append(f"pin message {name} != target {target}")
    seen[name] = seen.get(name, 0) + 1
    bad = {a.strip() for a in axioms.split(",") if a.strip()} - {"propext", "Classical.choice", "Quot.sound"}
    if bad: fail.append(f"non-standard axioms for {name}: {sorted(bad)}")
if pins.count("#print axioms") != len(pinned): fail.append("unparsed or unguarded #print axioms in the pin file")
for d in decls:
    if seen.get(d, 0) != 1: fail.append(f"theorem {d} pinned {seen.get(d, 0)} times")
for s in seen:
    if s not in decls: fail.append(f"pin for unknown theorem {s}")

inline = (root / man["inline_pins"]).read_text()
if pins.split("-/\n\n", 1)[1] not in inline: fail.append(f"inline pins in {man['inline_pins']} differ from {man['axiom_pins']}")

short = {d.split(".")[-1] for d in decls}
for h in man["headline"]:
    if h not in short: fail.append(f"missing headline theorem {h}")
for fam, names in man["control_families"].items():
    for n in names:
        if f"{ns}.Controls.{n}" not in decls: fail.append(f"missing control {n} ({fam})")

for path, digest in man["read_only_inputs"].items():
    got = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if got != digest: fail.append(f"read-only input changed: {path} (re-pin after review)")

print(f"modules {len(man['modules'])}, theorems {len(decls)}, pins {len(pinned)}, "
      f"control families {len(man['control_families'])}, inputs {len(man['read_only_inputs'])}")
for f in fail: print("FAIL", f)
print("ACCEPT" if not fail else f"REJECT ({len(fail)})")
sys.exit(1 if fail else 0)
