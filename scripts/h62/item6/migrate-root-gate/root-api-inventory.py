#!/usr/bin/env python3
"""Guard against treating the 25-file root source census as exported API acceptance.

Regression guarded: unchanged source bytes and lexical declaration headers cannot
certify compiler-generated names, visibility or axiom fidelity across toolchains.
No Lean, build, baseline restart, missing-export regeneration or source edits.
"""
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def scope():
    tree = ast.parse((Path(__file__).with_name("census.py")).read_text())
    owned = [n.value.func.value.value.split() for n in tree.body
             if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "OWNED" for t in n.targets)]
    if len(owned) != 1 or len(owned[0]) != 25 or len(set(owned[0])) != 25:
        raise ValueError("require exact original25 unique root paths")
    return owned[0]


def validate_coverage(expected, rows):
    paths = [r["path"] for r in rows]
    if len(paths) != len(set(paths)) or set(paths) != set(expected):
        raise ValueError("missing, duplicate or out-of-scope root input")


def lexical(raw, scanner):
    text = raw.decode()
    try:
        captured = scanner.headers(text)
        return {"headers": captured, "header_capture_complete_for_supported_grammar": True,
                "limitation": "Lexical subset only; not elaborated signatures or generated/public exports"}
    except ValueError as error:
        return {"headers": [], "header_capture_complete_for_supported_grammar": False,
                "error": str(error), "limitation": "Unsupported source retained by hash; no zero-declaration or API-coverage claim"}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: root-api-inventory.py NEW_OUTPUT.json")
    output = Path(sys.argv[1])
    if output.exists():
        raise ValueError("preserve prior evidence: output must be new")
    spec = importlib.util.spec_from_file_location("root_static_headers", Path(__file__).with_name("public-api-inventory.py"))
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=ROOT)
    head = git("rev-parse", "HEAD").decode().strip()
    rows = []
    for path in scope():
        old, new = git("show", BASE+":"+path), git("show", head+":"+path)
        if (ROOT/path).read_bytes() != new:
            raise ValueError("uncommitted root input: "+path)
        row = {"path": path, "base_sha256": digest(old), "source_sha256": digest(new),
               "whole_file_unchanged": old == new, "bytes": len(new),
               "kind": "Lean source" if path.endswith(".lean") else "configuration",
               "complete_exported_API": False, "axiom_fidelity_accepted": False,
               "required_shims": "unknown until exact old/new exported name/type/visibility metadata available",
               "installed_root_authored_shims": []}
        if path.endswith(".lean"):
            before, after = lexical(old, scanner), lexical(new, scanner)
            row.update(old_authored=before, new_authored=after)
            if before["header_capture_complete_for_supported_grammar"] and after["header_capture_complete_for_supported_grammar"]:
                row["lexical_header_delta"] = scanner.header_changes(before["headers"], after["headers"])
            row["generated_family_source_headers"] = [h for h in after["headers"] if re.search(r"\b(inductive|structure|class)\b", h)]
            row["imports"] = [line for line in new.decode().splitlines() if re.match(r"^import\s", line)]
            code_lines = scanner.code_only(new.decode()).splitlines()
            raw_lines = new.decode().splitlines()
            row["non_header_command_sites"] = [{"line": i+1, "source_line": raw_lines[i]}
                for i, line in enumerate(code_lines)
                if re.match(r"^\s*(?:syntax|elab|macro|initialize|builtin_initialize|declare_syntax_cat|attribute|export|axiom|constant|deriving|#\w+)\b", line)]
            row["non_header_boundary"] = "Command sites are lexical hints only, including axiom guards and syntax/elaborator declarations; zero captured headers is not zero exports. Imported/reexported APIs and registered syntax/attributes require separate compiler metadata."

        rows.append(row)
    validate_coverage(scope(), rows)
    result = {"schema_version": 1, "base": BASE, "source_head": head,
              "generator_sha256": digest(Path(__file__).read_bytes()),
              "scanner_sha256": digest(Path(scanner.__file__).read_bytes()),
              "scope_source": "scripts/h62/item6/migrate-root-gate/census.py:OWNED",
              "files": rows, "root_file_count": len(rows),
              "complete_root_input_index": True, "complete_public_generated_API_inventory": False,
              "API_axiom_acceptance": False, "Lean_runs": 0, "new_shims": [],
              "boundary": "All25 original root/global input bytes indexed; authored lexical subset only. Unchanged bytes do not certify generated APIs, semantic equivalence or axiom sets. Macro/elaborator-created declarations and accessibility require compiler exports; no generated/debug/proof exclusion inferred. H86 missing raw bytes not recovered or accepted. Existing timing/trust holds preserved."}
    with output.open("x") as f:
        json.dump(result, f, indent=2, ensure_ascii=False); f.write("\n")
    print(json.dumps({"source_head": head, "files": len(rows), "changed": [r["path"] for r in rows if not r["whole_file_unchanged"]], "generated_API_complete": False}))


if __name__ == "__main__":
    main()
