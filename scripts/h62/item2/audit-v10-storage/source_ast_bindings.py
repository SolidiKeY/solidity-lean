#!/usr/bin/env python3
"""Read-only compiler-AST identity intake for actual Source construction.

Regression purpose: do not erase the library storage formal, stringify a
string result as bytes, equate AST IDs with Source positions/code indexes,
or mistake an analysis AST/header for a Source program or runtime artifact.
No parsing, Source admission, body translation or semantics is implemented.
Bulk reports must remain outside the repository.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
DECLARATIONS = {"ContractDefinition", "StructDefinition", "FunctionDefinition", "VariableDeclaration"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()


def reference(node):
    if not isinstance(node, dict):
        return None
    direct = node.get("referencedDeclaration")
    if direct is not None:
        return direct
    return reference(node.get("pathNode"))


def parameter(node):
    return dict(ast_id=node.get("id"), name=node.get("name"),
                type=node.get("typeDescriptions", {}).get("typeString"),
                storage_location=node.get("storageLocation"),
                type_declaration=reference(node.get("typeName")))


def inspect(document):
    header, ast = document.get("header"), document.get("ast")
    if not isinstance(header, dict) or not isinstance(ast, dict) or ast.get("nodeType") != "SourceUnit":
        raise ValueError("header and SourceUnit required")
    if header.get("validationStage") != "analysis":
        raise ValueError("this intake expects analysis-stage fixtures")
    for field in ["compilerFile", "solcVersion", "solkeyCommit", "compilerSha256", "sourceSha256", "source"]:
        if not isinstance(header.get(field), str) or not header[field]:
            raise ValueError("missing recorded provenance: " + field)
    for field, length in [("solkeyCommit", 40), ("compilerSha256", 64), ("sourceSha256", 64)]:
        if len(header[field]) != length or any(c not in "0123456789abcdefABCDEF" for c in header[field]):
            raise ValueError("malformed recorded provenance: " + field)
    if type(header.get("provenanceVersion")) is not int or header["provenanceVersion"] != 1:
        raise ValueError("recorded provenance version1 required")
    if not isinstance(header.get("acceptedPragmas"), list):
        raise ValueError("recorded pragma list required")
    settings = header.get("settings", {})
    if type(settings.get("viaIR")) is not bool:
        raise ValueError("explicit Boolean pipeline required")
    counts, ids = Counter(), {}
    declarations, functions, calls, using = [], [], [], []

    def walk(value, path="", owner=None, function=None, structure=None):
        if isinstance(value, list):
            for index, item in enumerate(value):
                walk(item, path + "/" + str(index), owner, function, structure)
            return
        if not isinstance(value, dict):
            return
        kind = value.get("nodeType")
        if kind:
            counts[kind] += 1
        if kind and "id" in value:
            ident = value["id"]
            if type(ident) is not int or ident < 0 or ident in ids:
                raise ValueError("invalid or duplicate AST node ID")
            ids[ident] = path
        if kind == "ContractDefinition":
            owner = value.get("name")
            function, structure = None, None
        elif kind == "FunctionDefinition":
            function, structure = value.get("name"), None
        elif kind == "StructDefinition":
            structure = value.get("name")
        if kind in DECLARATIONS:
            if "id" not in value:
                raise ValueError("declaration ID required")
            declarations.append(dict(kind=kind, ast_id=value["id"], path=path,
                name=value.get("name"), owner_contract=owner, owner_function=function,
                owner_struct=structure, ast_scope_id=value.get("scope"),
                canonical_name=value.get("canonicalName"), contract_kind=value.get("contractKind"),
                state_variable=value.get("stateVariable"), **{
                    "type": value.get("typeDescriptions", {}).get("typeString"),
                    "storage_location": value.get("storageLocation"),
                    "type_declaration": reference(value.get("typeName")),
                    "node_sha256": digest(canonical(value))}))
        if kind == "FunctionDefinition":
            functions.append(dict(ast_id=value["id"], path=path, owner=owner,
                name=function, function_kind=value.get("kind"), visibility=value.get("visibility"),
                mutability=value.get("stateMutability"),
                parameters=[parameter(x) for x in value.get("parameters", {}).get("parameters", [])],
                returns=[parameter(x) for x in value.get("returnParameters", {}).get("parameters", [])],
                body_ast_id=(value.get("body") or {}).get("id"),
                body_sha256=digest(canonical(value.get("body")))))
        if kind == "FunctionCall":
            expression = value.get("expression") or {}
            receiver = expression.get("expression") or {}
            calls.append(dict(path=path, owner=owner, function=function,
                target_ast_id=reference(expression), member=expression.get("memberName"),
                callee_name=expression.get("name"), receiver_ast_id=reference(receiver),
                receiver_name=receiver.get("name"),
                arguments=[dict(path=path + "/arguments/" + str(i),
                    referenced_declaration=reference(x), type=x.get("typeDescriptions", {}).get("typeString"))
                    for i, x in enumerate(value.get("arguments", []))]))
        if kind == "UsingForDirective":
            using.append(dict(path=path, owner=owner,
                library_ast_id=reference(value.get("libraryName")),
                type_ast_id=reference(value.get("typeName")), global_=value.get("global")))
        for key, item in value.items():
            walk(item, path + "/" + key, owner, function, structure)

    walk(ast)
    return dict(header=header, pipeline="viaIR" if settings["viaIR"] else "legacy",
                canonical_ast_sha256=digest(canonical(ast)), node_kind_counts=dict(sorted(counts.items())),
                indexed_node_count=len(ids), declarations=declarations, functions=functions,
                calls=calls, using=using)


def pair(first, second):
    a, b = inspect(first), inspect(second)
    if (a["pipeline"], b["pipeline"]) != ("legacy", "viaIR"):
        raise ValueError("ordered legacy/viaIR inputs required")
    ah, bh = a["header"], b["header"]
    for field in ["compilerFile", "compilerSha256", "solcVersion", "solkeyCommit", "sourceSha256", "acceptedPragmas", "provenanceVersion", "validationStage"]:
        if ah.get(field) != bh.get(field):
            raise ValueError("pipeline provenance mismatch: " + field)
    settings = lambda h: {k: v for k, v in h["settings"].items() if k != "viaIR"}
    if settings(ah) != settings(bh):
        raise ValueError("settings differ beyond pipeline")
    if a["canonical_ast_sha256"] != b["canonical_ast_sha256"]:
        raise ValueError("analysis AST identities differ")
    return dict(schema_version=1, boundary="Compiler-AST identity inventory only; not Source.Env/SrcProg, origin/admission, execution, installation or bytecode adequacy. AST IDs are neither Source declaration positions nor runtime code indexes.",
                canonical_ast_equal=True, legacy=a, viaIR=b)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        parser.error("bulk output must remain outside Git")
    paths = [ROOT / "tests/solc/LibraryTry.ast.json", ROOT / "tests/solc/LibraryTryIR.ast.json"]
    report = pair(*(json.loads(p.read_text()) for p in paths))
    report["inputs"] = [dict(path=str(p.relative_to(ROOT)), sha256=digest(p.read_bytes())) for p in paths]
    source = ROOT / "tests/solc/LibraryTry.sol"
    report["local_raw_source"] = dict(path=str(source.relative_to(ROOT)), sha256=digest(source.read_bytes()),
        matches_reported_header_hash=digest(source.read_bytes()) == report["legacy"]["header"].get("sourceSha256"),
        boundary="Local raw bytes match the recorded header digest when true. This does not independently reproduce compilation or supply actual Source origins.")
    output.mkdir(parents=True, exist_ok=True)
    (output / "library-source-bindings.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(canonical_ast_equal=True, declarations=len(report["legacy"]["declarations"]),
        functions=len(report["legacy"]["functions"]), raw_source_matches_header=report["local_raw_source"]["matches_reported_header_hash"])))


if __name__ == "__main__":
    main()
