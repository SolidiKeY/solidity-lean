#!/usr/bin/env python3
"""Guard against counting private-name guesses or inherited fields as kernel coverage.

Join the frozen lexical census to the 190-core/37-Bridge generated inspection
manifests. Private identities and inherited obligations are source candidates
only. No inspection is executed and no kernel link or witness is certified.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import types

MEMBER = "7a9f8aa5b391696c70e3cb23b76135869f79bacb"
EMITTER = "ff0c28137e7aa031df7da1f026c3b501612720af"
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PREFIX = "scripts/h62/item2/audit-bytecode-selection/"
BOUNDARY = "Static linkage plan only: no executed inspection, verified kernel identity, proof-type classification, witness feasibility or coverage."


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def load_tool(repo, commit, name):
    raw = git(repo, "show", commit + ":" + PREFIX + name + ".py")
    module = types.ModuleType("h70_frozen_" + name)
    module.__file__ = commit + ":" + PREFIX + name + ".py"
    exec(compile(raw, module.__file__, "exec"), module.__dict__)
    return module, raw


def validate_inspection(raw, pins, package, sources, template, tool_hashes):
    expected = {path[:-5].replace("/", ".") if package == "core" else path[7:-5].replace("/", "."): path
                for path in sources if path.startswith("Solidity/" if package == "core" else "Bridge/")}
    modules = sorted(expected)
    if pins["base"] != BASE or pins["modules"] != modules:
        raise ValueError("wrong base, module order or incomplete package membership")
    if pins["source_sha256"] != {path: sources[path] for path in expected.values()}:
        raise ValueError("inspection source hashes differ")
    if pins["inspection_template_sha256"] != sha(template.encode()):
        raise ValueError("inspection template differs")
    if package == "core":
        keys = {"base", "modules", "source_sha256", "inspection_template_sha256"}
        if set(pins) != keys | {"manifest_sha256", "inspection_sha256"}:
            raise ValueError("unexpected core manifest fields")
        payload = {key: pins[key] for key in keys}
        fingerprint = sha(json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode())
    elif package == "Bridge":
        keys = {"schema_version", "package_root", "base", "member_head", "module_sources", "modules",
                "source_sha256", "inspection_template_sha256", "census_tool_sha256", "generator_tool_sha256",
                "execution_status", "boundary", "emitter_sha256"}
        if set(pins) != keys | {"manifest_sha256", "inspection_sha256"}:
            raise ValueError("unexpected Bridge manifest fields")
        if (pins["schema_version"] != 2 or pins["package_root"] != "Bridge" or pins["member_head"] != MEMBER
                or pins["module_sources"] != expected or pins["execution_status"] != "not run"):
            raise ValueError("Bridge package provenance differs")
        for key, value in tool_hashes.items():
            if pins[key] != value:
                raise ValueError("Bridge frozen tool hash differs: " + key)
        if pins["boundary"] != "Generated only; no Lean execution, kernel inspection, source-to-kernel linkage, witness or acceptance.":
            raise ValueError("Bridge generation boundary differs")
        payload = {key: pins[key] for key in keys}
        fingerprint = sha(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode())
    else:
        raise ValueError("unknown package")
    if pins["manifest_sha256"] != fingerprint:
        raise ValueError("inspection fingerprint differs")
    rebuilt = "import Lean\n" + "".join("import " + name + "\n" for name in modules)
    rebuilt += template.replace("MODULES", ", ".join("`" + name for name in modules)).replace("FINGERPRINT", fingerprint)
    if raw != rebuilt.encode() or pins["inspection_sha256"] != sha(raw):
        raise ValueError("generated inspection bytes differ")
    return {path: {"module": module, "package": package,
                   "inspection_manifest_sha256": fingerprint, "inspection_sha256": sha(raw)}
            for module, path in expected.items()}


EVENT = re.compile(
    r"(?m)^[ \t]*(?P<modifiers>(?:(?:@\[[^\n]*?\]|private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>namespace|section|end|theorem|lemma|def|abbrev|structure|class|inductive|opaque|instance|example)"
    r"\b[ \t]*(?P<name>[^\s({:]*)(?=[\s({:]|$)"
)


def top_level_keyword(text, word):
    depth = 0
    for index, char in enumerate(text):
        if depth == 0 and text.startswith(word, index):
            before = text[index - 1] if index else " "
            after = text[index + len(word)] if index + len(word) < len(text) else " "
            if not (before.isalnum() or before == "_") and not (after.isalnum() or after == "_"):
                return index
        if char in "({[⦃": depth += 1
        elif char in ")}]⦄":
            depth -= 1
            if depth < 0: raise ValueError("unbalanced source header")
    return None


def split_parents(text):
    parts, depth, start = [], 0, 0
    for index, char in enumerate(text):
        if char in "({[⦃": depth += 1
        elif char in ")}]⦄":
            depth -= 1
            if depth < 0: raise ValueError("unbalanced extends expression")
        elif char == "," and depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
    if depth: raise ValueError("unbalanced extends expression")
    parts.append(text[start:].strip())
    if any(not part for part in parts): raise ValueError("empty parent expression")
    return parts


def classify_source(path, text, scanner):
    clean = scanner.mask(text)
    stack, private, structures, notes, tokens = [], [], [], [], []
    for event in EVENT.finditer(clean):
        kind, name = event.group("kind", "name")
        if kind in ("namespace", "section"):
            stack.append((kind, name))
            continue
        if kind == "end":
            if stack:
                popped = stack.pop()
                if name and name != popped[1]:
                    notes.append({"line": text.count("\n", 0, event.start()) + 1,
                                  "status": "scope-label resolution requires elaboration"})
            else:
                notes.append({"line": text.count("\n", 0, event.start()) + 1,
                              "status": "unmatched lexical end; scope resolution requires elaboration"})
            continue
        namespace = ".".join(name for kind, name in stack if kind == "namespace")
        candidate = (namespace + "." if namespace else "") + name
        source_id = path + ":" + str(len(text[:event.start()].encode()))
        if kind in ("theorem", "lemma"):
            tokens.append({"id": source_id, "name_token_line": text.count("\n", 0, event.start("name")) + 1})
        if re.search(r"(?:^|\s)private(?:\s|$)", event.group("modifiers")):
            private.append({"id": source_id, "kind": kind, "candidate_user_name": candidate,
                            "name_token_line": text.count("\n", 0, event.start("name")) + 1,
                            "observed_kernel_name": None,
                            "classification": "explicit private modifier; mangled identity pending kernel inspection"})
        if kind not in ("structure", "class"):
            continue
        line_start = clean.rfind("\n", 0, event.start()) + 1
        command_line = clean[line_start:].split("\n", 1)[0]
        indent = len(command_line) - len(command_line.lstrip(" \t"))
        # End at the next nonempty line no more indented than this command.
        first_newline = clean.find("\n", event.end())
        stop = len(clean)
        if first_newline >= 0:
            cursor = first_newline + 1
            for line in clean[cursor:].splitlines(keepends=True):
                if line.strip() and len(line) - len(line.lstrip(" \t")) <= indent:
                    stop = cursor
                    break
                cursor += len(line)
        fragment = clean[event.end():stop]
        where = top_level_keyword(fragment, "where")
        row = {"id": source_id, "path": path, "kind": kind, "candidate_user_name": candidate,
               "namespace_candidate": namespace, "line": text.count("\n", 0, event.start()) + 1,
               "parents": [], "fields": [], "kernel_identity_verified": False}
        if where is None:
            row["status"] = "unsupported header retained; kernel inspection required"
            row["source_fragment_sha256"] = sha(text[event.start():stop].encode())
            structures.append(row)
            continue
        header = fragment[:where]
        extends = top_level_keyword(header, "extends")
        if extends is not None:
            raw = text[event.end() + extends + len("extends"):event.end() + where]
            row["parents"] = [{"expression": part, "resolution": "source-only; kernel parent metadata pending"}
                              for part in split_parents(raw)]
        body_start = event.end() + where + len("where")
        lines = list(re.finditer(r"(?m)^([ \t]*)([^\n]+)", clean[body_start:stop]))
        candidates = [line for line in lines if line.group(2).strip() and len(line.group(1)) > indent]
        field_indent = min((len(line.group(1)) for line in candidates), default=None)
        row["unparsed_body_lines"] = []
        row["source_body_sha256"] = sha(text[body_start:stop].encode())
        for line in candidates:
            if len(line.group(1)) != field_indent:
                continue
            field = re.match(r"(«[^»]+»|[^\s:({]+)\s*:", line.group(2))
            if field:
                offset = body_start + line.start() + len(line.group(1))
                row["fields"].append({"id": path + ":" + str(len(text[:offset].encode())),
                                      "name": field.group(1), "line": text.count("\n", 0, offset) + 1,
                                      "observed_kernel_projection": None, "proof_type": None,
                                      "classification": "direct source field; proof_type and projection pending kernel inspection"})
            else:
                offset = body_start + line.start()
                row["unparsed_body_lines"].append({"line": text.count("\n", 0, offset) + 1,
                                                    "source": text[offset:body_start + line.end()],
                                                    "status": "retained; direct-field parsing unresolved"})
        row["status"] = "source record candidate only; fields may have generated or inherited companions"
        structures.append(row)
    return {"private_declarations": private, "structures": structures, "scope_notes": notes, "theorem_tokens": tokens}


def inherited_candidates(structures):
    by_id = {row["id"]: row for row in structures}
    if len(by_id) != len(structures): raise ValueError("duplicate structure source identity")
    result = []
    for root in structures:
        collected, unresolved, cycles = {}, [], []
        def walk(row, trail):
            if row["id"] in trail:
                cycles.append(trail + [row["id"]])
                return
            trail = trail + [row["id"]]
            for field in row["fields"]:
                collected.setdefault(field["id"], {"source_field": field, "routes": []})["routes"].append(trail)
            for parent in row["parents"]:
                # Name lookup here is deliberately only a lexical candidate join.
                head = parent["expression"].split()[0]
                matches = [other for other in structures
                           if other["candidate_user_name"] == head or
                           ("." not in head and other["candidate_user_name"].rsplit(".", 1)[-1] == head)]
                if len(matches) != 1:
                    unresolved.append({"from": row["id"], "parent_expression": parent["expression"],
                                       "source_candidates": sorted(other["id"] for other in matches)})
                    continue
                walk(matches[0], trail)
        walk(root, [])
        result.append({"structure_id": root["id"], "candidate_user_name": root["candidate_user_name"],
                       "source_fields_once": [collected[key] for key in sorted(collected)],
                       "unresolved_parents": unresolved, "cycles": cycles,
                       "classification": "conditional lexical parent graph, not canonical kernel projections",
                       "kernel_obligations_verified": 0})
    return result


def build(repo, census_path, core_path, bridge_path):
    scanner, scanner_raw = load_tool(repo, MEMBER, "census")
    bridge, bridge_raw = load_tool(repo, EMITTER, "bridge_inspection")
    generator_raw = git(repo, "show", MEMBER + ":" + PREFIX + "elaborated_census.py")
    template = bridge.extract_template(generator_raw)
    source_data = json.loads(census_path.read_text())
    paths, _ = scanner.mapped_paths(repo)
    source_hashes = {path: sha((repo / path).read_bytes()) for path in paths}
    if source_data["base"] != BASE or source_data["files"] != [{"path": path, "sha256": source_hashes[path]} for path in paths]:
        raise ValueError("frozen source census membership differs")
    expected_rows, files, structures, private, scope_notes, anchors = [], [], [], [], [], {}
    for path in paths:
        raw = (repo / path).read_bytes()
        if raw != git(repo, "show", BASE + ":" + path):
            raise ValueError("frozen source changed: " + path)
        text = raw.decode()
        for row in scanner.declarations(text):
            expected_rows.append(dict(row, path=path, id=path + ":" + str(row["byte_start"])))
        classification = classify_source(path, text, scanner)
        structures.extend(classification["structures"])
        anchors.update({row["id"]: row["name_token_line"] for row in classification["theorem_tokens"]})
        private.extend(dict(row, path=path) for row in classification["private_declarations"])
        scope_notes.extend(dict(note, path=path) for note in classification["scope_notes"])
        files.append({"path": path, "source_sha256": sha(raw)})
    if source_data["declarations"] != expected_rows:
        raise ValueError("source candidate census differs; no dropped, changed or duplicate row allowed")
    if source_data["module_map_sha256"] != sha((repo / scanner.MAP).read_bytes()):
        raise ValueError("source census module map differs")
    expected_summary = {"files": len(paths), "named_theorem_candidates": len(expected_rows),
                        "witnesses_verified": 0, "uncovered_candidates": len(expected_rows)}
    if source_data["summary"] != expected_summary:
        raise ValueError("source census summary overclaims or differs")
    jobs = {}
    for package, path in [("core", core_path), ("Bridge", bridge_path)]:
        pins = json.loads(path.with_suffix(".pins.json").read_text())
        jobs.update(validate_inspection(path.read_bytes(), pins, package, source_hashes, template,
                    {"census_tool_sha256": sha(scanner_raw), "generator_tool_sha256": sha(generator_raw),
                     "emitter_sha256": sha(bridge_raw)}))
    if set(jobs) != set(paths): raise ValueError("inspection manifest union is not exactly the frozen file set")
    for row in expected_rows:
        row.update(jobs[row["path"]])
        row["candidate_user_name"] = row.pop("name_candidate")
        row["observed_kernel_name"] = None
        row["name_token_line"] = anchors.get(row["id"])
        row["kernel_join_key_candidate"] = [row["module"], row["name_token_line"], row["candidate_user_name"]]
        row["kernel_link_status"] = "pending validated inspection, private user-name and declaration-range join"
        row["witness_status"] = "uncovered; no static source candidate is a simultaneous witness"
    for row in files + private + structures:
        row.update(jobs[row["path"]])
    graph = inherited_candidates(structures)
    return {"schema_version": 1, "base": BASE, "boundary": BOUNDARY,
            "source_census_sha256": sha(census_path.read_bytes()), "scanner_sha256": sha(scanner_raw),
            "linker_sha256": sha(Path(__file__).read_bytes()), "files": files,
            "source_candidates": expected_rows, "private_declarations": private,
            "structure_candidates": structures, "inherited_field_candidates": graph,
            "scope_notes": scope_notes,
            "kernel_join_contract": ["same package/module and frozen source hash",
                                     "kernel theorem kind and exact type/binder metadata retained",
                                     "privateToUserName and selection_line match the proposed source key",
                                     "missing/ambiguous/private/generated matches remain uncovered",
                                     "identity linkage never establishes premise feasibility or witness coverage"],
            "summary": {"files": len(files), "packages": dict(Counter(row["package"] for row in files)),
                        "source_candidates": len(expected_rows), "private_source_declarations": len(private),
                        "structure_candidates": len(structures),
                        "structures_with_extends": sum(bool(row["parents"]) for row in structures),
                        "lexical_parent_edges_without_unique_candidate": sum(len(row["unresolved_parents"]) for row in graph),
                        "kernel_parent_edges_pending": sum(len(row["parents"]) for row in structures),
                        "private_kernel_identities_pending": len(private),
                        "direct_field_proof_types_pending": sum(len(row["fields"]) for row in structures),
                        "source_name_anchors_pending": sum(row["name_token_line"] is None for row in expected_rows),
                        "kernel_links_verified": 0, "simultaneous_witnesses_verified": 0,
                        "core_and_bridge_inspection_executed": False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--source-census", required=True, type=Path)
    parser.add_argument("--core-inspection", required=True, type=Path)
    parser.add_argument("--bridge-inspection", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if any(args.output.resolve().is_relative_to(root.resolve()) for root in (args.repo, Path(__file__).resolve().parents[4])):
        raise ValueError("H44: output must be outside repositories")
    if args.output.exists() or any(parent.is_symlink() for parent in (args.output, *args.output.parents)):
        raise ValueError("refusing existing or symlink output")
    result = build(args.repo.resolve(), args.source_census, args.core_inspection, args.bridge_inspection)
    with args.output.open("x") as out:
        out.write(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps(result["summary"], sort_keys=True))
    print(BOUNDARY)


if __name__ == "__main__":
    main()
