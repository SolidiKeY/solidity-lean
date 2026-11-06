#!/usr/bin/env python3
"""Conservative lexical duplicate discovery. Results are leads, not Lean proofs."""
import argparse
import fnmatch
import hashlib
import hmac
import json
import re
from pathlib import Path

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)?(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|local[ \t]+|partial[ \t]+|unsafe[ \t]+)*(theorem|lemma|def|abbrev|opaque|example|instance|structure|inductive|class|axiom|constant)(?=[\s(:{\[])(?:[ \t]+([^\s(:{\[]+))?")
TOKEN = re.compile(r"""r(#+)"[\s\S]*?"\1|'(?:\\(?:u\{[0-9A-Fa-f]+\}|u[0-9A-Fa-f]{4}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'|«[^»]*»|"(?:\\.|[^"\\])*"|(?:[^\W\d]|_)[\w\'!?]*(?:\.(?:[^\W\d]|_)[\w\'!?]*)*|[\w\']+(?:\.[\w\']+)*|[^\s]""")
RAW_START = re.compile(r'r(#+)"')
CHAR = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|u[0-9A-Fa-f]{4}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'")
BINDER = re.compile(r"([({\[])\s*((?:[^\W\d]|_)[\w'!?]*(?:\s+(?:[^\W\d]|_)[\w'!?]*)*)\s*:\s*([^(){}\[\]]*)([)}\]])\s*")

def raw_literal(text, i):
    if text[i] != "r" or (i and (text[i-1].isalnum() or text[i-1] in "_'!?")): return None
    match = RAW_START.match(text, i)
    if not match: return None
    close = '"' + match.group(1)
    end = text.find(close, match.end())
    if end < 0: raise ValueError("unterminated raw string")
    return end + len(close)

def char_literal(text, i):
    if text[i] != "'" or (i and (text[i-1].isalnum() or text[i-1] in "_'!?")): return None
    return CHAR.match(text, i)

def mask(text):
    out = list(text)
    i = depth = 0
    string = False
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out[i:i+2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out[i:i+2] = "  "
                i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif quoted:
            if text[i] == "»": quoted = False
            i += 1
        elif string:
            if text[i] == "\\": i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif text[i] == "r" and i+1 < len(text) and text[i+1] == "#" and (end := raw_literal(text, i)):
            i = end
        elif text[i] == "'" and (literal := char_literal(text, i)):
            i = literal.end()
        elif text[i] == '"':
            string = True
            i += 1
        elif text[i] == "«":
            quoted = True
            i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i+2] = "  "
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0: j = len(text)
            out[i:j] = " " * (j-i)
            i = j
        else: i += 1
    if depth or string or quoted: raise ValueError("unterminated comment, string or escaped identifier")
    return "".join(out)

def hide_strings(text):
    out = list(text)
    i = 0
    inside = False
    quoted = False
    while i < len(text):
        c = text[i]
        if quoted:
            if c == "»": quoted = False
            if c != "\n": out[i] = " "
        elif inside:
            if c == "\\" and i+1 < len(text):
                out[i] = " "
                if text[i+1] != "\n": out[i+1] = " "
                i += 2
                continue
            if c == '"': inside = False
            if c != "\n": out[i] = " "
        elif c == "r" and i+1 < len(text) and text[i+1] == "#" and (end := raw_literal(text, i)):
            for j in range(i, end):
                if text[j] != "\n": out[j] = " "
            i = end
            continue
        elif c == "'" and (literal := char_literal(text, i)):
            end = literal.end()
            for j in range(i, end):
                if text[j] != "\n": out[j] = " "
            i = end
            continue
        elif c == '"':
            inside = True
            out[i] = " "
        elif c == "«":
            quoted = True
            out[i] = " "
        i += 1
    return "".join(out)

def tokenize(s):
    return [match.group(0) for match in TOKEN.finditer(s)]

def normalize(header):
    # Types are read before introducing the names bound by their group.
    if "«" in header or "»" in header: return None
    env = {}
    out = []
    pos = 0
    while True:
        match = BINDER.match(header, pos)
        if not match: break
        opening, closing = match.group(1), match.group(4)
        if {"(": ")", "{": "}", "[": "]"}[opening] != closing: return None
        ns = match.group(2).split()
        if "_" in ns or len(set(ns)) != len(ns) or any(n in env for n in ns): return None
        type_text = match.group(3)
        if any(c in type_text for c in "λ∀∃") or re.search(r"\b(fun|let|forall|match)\b", type_text): return None
        typ = tokenize(type_text)
        if any("." in t and any(n in t.split(".") for n in env) for t in typ): return None
        if any(typ[i] == "." and i + 1 < len(typ) and typ[i+1] in env for i in range(len(typ))): return None
        out.extend([opening] + ["$binder" + str(len(env)+i) for i in range(len(ns))] + [":"])
        out.extend(env.get(t, t) for t in typ)
        out.append(closing)
        for n in ns: env[n] = "$binder" + str(len(env))
        pos = match.end()
    rest = header[pos:]
    if any(c in rest for c in "{}[]λ∀∃") or re.search(r"\b(fun|let|forall|match|by|do|have)\b", header): return None
    if re.search(r"\([^()]*:", rest): return None
    ts = tokenize(rest)
    if any("." in t and any(n in t.split(".") for n in env) for t in ts): return None
    if any(ts[i] == "." and i + 1 < len(ts) and ts[i+1] in env for i in range(len(ts))): return None
    out.extend(env.get(t, t) for t in ts)
    return out

def split_definition(content):
    """Find a top-level :=, ignoring strings and bracketed default values."""
    result = split_declaration(content, allow_equations=False)
    return None if result is None else result[:2]

def split_declaration(content, allow_equations=True, skeleton=None):
    """Recognize := or an unambiguous line-initial equation case."""
    if skeleton is None: skeleton = hide_strings(content)
    stack = []
    pairs = {")": "(", "]": "[", "}": "{"}
    line_start = 0
    has_result_type = False
    for i, c in enumerate(skeleton):
        if c == "\n":
            line_start = i + 1
            continue
        if c in "([{": stack.append(c); continue
        if c in ")]}":
            if not stack or stack.pop() != pairs[c]: return None
            continue
        if stack: continue
        if c == ":":
            if skeleton.startswith(":=", i):
                return content[:i], content[i+2:], "assignment"
            if not skeleton.startswith("::", i): has_result_type = True
        if allow_equations and c == "|" and not skeleton[line_start:i].strip():
            line_end = skeleton.find("\n", i)
            if line_end < 0: line_end = len(skeleton)
            if not has_result_type or "=>" not in skeleton[i:line_end]: return None
            return content[:i], content[i:], "equations"
    return None

def scan(path, root, source=None):
    if source is None: source = path.read_bytes()
    text = mask(source.decode("utf-8"))
    skeleton = hide_strings(text)
    matches = list(DECL.finditer(skeleton))
    context_commands = list(re.finditer(r"(?m)^[ \t]*(?:import|namespace|section|end|open|variable|universe)\b[^\n]*", skeleton))
    rows = []
    relative_path = path.relative_to(root).as_posix()
    def indent(m):
        prefix = re.match(r"[ \t]*", skeleton[m.start():m.start(1)]).group()
        return len(prefix.expandtabs(8))
    for i, match in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else len(text)
        content = text[match.end():end]
        content_skeleton = skeleton[match.end():end]
        command = re.search(r"(?m)^[ \t]*(?:end|namespace|section|open|variable|attribute|#\w+)\b", content_skeleton)
        command_inside = False
        if command:
            prefix = re.match(r"[ \t]*", command.group()).group()
            command_inside = len(prefix.expandtabs(8)) > indent(match)
            content = content[:command.start()]
            content_skeleton = content_skeleton[:command.start()]
        qualifiers = sorted(re.findall(r"\b(?:partial|unsafe|noncomputable)\b", skeleton[match.start():match.start(1)]))
        context = digest([m.group().strip() for m in context_commands if m.start() < match.start()])
        unsupported = match.group(1) in {"structure", "inductive", "class", "axiom", "constant"}
        parts = None if unsupported else split_declaration(content, skeleton=content_skeleton)
        reason = "unsupported-declaration-form" if unsupported else "missing-top-level-definition"
        if parts is not None:
            head_skeleton = content_skeleton[:len(parts[0])]
            if re.search(r"\bwhere\b", head_skeleton):
                parts, reason = None, "unsupported-where-declaration"
            elif re.search(r"(?m)^[ \t]*\|", head_skeleton):
                parts, reason = None, "unsupported-equation-declaration"
        if parts is None:
            rows.append(dict(path=relative_path,
                             line=text.count("\n", 0, match.start())+1,
                             kind=match.group(1), name=match.group(2) or "<anonymous>",
                             statement=None, body=[], body_form=None, body_reject_reason=reason,
                             owner="unknown", context_hash=context, qualifiers=qualifiers,
                             reject_reason=reason))
            continue
        header, body, body_form = parts
        next_is_nested = i + 1 < len(matches) and indent(matches[i+1]) > indent(match)
        body_reject_reason = "nested-declaration-boundary" if next_is_nested else None
        if "«" in header or "»" in header: body_reject_reason = "escaped-identifier-boundary"
        if command_inside: body_reject_reason = "indented-command-boundary"
        body_skeleton = content_skeleton[len(header) + (2 if body_form == "assignment" else 0):]
        if re.search(r"\bwhere\b", body_skeleton):
            body_reject_reason = "body-may-have-local-helpers"
        boundary = re.search(r"(?m)^[ \t]*(?:end|namespace|section|open|variable|attribute|#\w+)\b", body_skeleton)
        if boundary:
            prefix = re.match(r"[ \t]*", boundary.group()).group()
            if len(prefix.expandtabs(8)) > indent(match):
                body_reject_reason = "indented-command-boundary"
            body = body[:boundary.start()]
        normalized = normalize(header.strip())
        rows.append(dict(path=relative_path,
                         line=text.count("\n", 0, match.start())+1,
                         kind=match.group(1), name=match.group(2) or "<anonymous>",
                         statement=normalized, body=tokenize(body), body_form=body_form,
                         body_reject_reason=body_reject_reason, owner="unknown", context_hash=context, qualifiers=qualifiers,
                         reject_reason="unsupported-binder-syntax" if normalized is None else None))
    return rows

def digest(obj):
    return hashlib.sha256(json.dumps(obj, ensure_ascii=False, separators=(",", ":")).encode()).hexdigest()

MAX_PREVIOUS_BYTES = 512 * 1024 * 1024

def unique_previous_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError("duplicate previous JSON key")
        result[key] = value
    return result

def reject_previous_number(_):
    raise ValueError("non-integer previous JSON number")

def load_previous(path, expected):
    if not re.fullmatch(r"[0-9a-f]{64}", expected):
        raise ValueError("previous SHA256 must be 64 lowercase hexadecimal digits")
    with path.open("rb") as stream:
        raw = stream.read(MAX_PREVIOUS_BYTES + 1)
    if len(raw) > MAX_PREVIOUS_BYTES:
        raise ValueError("previous report exceeds byte limit")
    actual = hashlib.sha256(raw).hexdigest()
    if not hmac.compare_digest(actual, expected):
        raise ValueError("previous report SHA256 mismatch")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=unique_previous_object,
                      parse_constant=reject_previous_number, parse_float=reject_previous_number)

def prior_map(records, key, label):
    if not isinstance(records, list): raise ValueError("malformed previous " + label)
    result = {}
    for row in records:
        if not isinstance(row, dict) or not isinstance(row.get(key), str) or row[key] in result:
            raise ValueError("malformed or duplicate previous " + label)
        result[row[key]] = row
    return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--owners", type=Path, help="JSON mapping exact relative paths to owner labels")
    parser.add_argument("--previous", type=Path, help="previous scanner JSON report")
    parser.add_argument("--previous-sha256", help="caller-supplied SHA256 pin for previous report")
    parser.add_argument("--registry", type=Path, help="coordinator ownership snapshot; references are advisory")
    args = parser.parse_args()
    root = args.root.resolve()
    if (args.previous is None) != (args.previous_sha256 is None):
        parser.error("--previous and --previous-sha256 must be supplied together")
    selection = dict(root=str(root), patterns=sorted(set(args.paths)))
    previous = None
    old_inputs, old_statements, old_bodies = {}, {}, {}
    if args.previous is not None:
        try:
            previous = load_previous(args.previous, args.previous_sha256)
            if (not isinstance(previous, dict) or type(previous.get("version")) is not int or
                previous.get("version") != 2 or previous.get("selection") != selection):
                raise ValueError("incompatible version or selection")
            if previous.get("errors") != [] or previous.get("unmatched_patterns") != []:
                raise ValueError("previous report is incomplete")
            old_inputs = prior_map(previous.get("inputs"), "path", "inputs")
            if any(not isinstance(row.get("sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", row["sha256"])
                   for row in old_inputs.values()):
                raise ValueError("malformed previous input hash")
            old_statements = prior_map(previous.get("candidates"), "lexical_key", "statement candidates")
            old_bodies = prior_map(previous.get("body_candidates"), "body_hash", "body candidates")
            if any(not re.fullmatch(r"[0-9a-f]{64}", key) for key in (*old_statements, *old_bodies)):
                raise ValueError("malformed previous candidate key")
            for label, groups in (("statement", old_statements), ("body", old_bodies)):
                for row in groups.values():
                    if (not isinstance(row.get("members"), list) or len(row["members"]) < 2 or
                        not isinstance(row.get("reject_reasons"), list) or
                        any(not isinstance(reason, str) for reason in row["reject_reasons"]) or
                        not isinstance(row.get("action"), str) or any(
                            not isinstance(member, dict) or
                            not isinstance(member.get("path"), str) or
                            type(member.get("line")) is not int or member["line"] < 1 or
                            not isinstance(member.get("name"), str) or
                            not isinstance(member.get("kind"), str) or
                            not isinstance(member.get("owner"), str)
                            for member in row["members"])):
                        raise ValueError("malformed previous " + label + " candidate")
            for field in ("owner_config_sha256", "registry_sha256", "scanner_sha256"):
                value = previous.get(field)
                if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
                    raise ValueError("malformed previous " + field)
        except (OSError, UnicodeError, ValueError, RecursionError) as exc:
            parser.error("previous report: " + str(exc))
    matched = {pat: sorted(f for f in root.glob(pat) if f.suffix == ".lean") for pat in args.paths}
    unmatched = sorted(pat for pat, paths in matched.items() if not paths)
    files = sorted({f for paths in matched.values() for f in paths})
    rows, errors, inputs, aliases = [], [], [], []
    resolved_inputs = {}
    owners = json.loads(args.owners.read_text()) if args.owners else {}
    if not isinstance(owners, dict) or not all(isinstance(k, str) and isinstance(v, str) and v for k, v in owners.items()):
        parser.error("owners must be a path-to-owner JSON object")
    registry_bytes = args.registry.read_bytes() if args.registry else b""
    registry = json.loads(registry_bytes) if registry_bytes else {}
    refs = set()
    def strings(value):
        if isinstance(value, str): yield value
        elif isinstance(value, dict):
            for child in value.values(): yield from strings(child)
        elif isinstance(value, list):
            for child in value: yield from strings(child)
    for item in registry.get("items", []):
        if not isinstance(item, dict): parser.error("invalid registry item")
        for value in strings(item):
            for pattern in re.findall(r"(?:Solidity|tests|scripts)/[A-Za-z0-9_./*?\[\]-]*", value):
                pattern = pattern.rstrip(".,;:)")
                refs.add((pattern, str(item.get("id", "")), str(item.get("owner", "")), str(item.get("status", ""))))
    for path in files:
        try:
            rel = path.relative_to(root).as_posix()
            if ".." in path.relative_to(root).parts:
                raise ValueError("selected path contains parent traversal")
            resolved = path.resolve(strict=True)
            if not resolved.is_relative_to(root):
                raise ValueError("selected Lean path resolves outside root")
            if not resolved.is_file():
                raise ValueError("selected Lean path is not a regular file")
            source = path.read_bytes()
            target = resolved.relative_to(root).as_posix()
            resolved_inputs[rel] = target
            if target != rel:
                aliases.append(dict(path=rel, resolved_path=target))
            inputs.append(dict(path=rel, sha256=hashlib.sha256(source).hexdigest()))
            found = scan(path, root, source)
            references = [dict(pattern=p, id=i, owner=o, status=st) for p, i, o, st in sorted(refs)
                if (rel.startswith(p) if p.endswith("/") else fnmatch.fnmatchcase(rel, p))]
            for row in found:
                row["owner"] = owners.get(rel, "unknown")
                row["registry_references"] = references
            rows.extend(found)
        except (OSError, ValueError, UnicodeError, RuntimeError) as exc:
            errors.append(dict(path=str(path), reason=str(exc)))
    def alias_reasons(group):
        paths = {row["path"] for row in group}
        return (["shared-resolved-source"]
                if len({resolved_inputs[path] for path in paths}) < len(paths) else [])
    groups = {}
    for row in rows:
        if row["statement"] is not None:
            groups.setdefault(digest([row["kind"], row["qualifiers"], row["statement"], row["context_hash"]]), []).append(row)
    candidates = []
    for key, group in sorted(groups.items()):
        if len(group) > 1:
            candidates.append(dict(lexical_key=key, reject_reasons=["intrinsic-signature-unresolved", "ownership-requires-live-verification"] + alias_reasons(group),
                members=[{k:v for k,v in row.items() if k not in ("statement", "body")} for row in group],
                body_hashes=sorted({digest(row["body"]) for row in group}),
                action="weak-lexical-lead-review-signatures-and-ownership"))
    bodies = {}
    for row in rows:
        if row["body"] and row["body_reject_reason"] is None:
            bodies.setdefault(digest([row["body_form"], row["body"]]), []).append(row)
    body_candidates = []
    for key, group in sorted(bodies.items()):
        if len(group) > 1:
            body_candidates.append(dict(body_hash=key,
                members=[{k:v for k,v in row.items() if k not in ("statement", "body")} for row in group],
                reject_reasons=sorted({"intrinsic-signature-unresolved", "ownership-requires-live-verification"} | set(alias_reasons(group)) |
                    ({"different-or-unsupported-statements"}
                    if len({digest([row["kind"], row["qualifiers"], row["statement"], row["context_hash"]]) for row in group}) > 1 or
                       any(row["statement"] is None for row in group) else set())),
                action="weak-lexical-lead-review-signatures-and-ownership"))
    old = {path: row["sha256"] for path, row in old_inputs.items()}
    new = {x["path"]: x["sha256"] for x in inputs}
    def candidate_delta(old_groups, new_rows, key):
        new_groups = {row[key]: row for row in new_rows}
        def stable(row):
            return hashlib.sha256(json.dumps(row, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        return dict(added=sorted(new_groups.keys()-old_groups.keys()),
                    removed=sorted(old_groups.keys()-new_groups.keys()),
                    changed=sorted(k for k in old_groups.keys() & new_groups.keys()
                                   if stable(old_groups[k]) != stable(new_groups[k])))
    changes = None
    if previous is not None and not errors and not unmatched:
        try:
            changes = dict(statements=candidate_delta(old_statements, candidates, "lexical_key"),
                           bodies=candidate_delta(old_bodies, body_candidates, "body_hash"))
        except (RecursionError, ValueError) as exc:
            parser.error("previous candidate comparison: " + str(exc))
    scanner_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    incomplete = bool(errors or unmatched)
    incremental = dict(added=None if incomplete else sorted(new.keys()-old.keys()),
        removed=None if incomplete else sorted(old.keys()-new.keys()),
        changed=None if incomplete else sorted(k for k in old.keys() & new.keys() if old[k] != new[k]),
        owner_config_changed=previous is not None and previous.get("owner_config_sha256") != digest(owners),
        registry_changed=previous is not None and previous.get("registry_sha256") != hashlib.sha256(registry_bytes).hexdigest(),
        scanner_changed=previous is not None and previous.get("scanner_sha256") != scanner_sha256,
        previous_sha256=args.previous_sha256,
        previous_provenance="caller-pin-unverified" if previous is not None else "no-baseline",
        comparison_status=("current-incomplete" if incomplete else
                           "no-baseline" if previous is None else "scanner-output-comparable"),
        candidate_groups=changes)
    rejected = [{k:r[k] for k in ("path", "line", "name", "reject_reason")} for r in rows if r["reject_reason"]]
    inventory = [{k:v for k,v in row.items() if k not in ("statement", "body")} for row in rows]
    rejection_counts = {}
    for row in rejected:
        reason = row["reject_reason"]
        rejection_counts[reason] = rejection_counts.get(reason, 0) + 1
    print(json.dumps(dict(version=2, selection=selection, inputs=inputs, declarations=len(rows), inventory=inventory, candidates=candidates, rejected_declarations=rejected,
        body_candidates=body_candidates, incremental=incremental, unmatched_patterns=unmatched, input_aliases=aliases,
        owner_config_sha256=digest(owners), registry_sha256=hashlib.sha256(registry_bytes).hexdigest(), scanner_sha256=scanner_sha256,
        rejections=dict(by_reason=rejection_counts,
                        unknown_ownership=sum(r["owner"] == "unknown" for r in rows)), errors=errors),
        sort_keys=True, ensure_ascii=False, indent=2))
    return bool(errors or unmatched)

if __name__ == "__main__":
    raise SystemExit(main())
