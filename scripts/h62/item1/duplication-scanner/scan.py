#!/usr/bin/env python3
"""Conservative lexical duplicate discovery. Results are leads, not Lean proofs.

The optional live fixture gate guards stale/unbound signature promotion; it
never accepts a saved receipt or removes candidate ownership/refusal checks.
"""
import argparse
import bisect
import fnmatch
import hashlib
import hmac
import json
import os
import re
import stat
from pathlib import Path

DECL = re.compile(r"(?m)^[ \t]*(?:private[ \t\r\n]+|public[ \t\r\n]+|protected[ \t\r\n]+|meta[ \t\r\n]+|noncomputable[ \t\r\n]+|local[ \t\r\n]+|scoped[ \t\r\n]+|partial[ \t\r\n]+|nonrec[ \t\r\n]+|unsafe[ \t\r\n]+)*(theorem|lemma|def|abbrev|opaque|example|instance|structure|inductive|class[ \t\r\n]+(?:inductive|abbrev)|class|axiom|constant)(?=[\s(:{\[])(?:[ \t\r\n]+([^\s(:{\[]+?)(?=\.\{|[\s(:{\[]|\Z))?")
ID_FIRST = r"A-Za-z_\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9\u03b1-\u03ba\u03bc-\u03c9\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
ID_REST = ID_FIRST + r"0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENT = "[" + ID_FIRST + "][" + ID_REST + "]*"
TOKEN = re.compile(r"""r(#+)"[\s\S]*?"\1|'(?:\\(?:u\{[0-9A-Fa-f]+\}|u[0-9A-Fa-f]{4}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'|«[^»]*»|"(?:\\.|[^"\\])*"|""" + IDENT + r"(?:\." + IDENT + r")*|[0-9]+(?:\.[0-9]+)*|[^\s]")
RAW_START = re.compile(r'r(#+)"')
CHAR = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|u[0-9A-Fa-f]{4}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'")
BINDER = re.compile(r"([({\[])\s*(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*:\s*([^(){}\[\]]*)([)}\]])\s*")

ID_REST_CHAR = re.compile("[" + ID_REST + "]")
# This records lexical spelling only; it is not a resolved kernel Name.
SOURCE_NAME = re.compile(r"\s*((?:«[^»]*»|" + IDENT + r")(?:\.(?:«[^»]*»|" + IDENT + r"))*)")
INSTANCE_PRIORITY = re.compile(r"\s*\(\s*priority\s*:=")

def signature_coverage(rows, signature_key="fixture_signature", linked_label="local-fixture-linkage"):
    """Guard partial live binding being mistaken for selected-scope coverage.

    This partitions lexical rows, including unsupported and same-spelling rows.
    It does not enumerate generated kernel declarations or establish ownership.
    Only the live gate may attach its designated signature field before this census.
    """
    entries = []
    counts = {linked_label: 0, "unresolved": 0}
    for row in rows:
        status = linked_label if signature_key in row else "unresolved"
        counts[status] += 1
        entries.append({k: row[k] for k in ("path", "line", "name", "kind")} |
                       {"status": status, "lexical_reject_reason": row["reject_reason"]})
    return {"basis": "selected lexical declaration rows; generated declarations are not enumerated",
            "total": len(rows), "counts": counts, "rows": entries,
            "complete_signature_coverage": counts["unresolved"] == 0 and bool(rows),
            "ownership_verified": False}

def live_receipt_hash(binder, output, live):
    """Guard persistent edits replacing the receipt cited by a live scan."""
    expected = hashlib.sha256((json.dumps(live, indent=2)+"\n").encode()).hexdigest()
    if binder.regular(output/"receipt.json")["sha256"] != expected:
        raise ValueError("live scanner receipt hash mismatch")
    return expected


def attach_source_bindings(rows, inputs, linked, live, source_path, signature_key="fixture_signature"):
    """Guard source drift, partial row coverage and stale annotation reuse."""
    selected = [row for row in rows if row["path"] == source_path]
    sources = [row for row in inputs if row["path"] == source_path]
    if not selected or len(sources) != 1:
        raise ValueError("missing or ambiguous selected source")
    source_hash = sources[0]["sha256"]
    if linked["source_sha256"] != source_hash or live["source_sha256"] != source_hash:
        raise ValueError("scan source differs from live source-location bytes")
    key = lambda row: tuple(row[k] for k in ("path", "line", "name", "kind"))
    by_key = {key(row):row for row in linked["rows"]}
    selected_keys = {key(row) for row in selected}
    if len(by_key) != len(linked["rows"]) or len(selected_keys) != len(selected) or set(by_key) != selected_keys:
        raise ValueError("source-location/selected-row coverage mismatch")
    direct = sum(row["status"] == "direct-source-signature-link" for row in linked["rows"])
    if direct != linked["linked"] or direct != live["linked"]:
        raise ValueError("source-location linkage count mismatch")
    if any(signature_key in row for row in selected):
        raise ValueError("stale source annotation already present")
    for row in selected:
        binding = by_key[key(row)]
        if binding["status"] == "direct-source-signature-link":
            row[signature_key] = {k:binding[k] for k in ("declaration", "signature", "selection")}
            row[signature_key].update(source_path=source_path, source_sha256=source_hash,
                                      linkage="direct-source-location")


def closure_source_receipt(live, source_path):
    """Guard dependency receipt rows being mistaken for the annotated target."""
    selected=[row for row in live["fresh_project_closure"] if row["source"]==source_path]
    if len(selected)!=1:
        raise ValueError("missing or ambiguous live closure source")
    return dict(live,source_sha256=selected[0]["source_sha256"])


def raw_literal(text, i):
    if text[i] != "r" or (i and (ID_REST_CHAR.fullmatch(text[i-1]))): return None
    match = RAW_START.match(text, i)
    if not match: return None
    close = '"' + match.group(1)
    end = text.find(close, match.end())
    if end < 0: raise ValueError("unterminated raw string")
    return end + len(close)

def char_literal(text, i):
    if text[i] != "'" or (i and (ID_REST_CHAR.fullmatch(text[i-1]))): return None
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

ATTRIBUTE_START = re.compile(r"(?m)^[ \t]*@\[")

def hide_attributes(skeleton):
    """Mask line-initial balanced attribute prefixes without moving lines."""
    out = list(skeleton)
    spans = []
    pos = 0
    while match := ATTRIBUTE_START.search(skeleton, pos):
        prefix_start = match.start()
        start = skeleton.find("@[", match.start(), match.end())
        while True:
            depth = 1
            end = start + 2
            while end < len(skeleton) and depth:
                if skeleton[end] == "[": depth += 1
                elif skeleton[end] == "]": depth -= 1
                end += 1
            if depth: raise ValueError("unterminated attribute prefix")
            for i in range(start, end):
                if skeleton[i] != "\n": out[i] = " "
            next_pos = end
            while next_pos < len(skeleton) and skeleton[next_pos].isspace(): next_pos += 1
            if not skeleton.startswith("@[", next_pos): break
            start = next_pos
        spans.append((prefix_start, end))
        pos = end
    return "".join(out), spans

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
    skeleton, attribute_spans = hide_attributes(hide_strings(text))
    matches = list(DECL.finditer(skeleton))
    attribute_ends = [end for _, end in attribute_spans]
    declaration_starts = []
    for match in matches:
        start = match.start()
        index = bisect.bisect_right(attribute_ends, match.start(1)) - 1
        if index >= 0:
            prefix_start, prefix_end = attribute_spans[index]
            between = skeleton[prefix_end:match.start(1)]
            if re.fullmatch(r"\s*(?:(?:private|public|protected|meta|noncomputable|local|scoped|partial|nonrec|unsafe)\s+)*", between):
                start = min(start, prefix_start)
        declaration_starts.append(start)
    context_commands = list(re.finditer(r"(?m)^[ \t]*(?:(?:import|namespace|section|end|open|variable|universe|set_option)|(?:(?:local|scoped)[ \t]+)*(?:notation|infixl|infixr|infix|prefix|postfix))\b[^\n]*", skeleton))
    # Preserve literal bytes and continuation lines until the next recognized
    # boundary. This remains a lexical approximation of the Lean environment.
    boundaries = sorted([m.start() for m in context_commands] + declaration_starts)
    context_spans = []
    for command in context_commands:
        index = bisect.bisect_right(boundaries, command.start())
        stop = boundaries[index] if index < len(boundaries) else len(text)
        # Scoped option/open headers may place `in` on a later line. Refuse
        # inline declaration prefixes that the line recognizer would miss.
        scoped = re.match(r"[ \t]*(set_option|open)\b", command.group())
        if (scoped and
            re.search(r"\bin[ \t]+(?:@\[|(?:private|public|protected|meta|noncomputable|local|scoped|partial|nonrec|unsafe|theorem|lemma|def|abbrev|opaque|example|instance|structure|inductive|class|axiom|constant)\b)", skeleton[command.start():stop])):
            raise ValueError("unsupported same-line scoped " + scoped.group(1) + " declaration")
        context_spans.append((command.start(), text[command.start():stop].strip()))
    rows = []
    relative_path = path.relative_to(root).as_posix()
    start_by_keyword = {match.start(1): start for match, start in zip(matches, declaration_starts)}
    def indent(m):
        start = start_by_keyword[m.start(1)]
        line_start = text.rfind("\n", 0, start) + 1
        prefix = re.match(r"[ \t]*", text[line_start:]).group()
        return len(prefix.expandtabs(8))
    for i, match in enumerate(matches):
        end = declaration_starts[i+1] if i+1 < len(matches) else len(text)
        content = text[match.end():end]
        content_skeleton = skeleton[match.end():end]
        command = re.search(r"(?m)^[ \t]*(?:(?:import|end|namespace|section|open|variable|universe|set_option|attribute|#\w+)|(?:(?:local|scoped)[ \t]+)*(?:notation|infixl|infixr|infix|prefix|postfix))\b", content_skeleton)
        command_inside = False
        if command:
            prefix = re.match(r"[ \t]*", command.group()).group()
            command_inside = len(prefix.expandtabs(8)) > indent(match)
            content = content[:command.start()]
            content_skeleton = content_skeleton[:command.start()]
        qualifiers = sorted(re.findall(r"\b(?:private|public|protected|meta|noncomputable|local|scoped|partial|nonrec|unsafe)\b", skeleton[match.start():match.start(1)]))
        context = digest([span for start, span in context_spans if start < match.start()])
        kind = " ".join(match.group(1).split())
        name = match.group(2) or "<anonymous>"
        escaped_name = False
        if kind != "example":
            raw_name = SOURCE_NAME.match(text, match.end(1))
            if raw_name and "«" in raw_name.group(1):
                name = raw_name.group(1)
                escaped_name = True
            elif not raw_name:
                cursor = match.end(1)
                while cursor < len(text) and text[cursor].isspace():
                    cursor += 1
                if text.startswith("«", cursor):
                    raise ValueError("unsupported escaped declaration name")
        priority = False
        if kind == "instance":
            priority_start = INSTANCE_PRIORITY.match(skeleton, match.end(1), end)
            if priority_start:
                priority = True
                cursor = priority_start.end()
                depth = 1
                while cursor < end and depth:
                    if skeleton[cursor] == "(": depth += 1
                    elif skeleton[cursor] == ")": depth -= 1
                    cursor += 1
                if depth:
                    raise ValueError("unterminated instance priority")
                priority_name = SOURCE_NAME.match(text, cursor, end)
                if priority_name:
                    name = priority_name.group(1)
                    escaped_name = "«" in name
        unsupported = kind in {"structure", "inductive", "class", "class inductive", "class abbrev", "axiom", "constant"}
        parts = None if unsupported else split_declaration(content, skeleton=content_skeleton)
        reason = ("unsupported-declaration-form" if unsupported else
                  "unsupported-instance-priority" if priority else "missing-top-level-definition")
        if parts is not None:
            head_skeleton = content_skeleton[:len(parts[0])]
            if re.search(r"\bwhere\b", head_skeleton):
                parts, reason = None, "unsupported-where-declaration"
            elif re.search(r"(?m)^[ \t]*\|", head_skeleton):
                parts, reason = None, "unsupported-equation-declaration"
        if parts is None:
            rows.append(dict(path=relative_path,
                             line=text.count("\n", 0, match.start(1))+1,
                             kind=kind, name=name,
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
        boundary = re.search(r"(?m)^[ \t]*(?:(?:import|end|namespace|section|open|variable|universe|set_option|attribute|#\w+)|(?:(?:local|scoped)[ \t]+)*(?:notation|infixl|infixr|infix|prefix|postfix))\b", body_skeleton)
        if boundary:
            prefix = re.match(r"[ \t]*", boundary.group()).group()
            if len(prefix.expandtabs(8)) > indent(match):
                body_reject_reason = "indented-command-boundary"
            body = body[:boundary.start()]
        if escaped_name:
            body_reject_reason = "escaped-identifier-boundary"
        if priority:
            body_reject_reason = "unsupported-instance-priority"
        normalized = None if escaped_name or priority else normalize(header.strip())
        rows.append(dict(path=relative_path,
                         line=text.count("\n", 0, match.start(1))+1,
                         kind=kind, name=name,
                         statement=normalized, body=tokenize(body), body_form=body_form,
                         body_reject_reason=body_reject_reason, owner="unknown", context_hash=context, qualifiers=qualifiers,
                         reject_reason=("unsupported-instance-priority" if priority else
                                        "unsupported-binder-syntax" if normalized is None else None)))
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

def selected_paths(root, pattern, errors):
    """Path.glob-style selection with explicit enumeration errors.

    Recursive ** does not follow directory symlinks and reports their omission.
    Explicit finite directory components can follow them; resolved containment
    is checked before reading.
    """
    parts = Path(pattern).parts
    directories_only = pattern.endswith("/")
    if not parts or Path(pattern).is_absolute() or ".." in parts or any("**" in p and p != "**" for p in parts):
        raise ValueError("invalid relative selection pattern: " + pattern)

    def failure(path, exc):
        error = dict(path=str(path), pattern=pattern,
                     reason="selection enumeration failed: " + str(exc))
        if error not in errors:
            errors.append(error)

    def checked_link_directory(path):
        resolved = path.resolve(strict=True)
        if not resolved.is_relative_to(root):
            raise ValueError("selected directory symlink resolves outside root")
        return stat.S_ISDIR(resolved.stat().st_mode)

    def descend(base, index):
        if index == len(parts):
            try:
                if not directories_only or base.is_dir():
                    yield base
            except OSError as exc:
                failure(base, exc)
            return
        part = parts[index]
        if part != "**" and not any(c in part for c in "*?["):
            path = base / part
            try:
                mode = path.lstat().st_mode
            except FileNotFoundError:
                return
            except OSError as exc:
                failure(path, exc)
                return
            if index + 1 == len(parts):
                yield from descend(path, index + 1)
            else:
                try:
                    is_directory = checked_link_directory(path) if stat.S_ISLNK(mode) else stat.S_ISDIR(mode)
                    if is_directory:
                        yield from descend(path, index + 1)
                except (OSError, ValueError, RuntimeError) as exc:
                    failure(path, exc)
            return
        if part == "**":
            yield from descend(base, index + 1)
        try:
            with os.scandir(base) as iterator:
                entries = sorted(iterator, key=lambda entry: entry.name)
        except OSError as exc:
            failure(base, exc)
            return
        for entry in entries:
            path = base / entry.name
            if part == "**":
                try:
                    if entry.is_symlink():
                        # Path.glob-style recursion skips directory links. A
                        # whole-scope report must not silently call that complete.
                        target = entry.stat(follow_symlinks=True)
                        if stat.S_ISDIR(target.st_mode):
                            failure(path, ValueError("recursive selection skips directory symlink"))
                    elif entry.is_dir(follow_symlinks=False):
                        yield from descend(path, index)
                except OSError as exc:
                    failure(path, exc)
            elif fnmatch.fnmatchcase(entry.name, part):
                if index + 1 == len(parts):
                    yield from descend(path, index + 1)
                else:
                    try:
                        if entry.is_symlink():
                            is_directory = checked_link_directory(path)
                        else:
                            is_directory = entry.is_dir(follow_symlinks=False)
                        if is_directory:
                            yield from descend(path, index + 1)
                    except (OSError, ValueError, RuntimeError) as exc:
                        failure(path, exc)
    yield from descend(root, 0)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--owners", type=Path, help="JSON mapping exact relative paths to owner labels")
    parser.add_argument("--previous", type=Path, help="previous scanner JSON report")
    parser.add_argument("--previous-sha256", help="caller-supplied SHA256 pin for previous report")
    parser.add_argument("--registry", type=Path, help="coordinator ownership snapshot; references are advisory")
    binding_options = parser.add_mutually_exclusive_group()
    binding_options.add_argument("--fixture-binding-output", type=Path, help="fresh live five-fixture rebuild directory; never accepts an old receipt")
    binding_options.add_argument("--source-binding-output", type=Path, help="fresh live fixture source-location binding directory; never accepts saved receipts")
    binding_options.add_argument("--project-binding-output", type=Path, help="fresh live pinned KeySort source binding; never accepts saved receipts")
    parser.add_argument("--project-binding-target", choices=("keysort","ast","scope"), help="admitted project target; requires live project output, defaults to keysort")
    args = parser.parse_args()
    if args.project_binding_target is not None and args.project_binding_output is None:
        parser.error("--project-binding-target requires --project-binding-output")
    closure_binding = args.project_binding_target in ("ast","scope")
    project_name = {"ast":"AST","scope":"Scope"}.get(args.project_binding_target,"KeySort")
    root = args.root.resolve()
    binding_output = (args.project_binding_output if args.project_binding_output is not None else
                      args.source_binding_output if args.source_binding_output is not None else args.fixture_binding_output)
    if (args.previous is None) != (args.previous_sha256 is None):
        parser.error("--previous and --previous-sha256 must be supplied together")
    if any(Path(pat).is_absolute() or ".." in Path(pat).parts for pat in args.paths):
        parser.error("patterns must stay within the root")
    selection = dict(root=str(root), patterns=sorted(set(args.paths)))
    if args.fixture_binding_output is not None:
        if root != Path(__file__).resolve().parents[4] or not args.fixture_binding_output.is_absolute():
            parser.error("fixture binding requires the real checkout root and absolute fresh output")
        if args.fixture_binding_output.exists() or args.fixture_binding_output.is_symlink():
            parser.error("fixture binding output must be fresh; saved receipts are not accepted")
        selection["fixture_binding_contract"] = hashlib.sha256((root/"tests/h62/item1/duplication-scanner/local-rebuild-pins.json").read_bytes()).hexdigest()
    if args.source_binding_output is not None:
        if root != Path(__file__).resolve().parents[4] or not args.source_binding_output.is_absolute():
            parser.error("source binding requires the real checkout root and absolute fresh output")
        if args.source_binding_output.exists() or args.source_binding_output.is_symlink():
            parser.error("source binding output must be fresh; saved receipts are not accepted")
        selection["source_binding_contract"] = hashlib.sha256((root/"tests/h62/item1/duplication-scanner/source-location-pins.json").read_bytes()).hexdigest()
    if args.project_binding_output is not None:
        if root != Path(__file__).resolve().parents[4] or not args.project_binding_output.is_absolute():
            parser.error("project binding requires the real checkout root and absolute fresh output")
        if args.project_binding_output.exists() or args.project_binding_output.is_symlink():
            parser.error("project binding output must be fresh; saved receipts are not accepted")
        project_contract = "scope-closure-pins.json" if args.project_binding_target=="scope" else "project-closure-pins.json" if closure_binding else "project-leaf-pins.json"
        selection["project_binding_contract"] = hashlib.sha256((root/"tests/h62/item1/duplication-scanner"/project_contract).read_bytes()).hexdigest()
        if closure_binding:
            selection["project_binding_target"] = "Solidity."+project_name
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
    selection_errors = []
    try:
        matched = {pat: sorted(f for f in selected_paths(root, pat, selection_errors) if f.suffix == ".lean") for pat in sorted(set(args.paths))}
    except ValueError as exc:
        parser.error(str(exc))
    unmatched = sorted(pat for pat, paths in matched.items() if not paths)
    files = sorted({f for paths in matched.values() for f in paths})
    rows, errors, inputs, aliases = [], selection_errors, [], []
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
    fixture_binding = None
    binder = None
    binding_receipt_sha = None
    if args.fixture_binding_output is not None:
        try:
            if errors or unmatched:
                raise ValueError("cannot bind incomplete selected inputs")
            import importlib.util
            spec = importlib.util.spec_from_file_location("h62_local_binder", Path(__file__).with_name("bind_signature_fixture.py"))
            binder = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(binder)
            source_path = "tests/h62/item1/duplication-scanner/SignatureFingerprint.lean"
            expected_names = {"alphaA", "alphaB", "differentType", "indexedOne", "indexedTwo"}
            selected = [r for r in rows if r["path"] == source_path and r["name"] in expected_names]
            if len(selected) != 5 or {r["name"] for r in selected} != expected_names:
                raise ValueError("selected scope must contain each of the five fixture declarations once")
            with binder.writer_lease():
                live = binder.rebuild(args.fixture_binding_output)
                binding_receipt_sha = live_receipt_hash(binder,binding_output,live)
            by_name = {binder.observer.name_parts(r["declaration"])[-1]: r for r in live["source_bindings"]}
            source_hash = next(r["sha256"] for r in inputs if r["path"] == source_path)
            for row in selected:
                binding = by_name[row["name"]]
                if binding["source_sha256"] != source_hash:
                    raise ValueError("scan source differs from live rebuilt source")
                row["fixture_signature"] = binding
            fixture_binding = {"kind": "live-canonical-five-fixture-rebuild", "records": 5,
                               "raw_environment_binding": "unbound", "compiler_sha256": live["compiler_sha256"],
                               "pins_sha256": live["pins_sha256"],
                               "coverage": signature_coverage(rows),
                               "boundary": "Only five pinned fixture rows have local source/artifact linkage; all candidate refusal/ownership checks remain. Execution receipt is external, not accepted as input."}
        except (OSError, ValueError) as exc:
            parser.error("live fixture binding: " + str(exc))
    if args.source_binding_output is not None:
        try:
            if errors or unmatched:
                raise ValueError("cannot bind incomplete selected inputs")
            source_path = "tests/h62/item1/duplication-scanner/SignatureFingerprint.lean"
            selected = [r for r in rows if r["path"] == source_path]
            if not selected:
                raise ValueError("selected scope must contain the pinned source fixture")
            import importlib.util
            spec = importlib.util.spec_from_file_location("h62_source_binder",Path(__file__).with_name("bind_source_locations.py"))
            controller = importlib.util.module_from_spec(spec); spec.loader.exec_module(controller)
            binder = controller.binder
            with binder.writer_lease():
                live = controller.run(binding_output)
                binding_receipt_sha = live_receipt_hash(binder,binding_output,live)
                linked = controller.read_bound_json(binding_output/"source-bindings.json",live["bindings_sha256"])
            attach_source_bindings(rows,inputs,linked,live,source_path)
            fixture_binding = {"kind":"live-direct-source-location-rebuild","records":linked["linked"],
                               "raw_environment_binding":"unbound","pins_sha256":live["pins_sha256"],
                               "coverage":signature_coverage(rows),
                               "visible_kernel_constants":linked["visible_kernel_total"],
                               "kernel_without_lexical_link":linked["kernel_without_lexical_link"],
                               "boundary":"Only pinned fixture source/name/type linkage. Candidate refusals and ownership checks remain; no global, private/unloaded, proof-body or attestation claim."}
        except (OSError,ValueError,RecursionError) as exc:
            parser.error("live source binding: "+str(exc))
    if args.project_binding_output is not None:
        try:
            if errors or unmatched:
                raise ValueError("cannot bind incomplete selected inputs")
            source_path = "Solidity/"+project_name+".lean"
            if not any(row["path"] == source_path for row in rows):
                raise ValueError("selected scope must contain the pinned project source")
            import importlib.util
            spec = importlib.util.spec_from_file_location("h62_project_binder",Path(__file__).with_name("bind_project_closure.py" if closure_binding else "bind_project_leaf.py"))
            controller = importlib.util.module_from_spec(spec); spec.loader.exec_module(controller)
            binder = controller.binder
            with binder.writer_lease():
                live = controller.run(binding_output,args.project_binding_target) if closure_binding else controller.run(binding_output)
                binding_receipt_sha = live_receipt_hash(binder,binding_output,live)
                source_reader = controller.leaf.source_binding if closure_binding else controller.source_binding
                linked = source_reader.read_bound_json(binding_output/"source-bindings.json",live["bindings_sha256"])
            source_live = closure_source_receipt(live,source_path) if closure_binding else live
            attach_source_bindings(rows,inputs,linked,source_live,source_path,"project_signature")
            fixture_binding = {"kind":"live-pinned-project-closure-rebuild" if closure_binding else "live-pinned-project-leaf-rebuild",
                               "project_module":"Solidity."+project_name,
                               "source_path":source_path, "records":linked["linked"],
                               "execution_binding":"trusted-live-project-closure" if closure_binding else "trusted-live-project-leaf", "pins_sha256":live["pins_sha256"],
                               "coverage":signature_coverage(rows,"project_signature","local-project-linkage"),
                               "visible_kernel_constants":linked["visible_kernel_total"],
                               "kernel_without_lexical_link":linked["kernel_without_lexical_link"],
                               "boundary":("Only pinned unchanged Scope source/name/type linkage with fresh AST and KeySort dependencies. Dependency and other selected rows remain unresolved in this Scope census; all candidate refusals and ownership checks remain. No general/private/unloaded/body-equivalence or runtime acceptance claim." if args.project_binding_target=="scope" else "Only pinned unchanged AST source/name/type linkage with fresh KeySort dependency. KeySort and other selected rows remain unresolved in this AST census; all candidate refusals and ownership checks remain. No general/private/unloaded/body-equivalence or runtime acceptance claim." if closure_binding else "Only pinned unchanged KeySort source/name/type linkage. Anonymous and other selected rows remain unresolved; all candidate refusals and ownership checks remain. No general/private/unloaded/body-equivalence or runtime acceptance claim.")}
            if closure_binding:
                fixture_binding["fresh_project_dependencies"] = live["fresh_project_closure"]
        except (OSError,ValueError,RecursionError) as exc:
            parser.error("live project binding: "+str(exc))
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
    payload = json.dumps(dict(version=2, selection=selection, inputs=inputs, declarations=len(rows), inventory=inventory, candidates=candidates, rejected_declarations=rejected,
        body_candidates=body_candidates, incremental=incremental, unmatched_patterns=unmatched, input_aliases=aliases,
        owner_config_sha256=digest(owners), registry_sha256=hashlib.sha256(registry_bytes).hexdigest(), scanner_sha256=scanner_sha256,
        rejections=dict(by_reason=rejection_counts,
                        unknown_ownership=sum(r["owner"] == "unknown" for r in rows)), errors=errors,
        **({("project_binding" if args.project_binding_output is not None else "fixture_binding"): fixture_binding} if fixture_binding is not None else {})),
        sort_keys=True, ensure_ascii=False, indent=2)
    if fixture_binding is not None:
        with binder.writer_lease():
            report_bytes = (payload + "\n").encode()
            if binder.regular(binding_output/"receipt.json")["sha256"] != binding_receipt_sha:
                parser.error("live scanner receipt changed before report sealing")
            (binding_output/"scan.json").write_bytes(report_bytes)
            (binding_output/"scan-binding.json").write_text(json.dumps({
                "canonical_scan_sha256": hashlib.sha256(report_bytes).hexdigest(),
                "live_rebuild_receipt_sha256": binding_receipt_sha,
                "scanner_sha256": scanner_sha256,
                "boundary": "Created by this scanner's live rebuild invocation; not remote attestation or authority for other signatures."}, indent=2)+"\n")
    print(payload)
    return bool(errors or unmatched)

if __name__ == "__main__":
    raise SystemExit(main())
