#!/usr/bin/env python3
"""Lossless source census, not a Lean elaborator or a semantic proof.

All RoadmapV15 sources are frozen by file hashes. Declaration statement hashes
include explicit binders, defaults and local let expressions. Anonymous examples
receive stable per-file ordinal IDs. Comments and strings cannot create commands.
The scanner refuses unsupported declaration forms instead of silently omitting
them. Bulk JSON belongs outside git (H44).
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FAMILY = Path("Bridge/SolidityBridge/RoadmapV15")
COMMAND = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
    r"(?P<kind>theorem|lemma|example|def|abbrev|structure|inductive|class|instance|opaque|axiom)\b"
    r"|^(?:namespace|section|end|open|import|export|set_option|attribute|variable|universe|mutual)\b"
    r"|^#\w+", re.M)
DECL = re.compile(
    r"(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
    r"(?P<kind>theorem|lemma|example|def|abbrev|structure|inductive|class|instance|opaque|axiom)\b"
    r"\s*(?P<name>[^\s:({\[]+)?")


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def mask(text):
    """Preserve offsets/newlines while blanking nested comments and strings."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "; i += 1
                if i < len(text):
                    if text[i] != "\n": out[i] = " "
                    i += 1
            elif text[i] == '"':
                out[i] = " "; string = False; i += 1
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out[i:end] = " " * (end-i); i = end
        elif text[i] == '"':
            out[i] = " "; string = True; i += 1
        elif text[i] == "'" and (i == 0 or not (text[i-1].isalnum() or text[i-1] in "_'")):
            char = re.match(r"'(?:\\.|[^\\'\n])'", text[i:])
            if char:
                out[i:i+len(char.group())] = " " * len(char.group()); i += len(char.group())
            else:
                i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("unterminated comment/string")
    return "".join(out)


def statement_end(code):
    """Find the declaration value separator, ignoring binder defaults/lets.

    A top-level := after the result colon starts the proof/value. Result types
    containing a top-level let ... := are handled by their let/in balance.
    The whole file hash independently freezes context and all source bytes.
    """
    stack, lets = [], 0
    tokens = re.finditer(r"\blet\b|\bin\b|:=|\bwhere\b|[(){}\[\]⟨⟩]", code)
    pairs = {')':'(', '}':'{', ']':'[', '⟩':'⟨'}
    for t in tokens:
        v = t.group()
        if v in "({[⟨": stack.append(v)
        elif v in pairs:
            if not stack or stack.pop() != pairs[v]:
                raise ValueError("unbalanced declaration delimiters")
        elif not stack:
            if v == 'let': lets += 1
            elif v == 'in' and lets: lets -= 1
            elif v == ':=':
                if lets: lets -= 1  # Lean's let binding extends to line/semicolon.
                else: return t.start()
            elif v == 'where': return t.start()
    if stack: raise ValueError('unbalanced declaration delimiters')
    return len(code.rstrip())


def declarations(text, path):
    clean = mask(text)
    commands = list(COMMAND.finditer(clean))
    supported = {c.start() for c in commands if c.group('kind')}
    # This family uses column-zero declarations. Refuse other forms explicitly.
    for candidate in re.finditer(
            r"^[ \t]*(?:@\[[^\n]*\][ \t]*)*"
            r"(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
            r"(?:theorem|lemma|example|def|abbrev|structure|inductive|class|instance|opaque|axiom)\b", clean, re.M):
        if candidate.start() not in supported:
            raise ValueError(f"unsupported indented/attributed declaration in {path}")
    rows, ordinal = [], 0
    for i, command in enumerate(commands):
        if command.group('kind') is None: continue
        start = command.start()
        end = commands[i+1].start() if i+1 < len(commands) else len(text)
        code = clean[start:end]
        parsed = DECL.match(code)
        kind = parsed.group('kind')
        ordinal += 1
        name = f"@example-{ordinal:04d}" if kind == 'example' else parsed.group('name')
        if kind == 'instance' and name is None: name = f'@instance-{ordinal:04d}'
        if not name or name == ':=': raise ValueError(f"unsupported anonymous declaration: {path}:{ordinal}")
        signature_end = len(code.rstrip()) if kind in {'structure', 'class', 'inductive'} else statement_end(code)
        signature = text[start:start+signature_end].rstrip()
        value = text[start+signature_end:end].rstrip()
        statement_code = clean[start:start+signature_end]
        flags = [label for label, pattern in (
            ('refusal-or-error', r'\.error\b|\bnone\b'),
            ('negative', r'≠|¬|\bFalse\b'),
            ('parameterized', r'\([^\n]*:'),
            ('kernel-decision-in-body', r'\bdecide\b'),
        ) if re.search(pattern, code if label == 'kernel-decision-in-body' else statement_code)]
        rows.append(dict(id=f"{path}::{name}", name=name, kind=kind,
                         private=bool(re.match(r'private\b', code)),
                         line=text.count('\n', 0, start)+1,
                         statement=signature, statement_sha256=digest(signature),
                         declaration_sha256=digest(text[start:end].rstrip()),
                         body_sha256=digest(value), candidate_flags=flags))
    if len({r['id'] for r in rows}) != len(rows):
        raise ValueError(f"duplicate declaration IDs in {path}")
    return rows


def check_commands(text, path):
    """Record trust/diagnostic/evaluation commands separately from declarations.

    Include an immediately preceding doc comment (e.g. expected #guard_msgs
    output). Following #print/#check commands have their own rows. These rows
    are not counted as semantic test cases or proved declarations.
    """
    commands = list(COMMAND.finditer(mask(text)))
    rows = []
    for i, command in enumerate(commands):
        start = command.start()
        if text[start] != '#': continue
        end = commands[i+1].start() if i+1 < len(commands) else len(text)
        prefix = text[:start]
        doc = prefix.rfind('/--')
        if doc >= 0 and not mask(prefix[doc:]).strip(): start = doc
        rows.append(dict(id=f'{path}::@command-{len(rows)+1:04d}',
                         command=command.group(), line=text.count('\n', 0, command.start())+1,
                         source_sha256=digest(text[start:end].rstrip()), source=text[start:end].rstrip()))
    return rows


def census(repo):
    files, groups = [], defaultdict(list)
    family = repo/FAMILY
    if not family.is_dir(): raise ValueError(f'missing family directory: {family}')
    sources = sorted(family.rglob('*.lean'))
    if not sources: raise ValueError(f'empty family directory: {family}')
    for source in sources:
        path = source.relative_to(repo).as_posix()
        text = source.read_bytes().decode('utf-8')
        rows = declarations(text, path)
        is_controls = source.name.endswith('Controls.lean')
        files.append(dict(path=path, source_sha256=digest(text),
                          controls_filename=is_controls, declarations=rows,
                          check_commands=check_commands(text, path)))
        for row in rows:
            if is_controls and row['private']:
                groups[(row['kind'], row['name'])].append(row['id'])
    counts = Counter(row['kind'] for f in files for row in f['declarations'])
    controls_counts = Counter(row['kind'] for f in files if f['controls_filename'] for row in f['declarations'])
    check_counts = Counter(row['command'] for f in files for row in f['check_commands'])
    return dict(schema=1, base=BASE, family=FAMILY.as_posix(),
                boundary='Lexical source inventory; flags are candidates, not semantic classifications or Lean proof.',
                summary=dict(files=len(files), controls_files=sum(f['controls_filename'] for f in files),
                             declarations=dict(sorted(counts.items())), controls_declarations=dict(sorted(controls_counts.items())),
                             check_commands=dict(sorted(check_counts.items()))),
                audit_items={
                    '9': 'Per-case/twin candidate census only; no Backend or Evm migration claimed.',
                    '11': 'Private helper name groups below are candidates; same name does not prove equivalence.',
                    '16': 'Typed fixture-table candidates in Controls; Yul Raw/vector generation excluded (H55).'},
                repeated_private_names=[dict(kind=k[0], name=k[1], declarations=v)
                                        for k,v in sorted(groups.items()) if len(v)>1], files=files)


def render(value):
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--check', action='store_true', help='compare bytes; never overwrite expected inventory')
    args = parser.parse_args()
    result = render(census(args.repo))
    if args.check:
        if args.output.read_text() != result: raise SystemExit('FAIL: frozen source inventory changed')
    else:
        if args.output.resolve().is_relative_to(args.repo.resolve()):
            raise SystemExit('H44: bulk inventory must be outside repository')
        args.output.write_text(result)
    print(render(json.loads(result)['summary']), end='')
    print('CENSUS_SOURCE_PASS (not RUNTIME_GATE_PASS)')


if __name__ == '__main__': main()
