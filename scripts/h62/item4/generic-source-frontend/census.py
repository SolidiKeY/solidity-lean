#!/usr/bin/env python3
"""Deterministic conservative *source* inventory; no claim of elaborated types.

All Frontend Lean files and the enumerated term declaration forms are retained, including
anonymous examples. Control labels are candidates, never semantic exclusions.
Offsets index Unicode source characters; hashes cover original UTF-8 bytes.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
DECL = re.compile(r"(?m)^(?:[ \t]*)(?:(?:private|protected|noncomputable|unsafe|partial) +)*(def|theorem|lemma|example|abbrev|structure|inductive|class|instance|axiom|constant|opaque)\b")


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def mask(source):
    """Mask nested comments and string/character literals, retaining newlines.

    A single quote is a character opener only for a complete Lean char literal;
    identifiers such as Γ' and x' therefore remain untouched.
    """
    out = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith('--', i):
            j = source.find('\n', i)
            i = len(source) if j < 0 else j
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated comment')
        elif source[i] == '"':
            # Lean raw strings r###"..."### have arbitrary hash delimiters.
            raw = re.search(r'r(#+)?$', source[:i])
            if raw and (raw.start() == 0 or not source[raw.start()-1].isalnum()):
                close = '"' + (raw.group(1) or '')
                j = source.find(close, i+1)
                if j < 0:
                    raise ValueError('unterminated raw string')
                i = j + len(close)
            else:
                i += 1
                while i < len(source):
                    if source[i] == '\\':
                        i += 2
                    elif source[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise ValueError('unterminated string')
        elif source[i] == "'" and (i == 0 or not (source[i-1].isalnum() or source[i-1] in "_'")):
            char = re.match(r"'(?:[^'\\\n]|\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.))'", source[i:])
            if char:
                i += len(char.group())
            else:
                i += 1
                continue
        else:
            i += 1
            continue
        for k in range(start, min(i, len(source))):
            if source[k] != '\n':
                out[k] = ' '
    return ''.join(out)


def header_stop(tail):
    depth = 0
    lets = 0
    for i, ch in enumerate(tail):
        if ch in '([{⦃':
            depth += 1
        elif ch in ')]}⦄':
            depth -= 1
        elif depth == 0:
            left = i == 0 or not (tail[i-1].isalnum() or tail[i-1] in "_'")
            if left and re.match(r'let\b', tail[i:]):
                lets += 1
            if tail.startswith(':=', i):
                if lets:
                    lets -= 1
                else:
                    return i, 'explicit'
            if left and re.match(r'where\b', tail[i:]):
                return i, 'explicit'
            if ch == '|' and not tail[tail.rfind('\n', 0, i)+1:i].strip() and not tail.startswith('||', i):
                return i, 'equations'
    return len(tail), 'approximate-source-slice'


def mask_attributes(masked):
    out = list(masked)
    i = 0
    while i < len(masked):
        if masked.startswith('@[', i):
            start = i
            i += 2
            depth = 1
            while i < len(masked) and depth:
                if masked[i] == '[':
                    depth += 1
                elif masked[i] == ']':
                    depth -= 1
                i += 1
            for k in range(start, i):
                if out[k] != '\n':
                    out[k] = ' '
        else:
            i += 1
    return ''.join(out)


def declarations(source):
    masked = mask_attributes(mask(source))
    starts = list(DECL.finditer(masked))
    result = []
    for ordinal, match in enumerate(starts):
        start = match.start()
        # Header ends at := or where, outside comments and literal contents.
        # Full source is retained to allow independent correction of this
        # conservative lexical boundary (not a Lean environment type hash).
        limit = starts[ordinal+1].start() if ordinal+1 < len(starts) else len(source)
        tail = masked[match.end():limit]
        offset, boundary = header_stop(tail)
        stop = match.end() + offset
        header = source[start:stop].strip()
        name = re.match(r"\s*([^\s:(⦃{]+)", masked[match.end():limit])
        result.append(dict(ordinal=ordinal, kind=match.group(1),
                           name=None if match.group(1) == 'example' else (name.group(1) if name else None),
                           line=source.count('\n', 0, start)+1,
                           source_header=header, source_header_sha256=sha(header), boundary=boundary))
    return result


def inventory(repo):
    files = []
    if not (repo / 'Solidity/Frontend').is_dir():
        raise ValueError('missing Frontend scope directory')
    for path in sorted((repo / 'Solidity/Frontend').rglob('*.lean')):
        source = path.read_text()
        rel = path.relative_to(repo).as_posix()
        rows = declarations(source)
        candidate = bool(re.search(r'Controls|Checks|Examples|Counterexamples|WordTable', rel))
        files.append(dict(path=rel, sha256=sha(source), control_candidate=candidate,
                          audit_items=[16] if ('FixtureControls/' in rel or '/WordTable/' in rel) else [],
                          declarations=rows))
    return dict(schema=1, base=BASE, scope='Solidity/Frontend/**/*.lean',
                boundary='lexical source headers; not elaborated statement hashes', files=files,
                audit_applicability={'9': 'Backend/Evm twins; no owned Frontend migration authorized',
                                     '11': 'Backend/Evm shared lemmas; no owned Frontend migration authorized',
                                     '16': '45 StatementGrammarH28 cases; 30 NumericLiteralProofs WordTable parts; requireTyped at Source/Progress/{LiteralBuiltinControls,BuiltinControls}.lean is outside sole Frontend scope and remains owner-owned; Yul Raw producer reserved H55'})


def encode(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    value = inventory(args.repo)
    data = encode(value)
    if args.check:
        if args.output.read_text() != data:
            raise SystemExit('CENSUS_DRIFT')
    else:
        args.output.write_text(data)
    rows = sum(len(f['declarations']) for f in value['files'])
    controls = [f for f in value['files'] if f['control_candidate']]
    print(encode(dict(files=len(value['files']), declarations=rows,
                      control_candidate_files=len(controls),
                      control_candidate_declarations=sum(len(f['declarations']) for f in controls),
                      inventory_sha256=sha(data))))


if __name__ == '__main__':
    main()
