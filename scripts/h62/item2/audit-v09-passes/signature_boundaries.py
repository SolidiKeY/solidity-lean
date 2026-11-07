#!/usr/bin/env python3
"""Supplemental source header boundaries; never replace the legacy census.

Regression: equation-style theorem bodies consumed the next declaration's :=.
This bounded recognizer is not Lean parsing/elaboration. Ambiguous match/quoted
identifier forms are refused explicitly; no feasibility or proof is inferred.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
from census import BASE, MAP, DECL, declarations, masked, sha


def header(text, start, name_end, stop):
    clean = masked(text)
    stack, pending_lets = [], 0
    has_colon = False
    i = name_end
    while i < stop:
        ch = clean[i]
        if ch == '«':
            return {"status": "unresolved", "reason": "quoted-identifier-before-body"}
        word = re.match(r"[A-Za-z_][A-Za-z_0-9']*", clean[i:]) if (i == 0 or not (clean[i-1].isalnum() or clean[i-1] in "_'.")) else None
        if not stack and word:
            if word.group() == "match":
                return {"status": "unresolved", "reason": "top-level-match-before-body"}
            if word.group() == "let":
                pending_lets += 1
        if not stack and clean.startswith(":=", i):
            if pending_lets:
                pending_lets -= 1
                i += 2
                continue
            return record(text, start, i, "assignment")
        if not stack and ch == ':':
            has_colon = True
        line_start = clean.rfind('\n', 0, i) + 1
        if not stack and ch == '|' and not clean[line_start:i].strip():
            if has_colon and not pending_lets and i+1 < stop and clean[i+1].isspace():
                return record(text, start, i, "equations")
            return {"status": "unresolved", "reason": "ambiguous-leading-pipe"}
        if ch in "([{":
            stack.append(ch)
        elif ch in ")]}":
            if not stack or {")": "(", "]": "[", "}": "{"}[ch] != stack.pop():
                return {"status": "unresolved", "reason": "unbalanced-header"}
        i += 1
    return {"status": "unresolved", "reason": "no-body-before-next-declaration-or-eof"}


def record(text, start, end, kind):
    value = text[start:end].strip()
    return {"status": "recognized-source-header", "body_kind": kind,
            "character_span": [start, end], "header": value,
            "header_sha256": sha(value.encode())}


def supplement(path, text):
    matches = list(DECL.finditer(masked(text)))
    old = declarations(path, text)
    if len(matches) != len(old):
        raise ValueError("legacy declaration membership differs")
    out = []
    for index, (match, row) in enumerate(zip(matches, old)):
        stop = matches[index+1].start() if index+1 < len(matches) else len(text)
        item = {"name": row["name"], "path": path,
                "legacy_signature_sha256": row["signature_sha256"],
                "legacy_character_span": row["character_span"],
                **header(text, match.start(), match.end(), stop)}
        item['differs_from_legacy'] = (item.get('header_sha256') != row['signature_sha256']) if item['status'] == 'recognized-source-header' else None
        out.append(item)
    return out


def frozen_report(root):
    def frozen(path):
        return subprocess.check_output(['git', 'show', BASE+':'+path], cwd=root)
    module_map = frozen(MAP)
    named = set(re.findall(r'`(Backend/Passes/[A-Za-z0-9]+\.lean)`', module_map.decode()))
    if 'Other `Backend/Passes/*Controls.lean` and `*Pins.lean`' not in module_map.decode():
        raise ValueError('frozen wildcard changed')
    tree = subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,'Solidity/Backend/Passes'], cwd=root, text=True).splitlines()
    paths = {'Solidity/'+x for x in named} | {x for x in tree if x.endswith(('Controls.lean','Pins.lean'))}
    rows = [r for p in sorted(paths) for r in supplement(p, frozen(p).decode())]
    keys = [(r['path'],r['name']) for r in rows]
    if len(set(keys)) != len(keys):
        raise ValueError('duplicate source identity')
    return {'schema_version':1,'frozen_base':BASE,'files':len(paths),'rows':rows,
            'summary':{'rows':len(rows),'recognized':sum(r['status']=='recognized-source-header' for r in rows),
                       'unresolved':sum(r['status']=='unresolved' for r in rows),
                       'changed_boundaries':sum(r['differs_from_legacy'] is True for r in rows)},
            'limit':'Supplemental source recognition only. Legacy census unchanged. Not a Lean parser, elaborated identity census, statement equivalence proof or witness coverage.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[4]
    result = frozen_report(root)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
    print(json.dumps(result['summary'], sort_keys=True))


if __name__ == '__main__':
    main()
