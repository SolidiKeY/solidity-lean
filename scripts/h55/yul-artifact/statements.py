#!/usr/bin/env python3
"""Conservative surface-signature check against the pinned base.
This supplements Lean checking and owner review; identical text alone does not
establish equal elaborated types when imports, notation or variables change.
"""
import argparse, json, pathlib, re, subprocess
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'

def mask_comments(source):
    chars=list(source)
    i=0
    depth=0
    quoted=False
    while i < len(source):
        pair=source[i:i+2]
        if depth:
            if pair == '/-':
                depth+=1
                chars[i:i+2]='  '
                i+=2
            elif pair == '-/':
                depth-=1
                chars[i:i+2]='  '
                i+=2
            else:
                if source[i] != '\n': chars[i]=' '
                i+=1
        elif quoted:
            if source[i] == '\\':
                chars[i]=' '
                if i+1 < len(source) and source[i+1] != '\n': chars[i+1]=' '
                i+=2
            elif source[i] == '"': chars[i]=' '; quoted=False; i+=1
            else:
                if source[i] != '\n': chars[i]=' '
                i+=1
        elif pair == '/-':
            depth=1; chars[i:i+2]='  '; i+=2
        elif pair == '--':
            end=source.find('\n',i)
            if end == -1: end=len(source)
            chars[i:end]=' '*(end-i)
            i=end
        elif source[i] == '"': chars[i]=' '; quoted=True; i+=1
        else: i+=1
    if depth or quoted: raise ValueError('unterminated comment/string')
    return ''.join(chars)

def signatures(source):
    masked=mask_comments(source)
    found={}
    pattern=r'(?m)^[ \t]*(?:(?:private|protected) +)*(?:theorem|lemma) +([^\s:{(]+)'
    for match in re.finditer(pattern,masked):
        name=match.group(1)
        stack=[]
        quoted=False
        i=match.end()
        while i < len(masked):
            c=masked[i]
            if quoted:
                if c == '\\': i+=2; continue
                if c == '"': quoted=False
            elif c == '"': quoted=True
            elif not stack and (i == 0 or not (masked[i-1].isalnum() or masked[i-1] in "_'.")) and re.match(r'\b(?:let|have)\b', masked[i:]):
                raise ValueError('unsupported top-level let/have in theorem type: '+name)
            elif not stack and masked[i:i+2] == ':=':
                break
            elif c in '({[': stack.append(c)
            elif c in ')}]':
                if not stack or '({['[')}]'.index(c)] != stack.pop():
                    raise ValueError('unbalanced theorem header: '+name)
            i+=1
        else: raise ValueError('missing proof separator: '+name)
        # Qualify duplicate local names with their occurrence number. Namespace
        # changes require owner review separately, as do notation and imports.
        occurrence=sum(1 for key in found if key.split('#')[0] == name)
        found[name+'#'+str(occurrence)]=source[match.start():i].strip()
    return found

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths',nargs='+')
    parser.add_argument('--base',default=BASE)
    args=parser.parse_args()
    root=pathlib.Path(__file__).resolve().parents[3]
    result=[]
    failed=False
    for path in args.paths:
        before=subprocess.check_output(['git','show',args.base+':'+path],cwd=root,text=True)
        old=signatures(before)
        new=signatures((root/path).read_text())
        missing=sorted(set(old)-set(new))
        changed=sorted(key for key in old.keys() & new.keys() if old[key] != new[key])
        failed |= bool(missing or changed)
        result.append(dict(path=path,baseline_theorems=len(old),missing=missing,changed=changed,
            added=sorted(set(new)-set(old))))
    print(json.dumps(dict(base=args.base,surface_signatures_preserved=not failed,files=result),indent=2))
    return int(failed)
if __name__ == '__main__': raise SystemExit(main())
