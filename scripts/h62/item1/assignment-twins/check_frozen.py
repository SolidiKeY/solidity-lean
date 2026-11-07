#!/usr/bin/env python3
"""Conservative text guard for the six assignment twin files; not a Lean parser."""
from collections import Counter
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
DIRECTORY = "Solidity/Backend/Passes"
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(def|abbrev|theorem|lemma)\s+([^\s:{(]+)", re.MULTILINE)


def body_start(text, start, end):
    """Find top-level :=, skipping strings, line comments and nested block comments."""
    stack = []
    blocks = 0
    string = False
    i = start
    while i < end - 1:
        pair = text[i:i+2]
        if blocks:
            if pair == "/-": blocks += 1; i += 2; continue
            if pair == "-/": blocks -= 1; i += 2; continue
        elif string:
            if text[i] == "\\": i += 2; continue
            if text[i] == '"': string = False
        elif pair == "/-": blocks = 1; i += 2; continue
        elif pair == "--":
            newline = text.find("\n", i, end)
            i = end if newline < 0 else newline + 1
            continue
        elif text[i] == '"': string = True
        elif text[i] in "([{": stack.append(text[i])
        elif text[i] in ")]}":
            if not stack or "([{"[")]}".index(text[i])] != stack.pop():
                raise ValueError("unbalanced delimiter")
        elif pair == ":=" and not stack: return i
        elif text[i] == "|" and not stack and text[text.rfind("\n", start, i)+1:i].strip() == "": return i
        i += 1
    raise ValueError("declaration has no top-level :=")


def inventory(text):
    matches = list(DECL.finditer(text))
    result = []
    for n, match in enumerate(matches):
        end = matches[n+1].start() if n+1 < len(matches) else len(text)
        body = body_start(text, match.start(), end)
        kind, name = match.groups()
        # Theorems may change only after :=; definitions and abbreviations remain byte-identical.
        frozen = text[match.start():body] if kind in ("theorem", "lemma") else text[match.start():end]
        result.append((kind, name, frozen))
    return result


COMMAND = re.compile(r"^\s*(?:import|open|namespace|section|end|include|omit|axiom|opaque|constant|set_option|attribute|export|local|universe|universes|variable|variables|notation|infix|infixl|infixr|syntax|macro|instance|class|inductive|structure)\b[^\n]*|^\s*#[^\n]*", re.MULTILINE)


# Raw textual indicators are intentionally conservative, including comments/strings.
TRUST = re.compile(r"\b(?:sorry|sorryAx|admit|native_decide|ofReduceBool|unsafe|run_tac|axiom)\b")


def frozen_view(text):
    # Conservative extra check for common commands outside our declaration grammar.
    declarations = list(DECL.finditer(text))
    commands = [(sum(d.start() < c.start() for d in declarations), c.group())
                for c in COMMAND.finditer(text)]
    return inventory(text), commands, Counter(TRUST.findall(text))


def paths():
    for op in ("Addition", "Multiplication", "Subtraction"):
        for kind in ("Pass", "Controls"):
            yield f"{DIRECTORY}/Assignment{op}{kind}.lean"


def main():
    failed = False
    for path in paths():
        old = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT, text=True)
        new = (ROOT / path).read_text()
        before, after = frozen_view(old), frozen_view(new)
        if before != after:
            print(f"CHANGED: {path}")
            failed = True
        else:
            print(f"UNCHANGED: {path} ({len(before[0])} declarations)")
    print("Text heuristic only: trust indicators include comments/strings and cannot establish Lean types, axiom sets or semantics.")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
