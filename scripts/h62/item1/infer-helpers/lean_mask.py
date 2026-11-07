"""Mask ordinary Lean comments and strings while preserving offsets.

This is a conservative scanner, not a complete Lean lexer. An unfinished
block comment or ordinary string is rejected. Raw/interpolated strings and
quoted identifiers are outside its supported input grammar.
"""
import re

def mask(text):
    result = list(text)
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(text):
        c = text[i]
        nxt = text[i:i + 2]
        if line:
            if c == "\n":
                line = False
            else:
                result[i] = " "
            i += 1
        elif depth:
            if nxt == "/-":
                result[i:i + 2] = "  "
                depth += 1
                i += 2
            elif nxt == "-/":
                result[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if c != "\n": result[i] = " "
                i += 1
        elif string:
            if c == "\\" and i + 1 < len(text):
                result[i] = " "
                if text[i + 1] != "\n": result[i + 1] = " "
                i += 2
            else:
                if c != "\n": result[i] = " "
                if c == chr(34): string = False
                i += 1
        elif nxt == "--":
            result[i:i + 2] = "  "
            line = True
            i += 2
        elif nxt == "/-":
            result[i:i + 2] = "  "
            depth = 1
            i += 2
        elif c == chr(34):
            result[i] = " "
            string = True
            i += 1
        elif c == "«" or re.match(r"(?:r#+|[A-Za-z_][A-Za-z_0-9]*!)\"", text[i:]):
            raise ValueError("unsupported Lean quoted identifier, raw string or interpolated string")
        else:
            i += 1
    if depth or string:
        raise ValueError("unterminated block comment or string")
    return "".join(result)
