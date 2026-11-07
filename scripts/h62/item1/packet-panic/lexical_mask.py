"""Shared offset-preserving lexical mask; not a Lean parser."""
import re

def mask_comments_and_strings(source, mask_attributes=True):
    """Mask nested comments, line comments, and strings without shifting lines."""
    chars = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                chars[i:i + 2] = "  "
                i += 2
            elif pair == "-/":
                depth -= 1
                chars[i:i + 2] = "  "
                i += 2
            else:
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
        elif string:
            if source[i] == "\\" and i + 1 < len(source):
                chars[i] = " "
                if source[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
            else:
                if source[i] == chr(34):
                    string = False
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
        elif pair == "--":
            while i < len(source) and source[i] != "\n":
                chars[i] = " "
                i += 1
        elif pair == "/-":
            depth = 1
            chars[i:i + 2] = "  "
            i += 2
        elif source[i] == "!" and re.match(r'![ \t\r\n]*(?:/\-|--|(?:r#*)?")', source[i:]):
            raise ValueError("possible interpolated string syntax is unsupported by the lexical mask")
        elif source[i] == "r" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_\'")) and (raw := re.match(r'r(#+)?"', source[i:])):
            closing = '"' + (raw.group(1) or "")
            end = source.find(closing, i + len(raw.group()))
            if end < 0:
                raise ValueError("unterminated raw string")
            end += len(closing)
            for j in range(i, end):
                if source[j] != "\n":
                    chars[j] = " "
            i = end
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            char = re.match(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|.)|[^'\\\n])'", source[i:])
            if char:
                end = i + len(char.group())
                chars[i:end] = " " * (end - i)
                i = end
            else:
                i += 1
        elif source[i] == chr(34):
            string = True
            chars[i] = " "
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    masked = "".join(chars)
    if not mask_attributes:
        return masked
    i = 0
    while i < len(masked):
        if masked[i:i + 2] != "@[":
            i += 1
            continue
        start = i
        depth = 1
        i += 2
        while i < len(masked) and depth:
            if masked[i] == "[":
                depth += 1
            elif masked[i] == "]":
                depth -= 1
            i += 1
        if depth:
            raise ValueError("unterminated attribute")
        for j in range(start, i):
            if masked[j] != "\n":
                chars[j] = " "
    return "".join(chars)
