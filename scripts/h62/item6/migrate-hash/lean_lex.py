"""Nested Lean comment/string scanning shared by the migration census and full gate."""
def strip_comments(s):
    # Lean nested block comments, preserving line positions and strings.
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        pair = s[i:i+2]
        if depth:
            if pair == "/-": depth += 1; out.extend("  "); i += 2; continue
            if pair == "-/": depth -= 1; out.extend("  "); i += 2; continue
            out.append("\n" if s[i] == "\n" else " "); i += 1; continue
        if string:
            out.append(s[i])
            if s[i] == "\\" and i+1 < len(s): out.append(s[i+1]); i += 2; continue
            if s[i] == '"': string = False
            i += 1; continue
        if pair == "/-": depth = 1; out.extend("  "); i += 2; continue
        if pair == "--":
            j = s.find("\n",i)
            if j == -1: j = len(s)
            out.extend(" "*(j-i)); i = j; continue
        if s[i] == '"': string = True
        out.append(s[i]); i += 1
    assert depth == 0 and not string
    return "".join(out)
