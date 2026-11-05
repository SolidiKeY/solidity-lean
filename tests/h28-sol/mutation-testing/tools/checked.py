"""Validate successful Lean witness output; diagnostics alone cannot kill."""
import json
import re

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def messages(log):
    out = []
    for line in log.splitlines():
        if not line.strip() or line.startswith(("H28_MEASURE ", "H28_CGROUP_PEAK_BYTES=")):
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            raise ValueError("non-JSON compiler output: " + line)
        if (not isinstance(msg, dict) or msg.get("severity") not in ("information", "warning", "error")
                or not isinstance(msg.get("data"), str)):
            raise ValueError("malformed Lean diagnostic")
        out.append(msg)
    return out


def success(result, log, declarations=()):
    if result["kind"] != "exit" or result["exit"] != 0:
        raise ValueError("Lean did not successfully finish")
    parsed = messages(log)
    if any(m["severity"] in ("error", "warning") for m in parsed):
        raise ValueError("Lean error/warning in successful proof check")
    if "sorryAx" in log:
        raise ValueError("untrusted placeholder axiom")
    axioms, signatures = {}, {}
    for declaration in declarations:
        entries = [m["data"] for m in parsed if m["data"].startswith("'" + declaration + "' ")]
        if len(entries) != 1:
            raise ValueError("missing or duplicate axiom signature: " + declaration)
        info = entries[0]
        if info == "'" + declaration + "' does not depend on any axioms":
            deps = []
        else:
            match = re.fullmatch(re.escape("'" + declaration + "' depends on axioms: ") + r"\[(.*)\]", info)
            if not match:
                raise ValueError("malformed axiom signature")
            deps = match[1].split(", ") if match[1] else []
        if not set(deps) <= ALLOWED_AXIOMS:
            raise ValueError("unexpected axiom dependency")
        checks = [m["data"] for m in parsed if m["data"].startswith((declaration + " :", "@" + declaration + " :"))]
        if len(checks) != 1:
            raise ValueError("missing or duplicate theorem signature: " + declaration)
        axioms[declaration], signatures[declaration] = deps, checks[0]
    return {"axioms": axioms, "signatures": signatures}


def source_link_rejection(result, log, file, line):
    if result["kind"] != "exit" or result["exit"] != 1:
        raise ValueError("not a normal Lean rejection")
    parsed = messages(log)
    errors = [m for m in parsed if m["severity"] == "error"]
    if len(errors) != 1 or any(m["severity"] == "warning" for m in parsed):
        raise ValueError("unexpected rejection diagnostics")
    error = errors[0]
    if error["fileName"] != file or error["pos"]["line"] != line or not error["data"].startswith("Type mismatch"):
        raise ValueError("rejection not attributed to the source-link theorem")
    if "Taclet." not in error["data"]:
        raise ValueError("source-link error does not name a production constructor")
    return {"file": file, "line": line, "diagnostic": error["data"]}


def oracle_code(source):
    """Conservative owned format: no strings/quoted identifiers/quotations.

    Comments are lexical and nested, with line boundaries preserved. Refusing
    literal syntax before scanning prevents comment delimiters hiding code.
    """
    if any(char in source for char in ('"', '«', '»', '\x00')):
        raise ValueError("literal/quoted identifier syntax is outside the owned oracle format")
    out, depth, index = [], 0, 0
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            index += 2
        elif pair == "--":
            stop = source.find("\n", index)
            if stop == -1:
                stop = len(source)
            out.extend(" " * (stop - index))
            index = stop
        else:
            out.append(source[index])
            index += 1
    if depth:
        raise ValueError("unterminated owned oracle comment")
    clean = "".join(out)
    if "`" in clean or re.search(r"\bexample\b", clean):
        raise ValueError("quotation/anonymous proof is outside the owned oracle format")
    return clean


def all_owned_axioms(result, log, source):
    """Inventory every theorem of an owned single-namespace oracle source."""
    success(result, log)
    clean = oracle_code(source)
    namespaces = re.findall(r"^namespace (H28\.[A-Za-z0-9_]+)\s*$", clean, re.M)
    if len(namespaces) != 1:
        raise ValueError("expected one owned oracle namespace")
    names = re.findall(r"^theorem ([A-Za-z0-9_]+)\b", clean, re.M)
    if not names or len(names) != len(set(names)):
        raise ValueError("missing or duplicate owned theorem inventory")
    if len(re.findall(r"\btheorem\b", clean)) != len(names):
        raise ValueError("unrecognized owned theorem declaration form")
    printed = re.findall(r"^#print axioms ([A-Za-z0-9_]+)\s*$", clean, re.M)
    if sorted(printed) != sorted(names):
        raise ValueError("every owned theorem must have exactly one axiom export")
    inventory = {}
    parsed = messages(log)
    for name in names:
        qualified = namespaces[0] + "." + name
        entries = [m["data"] for m in parsed if m["data"].startswith("'" + qualified + "' ")]
        if len(entries) != 1:
            raise ValueError("missing or duplicate owned theorem axiom output")
        entry = entries[0]
        if entry == "'" + qualified + "' does not depend on any axioms":
            deps = []
        else:
            match = re.fullmatch(re.escape("'" + qualified + "' depends on axioms: ") + r"\[(.*)\]", entry)
            if not match:
                raise ValueError("malformed owned theorem axiom output")
            deps = match[1].split(", ") if match[1] else []
        if not set(deps) <= ALLOWED_AXIOMS:
            raise ValueError("unexpected axiom in owned helper theorem")
        inventory[qualified] = deps
    return inventory
