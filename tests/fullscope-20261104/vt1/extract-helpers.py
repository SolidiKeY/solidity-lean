#!/usr/bin/env python3
"""Cut helper functions verbatim out of the saved solc IR (no compiler run).

Writes fixtures/helpers.yul: an object whose code is exactly the listed
function definitions, each a verbatim substring of its source fixture.
Usage: extract-helpers.py [--check]
"""
import sys, pathlib
here = pathlib.Path(__file__).resolve().parent
HELPERS = [("Census.unoptimized.yul", n) for n in [
    "cleanup_t_uint256", "cleanup_t_int256", "panic_error_0x11", "panic_error_0x12",
    "checked_add_t_uint256", "checked_sub_t_uint256", "checked_div_t_int256"]] + [
    ("LinkedMath.unoptimized.yul", "checked_mul_t_uint256")]

def cut(text, name):
    start = text.index(f"function {name}(")
    line_start = text.rindex("\n", 0, start) + 1
    indent = text[line_start:start]
    end = text.index("\n" + indent + "}\n", start) + len(indent) + 3
    return text[line_start:end]

chunks = []
for fixture, name in HELPERS:
    text = (here / "fixtures" / fixture).read_text()
    chunk = cut(text, name)
    # a whole definition: from its keyword to the brace at its own indent
    assert chunk.lstrip().startswith(f"function {name}(") and chunk.rstrip().endswith("}")
    chunks.append(chunk)
out = 'object "Helpers" {\n    code {\n' + "\n".join(chunks) + '    }\n}\n'
target = here / "fixtures/helpers.yul"
if "--check" in sys.argv:
    if target.read_text() != out:
        sys.exit("helpers.yul differs")
    print("HELPERS_CHECK_PASS")
    sys.exit(0)
target.write_text(out)
print(len(out), "bytes")
