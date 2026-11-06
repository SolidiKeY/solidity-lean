#!/usr/bin/env python3
"""Cut helper functions verbatim out of the saved solc IR (no compiler run).

Writes fixtures/helpers.yul (checked arithmetic) and fixtures/exp-helpers.yul
(the checked_exp group): objects whose code is exactly the listed function
definitions, each a verbatim substring of its source fixture.
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

EXP_HELPERS = [("Census.unoptimized.yul", n) for n in [
    "cleanup_t_uint256", "panic_error_0x11", "shift_right_1_unsigned", "checked_exp_helper",
    "checked_exp_unsigned", "checked_exp_t_uint256_t_uint256"]]

def build(helpers, name):
    chunks = []
    for fixture, fn in helpers:
        text = (here / "fixtures" / fixture).read_text()
        chunk = cut(text, fn)
        # a whole definition: from its keyword to the brace at its own indent
        assert chunk.lstrip().startswith(f"function {fn}(") and chunk.rstrip().endswith("}")
        chunks.append(chunk)
    return f'object "{name}" {{\n    code {{\n' + "\n".join(chunks) + '    }\n}\n'

outputs = {"fixtures/helpers.yul": build(HELPERS, "Helpers"),
           "fixtures/exp-helpers.yul": build(EXP_HELPERS, "ExpHelpers")}
if "--check" in sys.argv:
    for path, out in outputs.items():
        if (here / path).read_text() != out:
            sys.exit(f"{path} differs")
    print("HELPERS_CHECK_PASS")
    sys.exit(0)
for path, out in outputs.items():
    (here / path).write_text(out)
    print(path, len(out), "bytes")
