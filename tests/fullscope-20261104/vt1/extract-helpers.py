#!/usr/bin/env python3
"""Cut helper functions verbatim out of the saved solc IR (no compiler run).

Writes fixtures/helpers.yul (checked arithmetic), fixtures/exp-helpers.yul
(the checked_exp group), fixtures/abi-helpers.yul (uint256 calldata decoding) and
fixtures/push-helpers.yul (storage array push): objects whose code is exactly the listed function
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

ABI_HELPERS = [("Census.unoptimized.yul", n) for n in [
    "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b",
    "cleanup_t_uint256", "validator_revert_t_uint256", "abi_decode_t_uint256", "abi_decode_tuple_t_uint256"]]
PUSH_HELPERS = [("Census.unoptimized.yul", n) for n in [
    "cleanup_t_uint256", "panic_error_0x41", "panic_error_0x32",
    "array_length_t_array$_t_uint256_$dyn_storage_ptr", "array_dataslot_t_array$_t_uint256_$dyn_storage_ptr",
    "storage_array_index_access_t_array$_t_uint256_$dyn_storage_ptr", "shift_left_dynamic",
    "update_byte_slice_dynamic32", "identity", "convert_t_uint256_to_t_uint256", "prepare_store_t_uint256",
    "update_storage_value_t_uint256_to_t_uint256", "array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr"]]

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
           "fixtures/exp-helpers.yul": build(EXP_HELPERS, "ExpHelpers"),
           "fixtures/abi-helpers.yul": build(ABI_HELPERS, "AbiHelpers"),
           "fixtures/push-helpers.yul": build(PUSH_HELPERS, "PushHelpers")}
if "--check" in sys.argv:
    for path, out in outputs.items():
        if (here / path).read_text() != out:
            sys.exit(f"{path} differs")
    print("HELPERS_CHECK_PASS")
    sys.exit(0)
for path, out in outputs.items():
    (here / path).write_text(out)
    print(path, len(out), "bytes")
