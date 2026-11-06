"""Keep the server-test CLI out of native WASM; preserve its exact Lean IR.

These 16 functions form the reverse call closure of two enormous generated
interactive-test loops. They are unreachable from the module initializer and
have no callers in other standard-library modules. Keeping them internal lets
Clang omit them without changing the initializer or other exported functions.
The browser frontend imports full private IR, so interpretation remains available.
"""
import re
import sys

source = open(sys.argv[1], encoding="utf8").read()
names = {
    "l_Lean_Server_Test_Runner_main",
    "l_Lean_Server_Test_Runner_main___boxed",
    "l_Lean_Server_Test_Runner_main___lam__0",
    "l_Lean_Server_Test_Runner_main___lam__0___boxed",
}
for base in [
    "l_List_forIn_x27_loop___at___Lean_Server_Test_Runner_main_spec__41",
    "l_List_forIn_x27_loop___at___Lean_Server_Test_Runner_main_spec__46",
    "l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Server_Test_Runner_main_spec__41_spec__41",
]:
    names.update(base + suffix for suffix in ["", "___boxed", "___redArg", "___redArg___boxed"])
pattern = re.compile(r"(?m)^LEAN_EXPORT ([^\n]*?\b)(" + "|".join(map(re.escape, sorted(names, key=len, reverse=True))) + r")(\()")
found = {match.group(2) for match in pattern.finditer(source)}
if found != names:
    raise SystemExit("Pinned Lean runner C changed; refusing an incomplete transform")
filtered = pattern.sub(lambda match: "static " + match.group(1) + match.group(2) + match.group(3), source)
if "LEAN_EXPORT lean_object* initialize_Lean_Server_Test_Runner(" not in filtered:
    raise SystemExit("Runner initializer must remain exported")
with open(sys.argv[2], "w", encoding="utf8") as output:
    output.write(filtered)
