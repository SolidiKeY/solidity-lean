"""Avoid Emscripten 4.0.15's linear export scan on every dlsym lookup.

Keep dlsym's export membership, stub checks, function address and symbol-index
semantics. Enumerate export indices only when adding a new function-table entry,
and reuse them while that DSO's exports remain unchanged. Missing appended names
rebuild the index. No Lean code or kernel decision is changed.
"""
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_text()
marker = "// Browser dlsym export index cache."
if marker in source:
    raise SystemExit(0)

old = """      newSymIndex = Object.keys(lib.exports).indexOf(symbol);
      if (newSymIndex == -1 || lib.exports[symbol].stub) {"""
new = """      if (!Object.prototype.hasOwnProperty.call(lib.exports, symbol) || lib.exports[symbol].stub) {"""
write = "          HEAPU64[((symbolIndex)>>3)] = BigInt(newSymIndex);"
indexed = """          // Browser dlsym export index cache.
          var indices = lib.browserSymbolIndices;
          if (!indices || !indices.has(symbol)) {
            indices = new Map(Object.keys(lib.exports).map((name, index) => [name, index]));
            lib.browserSymbolIndices = indices;
          }
          newSymIndex = indices.get(symbol);
""" + write
if source.count(old) != 1 or source.count(write) != 1:
    raise SystemExit("Pinned Emscripten dlsym implementation changed; refusing transform")
path.write_text(source.replace(old, new).replace(write, indexed))
