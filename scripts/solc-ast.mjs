#!/usr/bin/env node
/**
 * solc-ast — solc's AST of solkey's `TestSuite.sol`, as the fixture
 * `tests/solc/TestSuite.ast.json` that `solc_import` reads at elaboration
 * time (`Solidity/Frontend/Import.lean`).
 *
 * The compiler is the one solkey pins: `soljson-v0.8.34+commit.80d5c536.js`
 * from a solkey checkout's `keyext.solidity.core/build/soljson/`, its sha256
 * checked against `ext.soljsonSha256` in that checkout's
 * `keyext.solidity.core/build.gradle`.  It runs under node with
 * `--standard-json` input and `outputSelection {"*": {"": ["ast"]}}`, as
 * solkey's `SolcWrapper` calls it; the negative ids of builtins, which the
 * 32-bit WebAssembly build prints unsigned, are restored the same way.
 *
 * The AST is trimmed to what a reader needs: node types, names, operators,
 * literals (`value`, `kind`, `subdenomination`), `typeDescriptions.typeString`,
 * `referencedDeclaration` and the `id` of a declaration it points to,
 * documentation text, and `src` with the 1-based source `line` it starts at
 * on every statement and declaration.  The rest (`isPure`, name locations,
 * primitive `typeIdentifier`, …) is noise that changes with unrelated edits.
 * Modern fixtures retain scalar UDVT type identifiers for nominal operator checks.  A
 * function's `modifiers` and a contract's `baseContracts` are kept when they
 * are not empty: the import refuses what it would otherwise drop.
 *
 * The fixture starts with a header `{solcVersion, sourceSha256,
 * solkeyCommit, source}`.  Lake does not track a data file, so the module
 * that imports it names its hash (`hash 0x…`, FNV-1a 64 over the file's
 * bytes): the import refuses a fixture of another hash, and this script
 * rewrites the literal, which makes Lake re-check the module.
 *
 * A loop (`while`, `for`, `do … while`) keeps the `/// @custom:key` clauses
 * of the `///` lines directly above it as `loopSpec`, the text after the tag
 * each: solc drops them, and solkey reads them from the source by the loop's
 * `src` offset (`SolJSONParser.loopSpec`), as this does: only where the
 * loop starts its line, the `///` lines joined and split at a line that
 * starts with a tag, a line without one continuing the clause before it,
 * whitespace collapsed (`KeyNatspec.of`).  A loop takes `invariant` and
 * `decreases`, as in solkey, and `unwind`, Lean's own bound on the
 * unwinding, which solkey rejects.
 *
 * Usage: node scripts/solc-ast.mjs [--solkey <checkout>] [--soljson <dir>] [--source <file>]
 *          [--out <file>] [--wrapper <module>] [--no-wrapper]
 *   --solkey      the solkey checkout (default ../solkey, or SOLKEY_ROOT)
 *   --soljson     the directory holding the pinned soljson (default the
 *                 checkout's `keyext.solidity.core/build/soljson`; a fresh
 *                 clone has none, so point it at another checkout's)
 *   --compiler-file  an explicitly selected soljson file; requires --compiler-sha256
 *   --compiler-sha256  the selected compiler's exact SHA-256 (default remains SolKeY's pin)
 *   --source      the source: an absolute path, else a path in this repository if
 *                 there is one, else in the checkout (default
 *                 keyext.solidity.examples/TestSuite.sol);
 *                 another one is another fixture (`Solidity/Solkey/Constructors.lean`),
 *                 and needs --out
 *   --out         where to write the fixture (default tests/solc/TestSuite.ast.json)
 *   --wrapper     the importing module (default Solidity/Solkey/TestSuite.lean):
 *                 the literal rewritten is the one of the import of `--out`'s file
 *   --no-wrapper  leave the importing module's hash literal alone
 *   --world-metadata  retain explicit abstractness for strict world admission
 *   --compare-cache  also compare the trimmed AST with solkey's own cached solc
 *                 output for the same source (`~/.cache/solkey/solc/<soljson>/`,
 *                 keyed by the sha256 of `SolcWrapper`'s input), when there is one
 *   --legacy-fixture  preserve historical trimming and its four-field header
 *   --via-ir      record the IR pipeline (effective ABI coder v2)
 *   --evm-version  explicit EVM target (modern default osaka)
 *
 * Modern output records an exact supported compiler pin, source digest,
 * accepted pragmas, explicit settings and AST-analysis validation stage.
 * This is external-analysis provenance, not compiler-equivalence evidence.
 *
 * The loops fixture:
 *   node scripts/solc-ast.mjs --solkey <clone at the pin> --soljson <dir> \
 *     --source tests/solc/Loops.sol --out tests/solc/Loops.ast.json \
 *     --wrapper Solidity/Examples/Tactics/LoopsImport.lean
 */

import { readFileSync, writeFileSync, mkdirSync, existsSync } from "node:fs";
import { join, dirname, isAbsolute, resolve } from "node:path";
import { createHash } from "node:crypto";
import { createRequire } from "node:module";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const args = process.argv.slice(2);
const legacyFixture = args.includes("--legacy-fixture");
const optionOf = (flag, fallback) => {
  const i = args.indexOf(flag);
  return i >= 0 && args[i + 1] ? args[i + 1] : fallback;
};

const ROOT = join(dirname(fileURLToPath(import.meta.url)), "..");
const SOLKEY = resolve(optionOf("--solkey", process.env.SOLKEY_ROOT || join(ROOT, "../solkey")));
const OUT_ARG = optionOf("--out", null);
const OUT = OUT_ARG ?? join(ROOT, "tests/solc/TestSuite.ast.json");
const WRAPPER = optionOf("--wrapper", join(ROOT, "Solidity/Solkey/TestSuite.lean"));
const SOURCE = optionOf("--source", "keyext.solidity.examples/TestSuite.sol");
const SOURCE_PATH = isAbsolute(SOURCE) ? SOURCE
  : existsSync(join(ROOT, SOURCE)) ? join(ROOT, SOURCE) : join(SOLKEY, SOURCE);
const UNIT = SOURCE.split("/").pop();

const fail = (msg) => {
  console.error(`solc-ast: ${msg}`);
  process.exit(1);
};
if (args.includes("--source") && !OUT_ARG) {
  fail("--source needs --out: the default is the TestSuite fixture");
}

// The pinned compiler, checked against the checkout's build script.
const gradle = readFileSync(join(SOLKEY, "keyext.solidity.core/build.gradle"), "utf8");
const compilerFile = optionOf("--compiler-file", null);
const compilerSha = optionOf("--compiler-sha256", null);
if ((compilerFile === null) !== (compilerSha === null) ||
    (compilerSha !== null && !/^[0-9a-f]{64}$/.test(compilerSha)))
  fail("--compiler-file and --compiler-sha256 must be supplied together (SHA-256: 64 lowercase hex digits)");
if (compilerFile !== null && (!OUT_ARG || !args.includes("--source")))
  fail("a compiler override needs explicit --source and --out: the default fixture is frozen");
const soljsonFile = gradle.match(/ext\.soljsonFile\s*=\s*"([^"]+)"/)?.[1];
const soljsonSha = compilerSha ?? gradle.match(/ext\.soljsonSha256\s*=\s*"([0-9a-f]{64})"/)?.[1];
if (!soljsonFile || !soljsonSha) fail("no soljsonFile/soljsonSha256 in build.gradle");
const soljsonDir = resolve(optionOf("--soljson", join(SOLKEY, "keyext.solidity.core/build/soljson")));
const soljsonPath = compilerFile ? resolve(compilerFile) : join(soljsonDir, soljsonFile);
if (!existsSync(soljsonPath)) {
  fail(`${soljsonPath} is missing: run solkey's \`./gradlew downloadSoljson\` first`);
}
const sha256 = (buf) => createHash("sha256").update(buf).digest("hex");
if (sha256(readFileSync(soljsonPath)) !== soljsonSha) {
  fail(`${soljsonFile} does not have the sha256 build.gradle pins`);
}

const solc = createRequire(import.meta.url)(soljsonPath);
const compile = solc.cwrap("solidity_compile", "string", ["string", "number", "number"]);
const version = solc.cwrap("solidity_version", "string", [])();

// Modern source admission uses only these audited binaries. The historical
// serialization remains available explicitly for byte-for-byte fixture checks.
const compilerPins = [
  { version: "0.8.34+commit.80d5c536.Emscripten.clang",
    file: "soljson-v0.8.34+commit.80d5c536.js",
    sha256: "c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8" },
  { version: "0.8.38+commit.1835d247.Emscripten.clang",
    file: "soljson-v0.8.38+commit.1835d247.js",
    sha256: "6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390" },
];
const pin = compilerPins.find(p => p.version === version && p.sha256 === soljsonSha);
if (!legacyFixture && !pin) fail("modern provenance requires a supported exact compiler pin");
if (legacyFixture && (args.includes("--via-ir") || args.includes("--evm-version")))
  fail("--legacy-fixture cannot record pipeline/settings overrides");
const bytes = readFileSync(SOURCE_PATH);
let source;
try { source = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true }).decode(bytes); }
catch { fail("source is not valid UTF-8"); }
const settings = legacyFixture
  ? { outputSelection: { "*": { "": ["ast"] } } }
  : { viaIR: args.includes("--via-ir"), evmVersion: optionOf("--evm-version", "osaka"),
      optimizer: { enabled: false, runs: 200 }, libraries: {}, remappings: [],
      outputSelection: { "*": { "": ["ast"] } } };
const input = {
  language: "Solidity",
  sources: { [UNIT]: { content: source } },
  settings,
};
const output = JSON.parse(compile(JSON.stringify(input), 0, 0));
const errors = (output.errors || []).filter((e) => e.severity === "error");
if (errors.length) fail(errors.map((e) => e.formattedMessage || e.message).join("\n"));
const ast = output.sources?.[UNIT]?.ast;
if (!ast) fail("solc produced no AST");

// src counts UTF-8 bytes. Index byte positions once, including non-ASCII
// comments/strings, instead of decoding the whole prefix for every node.
const lineStarts = [0];
for (let i = 0; i < bytes.length; i++) if (bytes[i] === 10) lineStarts.push(i + 1);
const lineOfByte = (b) => {
  let lo = 0;
  let hi = lineStarts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (lineStarts[mid] <= b) lo = mid; else hi = mid - 1;
  }
  return lo + 1;
};

const NOISE = new Set([
  "isConstant", "isLValue", "isPure", "lValueRequested", "nameLocation", "nameLocations",
  "memberLocation", "keyNameLocation", "valueNameLocation", "keyName", "valueName", "scope",
  "functionSelector", "implemented", "virtual", "exportedSymbols", "contractDependencies",
  "linearizedBaseContracts", "usedErrors", "usedEvents", "fullyImplemented",
  "argumentTypes", "overloadedDeclarations", "hexValue", "assignments",
  "functionReturnParameters", "abstract", "license", "absolutePath",
  "commonType", "tryCall",
]);
// Kept only when not empty, so a fixture without them does not change.
const KEPT_IF_ANY = new Set(["modifiers", "baseContracts"]);
// The declarations an `id` is kept on: what `referencedDeclaration` points to.
const DECLS = new Set([
  "VariableDeclaration", "StructDefinition", "FunctionDefinition", "ContractDefinition",
  "EnumDefinition", "EnumValue", "UserDefinedValueTypeDefinition",
  "ModifierDefinition",
]);
// Selectors are declaration metadata, needed only when the source observes
// them. Retain precisely those identities and fields, preserving older
// fixtures that never use metadata. Interface IDs use the interface's own
// declarations, not its inherited interface functions.
// Internal memory-return dispatch distinguishes abstract declarations from
// malformed concrete candidates. Retain implementation evidence only for
// this newly supported function-value family; older fixtures stay unchanged.
let memoryReturnDispatch = false;
const selectorDeclarations = new Set();
const declarations = new Map();
function walkAst(node, visit) {
  if (Array.isArray(node)) { for (const child of node) walkAst(child, visit); }
  else if (node && typeof node === 'object') {
    visit(node);
    for (const child of Object.values(node)) walkAst(child, visit);
  }
}
walkAst(ast, node => {
  if (node.id !== undefined) declarations.set(node.id, node);
  if (node.nodeType === 'FunctionTypeName' && node.visibility !== 'external' &&
      node.parameterTypes?.parameters?.length === 0 &&
      node.returnParameterTypes?.parameters?.length === 1) {
    const result = node.returnParameterTypes.parameters[0];
    if (result.typeName?.name === 'bytes' && result.storageLocation === 'memory')
      memoryReturnDispatch = true;
  }
});
walkAst(ast, node => {
  if (node.nodeType !== 'MemberAccess') return;
  if (node.memberName === 'selector' && node.expression?.referencedDeclaration !== undefined)
    selectorDeclarations.add(node.expression.referencedDeclaration);
  if (node.memberName === 'interfaceId') {
    const declaration = declarations.get(node.expression?.arguments?.[0]?.referencedDeclaration);
    for (const member of declaration?.nodes ?? [])
      if (member.nodeType === 'FunctionDefinition' && member.kind === 'function' &&
          ['public', 'external'].includes(member.visibility))
        selectorDeclarations.add(member.id);
  }
});
const isDeclaration = n => DECLS.has(n.nodeType) || selectorDeclarations.has(n.id);
const modernDeclaration = n => isDeclaration(n) ||
  ["EventDefinition", "ErrorDefinition", "SourceUnit"].includes(n.nodeType);
// The nodes `src` and `line` are kept on.
const located = (n, parentKey) =>
  isDeclaration(n) || parentKey === "statements" || n.nodeType === "TryCatchClause";

// The `@custom:key` clauses of the `///` lines directly above the loop
// starting at byte `b` (solkey's `SolJSONParser.loopSpec`, `KeyNatspec.of`).
const TAG = "@custom:key";
const LOOPS = new Set(["WhileStatement", "ForStatement", "DoWhileStatement"]);
const LOOP_KINDS = new Set(["invariant", "decreases", "unwind"]);
const loopSpecAt = (b) => {
  const lines = bytes.subarray(0, b).toString("utf8").split("\n");
  // only a loop that starts its line
  if (lines[lines.length - 1].trim() !== "") return [];
  const comment = [];
  for (let l = lines.length - 2; l >= 0 && lines[l].trim().startsWith("///"); l--) {
    comment.unshift(lines[l].trim().slice(3));
  }
  const doc = comment.join("\n");
  if (!doc.includes(TAG)) return [];
  // a clause runs from its tag to the next tag that starts a line
  const tags = [...doc.matchAll(/^[ \t]*@[A-Za-z][\w:-]*/gm)];
  const out = [];
  tags.forEach((m, i) => {
    if (m[0].trim() !== TAG) return;
    const end = i + 1 < tags.length ? tags[i + 1].index : doc.length;
    const text = doc.slice(m.index + m[0].length, end).trim().replace(/\s+/g, " ");
    const kind = text.split(" ")[0];
    if (!LOOP_KINDS.has(kind)) {
      fail(`a loop takes only ${TAG} invariant, decreases and unwind, not '${kind}'`);
    }
    out.push(text);
  });
  return out;
};

// solc's WebAssembly build prints builtin ids (`require` is -18) unsigned.
const signed = (v) =>
  Number.isInteger(v) && v > 2 ** 31 - 1 && v < 2 ** 32 ? v - 2 ** 32 : v;

function trim(n, parentKey) {
  if (Array.isArray(n)) return n.map((x) => trim(x, parentKey));
  if (!n || typeof n !== "object") return signed(n);
  const out = {};
  for (const [k, v] of Object.entries(n)) {
    // Inherited contracts need Solc's C3 order. Self-only lists remain noise,
    // keeping existing non-inherited fixture hashes unchanged.
    // A hex literal's bytes are its `hexValue` (its `value` is their text,
    // when they are UTF-8 at all); a number's is noise.
    const hexBytes = k === "hexValue" && n.nodeType === "Literal" &&
      (n.kind === "hexString" || typeof n.value !== "string" ||
        (!legacyFixture && ["string", "unicodeString"].includes(n.kind)));
    const selector = k === 'functionSelector' && (selectorDeclarations.has(n.id) ||
      (!legacyFixture && ['FunctionDefinition', 'VariableDeclaration'].includes(n.nodeType) &&
        ['public', 'external'].includes(n.visibility)));
    const getterKeyName = !legacyFixture && k === 'keyName' &&
      n.nodeType === 'Mapping' && typeof v === 'string' && v.length > 0;
    const worldMetadata = k === 'abstract' && args.includes('--world-metadata');
    const implementationMetadata = !legacyFixture && memoryReturnDispatch &&
      k === 'implemented' && n.nodeType === 'FunctionDefinition';
    if (NOISE.has(k) && !hexBytes && !selector && !getterKeyName && !worldMetadata && !implementationMetadata && !(k === "commonType" && !legacyFixture) &&
        !(k === "linearizedBaseContracts" && Array.isArray(v) && v.length > 1)) continue;
    if (KEPT_IF_ANY.has(k) && Array.isArray(v) && v.length === 0) continue;
    if (k === "id" && !(legacyFixture ? isDeclaration(n) : modernDeclaration(n))) continue;
    if (k === "src") {
      if (located(n, parentKey) || (!legacyFixture && typeof n.nodeType === "string")) {
        out.src = v;
        out.line = lineOfByte(Number(v.split(":")[0]));
      }
      continue;
    }
    if (k === "typeDescriptions") {
      if (v && v.typeString !== undefined) {
        out.typeDescriptions = { typeString: v.typeString };
        // Operator aliases must retain nominal identity, even when two UDVTs
        // have the same underlying primitive or spelling in separate scopes.
        if (!legacyFixture && typeof v.typeIdentifier === "string" &&
            v.typeIdentifier.startsWith("t_userDefinedValueType"))
          out.typeDescriptions.typeIdentifier = v.typeIdentifier;
      }
      continue;
    }
    out[k] = trim(v, k);
  }
  if (LOOPS.has(n.nodeType) && typeof n.src === "string") {
    const spec = loopSpecAt(Number(n.src.split(":")[0]));
    if (spec.length) out.loopSpec = spec;
  }
  return out;
}

let solkeyCommit = "unknown";
if (existsSync(join(SOLKEY, "snapshot.json"))) {
  solkeyCommit = JSON.parse(readFileSync(join(SOLKEY, "snapshot.json"), "utf8")).commit;
} else try {
  solkeyCommit = execFileSync("git", ["-C", SOLKEY, "rev-parse", "HEAD"], { encoding: "utf8" }).trim();
} catch {
  // not a git checkout: the header says so
}

const fixture = {
  header: {
    solcVersion: version,
    sourceSha256: sha256(bytes),
    solkeyCommit,
    source: SOURCE,
    ...(!legacyFixture ? {
      provenanceVersion: 1,
      compilerFile: pin.file,
      compilerSha256: pin.sha256,
      validationStage: "analysis",
      settings,
      acceptedPragmas: ast.nodes.filter(n => n.nodeType === "PragmaDirective").map(n => n.literals),
    } : {}),
  },
  ast: trim(ast, ""),
};
// Indented down to the statements, each statement on one line: small, and a
// diff names the statements that changed.
const isStatement = (n) => n && typeof n === "object" && !Array.isArray(n) &&
  n.line !== undefined && !isDeclaration(n);
function serialize(v, indent) {
  if (isStatement(v) || v === null || typeof v !== "object") return JSON.stringify(v);
  const pad = " ".repeat(indent + 1);
  if (Array.isArray(v)) {
    if (v.length === 0) return "[]";
    return `[\n${v.map((x) => pad + serialize(x, indent + 1)).join(",\n")}\n${" ".repeat(indent)}]`;
  }
  const entries = Object.entries(v);
  if (entries.length === 0) return "{}";
  return `{\n${entries.map(([k, x]) => `${pad}${JSON.stringify(k)}: ${serialize(x, indent + 1)}`)
    .join(",\n")}\n${" ".repeat(indent)}}`;
}
const text = serialize(fixture, 0) + "\n";

// FNV-1a 64 over the actual bytes: what the importing commands check.
function fixtureHash(data) {
  let h = 0xcbf29ce484222325n;
  for (const b of data) h = ((h ^ BigInt(b)) * 0x100000001b3n) & 0xffffffffffffffffn;
  return h;
}
// Read the old bytes before replacing OUT: every valid import may name them,
// while deliberate stale-fixture regressions must retain their wrong literal.
const previousHash = existsSync(OUT) ? fixtureHash(readFileSync(OUT)) : null;
const hash = `0x${fixtureHash(Buffer.from(text, "utf8")).toString(16).padStart(16, "0")}`;
mkdirSync(dirname(OUT), { recursive: true });
writeFileSync(OUT, text);

if (!args.includes("--no-wrapper") && existsSync(WRAPPER)) {
  const w = readFileSync(WRAPPER, "utf8");
  let initializedImport = false;
  const w2 = w.replace(
    /(\bsolc_(?:import|world_factory|world_library)\s+"([^"]+)"\s+hash\s+)(0[xX][0-9a-fA-F_]+)/g,
    (match, prefix, path, literal) => {
      if (resolve(dirname(WRAPPER), path) !== resolve(OUT)) return match;
      if (previousHash !== null) {
        if (BigInt(literal.replaceAll("_", "")) !== previousHash) return match;
      } else if (prefix.startsWith("solc_import")) {
        // With no prior fixture there is no validity evidence. Retain the
        // historical bootstrap convention: initialize the first ordinary
        // import, leaving later deliberate stale imports alone. World
        // commands retain their existing initial-generation placeholders.
        if (initializedImport) return match;
        initializedImport = true;
      }
      return prefix + hash;
    })
    // A stale-fixture diagnostic reports the new actual hash, even though its
    // intentionally wrong import literal above remains unchanged.
    .replace(new RegExp(`(${OUT.split("/").pop().replace(/[.*+?^${}()|[\]\\]/g, "\\$&")} has the hash )0x[0-9a-f]+`, "g"), `$1${hash}`);
  if (w2 !== w) writeFileSync(WRAPPER, w2);
}
let cacheDiffers = false;
if (args.includes("--compare-cache")) {
  // `SolcOutputCache`: the directory is the soljson's sha256 prefix, the file
  // the sha256 of the standard-JSON input `SolcWrapper` sends, whose unit name
  // is the source's absolute path; `astOf` and `build` select differently.
  const cacheRoot = process.env.XDG_CACHE_HOME || join(process.env.HOME || "", ".cache");
  const dir = join(cacheRoot, "solkey/solc", soljsonSha.slice(0, 16));
  const unit = SOURCE_PATH;
  const selections = [
    { "": ["ast"] },
    { "": ["ast"], "*": ["evm.bytecode.object", "evm.deployedBytecode.object"] },
  ];
  let compared = false;
  for (const sel of selections) {
    const key = sha256(Buffer.from(JSON.stringify({
      language: "Solidity",
      sources: { [unit]: { content: source } },
      settings: { outputSelection: { "*": sel } },
    }), "utf8"));
    const file = join(dir, `${key}.json`);
    if (!existsSync(file)) continue;
    const cached = JSON.parse(readFileSync(file, "utf8")).sources?.[unit]?.ast;
    if (!cached) continue;
    if (JSON.stringify(trim(cached, "")) !== JSON.stringify(fixture.ast)) {
      // reported after the hash line, so a caller still reads the hash
      console.error(`solc-ast: the AST differs from solkey's cached solc output ${file}`);
      cacheDiffers = true;
    } else {
      console.log(`solc-ast: same AST as solkey's cached output ${file}`);
    }
    compared = true;
  }
  if (!compared) console.log("solc-ast: solkey has no cached output for this source (run solkey on it once)");
}

console.log(`solc-ast: ${OUT} (${text.length} bytes, hash ${hash}, solc ${version})`);
if (cacheDiffers) process.exit(1);
