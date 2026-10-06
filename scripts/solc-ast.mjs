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
 * `typeIdentifier`, …) is noise that changes with unrelated edits.  A
 * function's `modifiers` and a contract's `baseContracts` are kept when they
 * are not empty: the import refuses what it would otherwise drop.
 *
 * The fixture starts with a header `{solcVersion, sourceSha256,
 * solkeyCommit, source}`.  Lake does not track a data file, so the module
 * that imports it names its hash (`hash 0x…`, FNV-1a 64 over the file's
 * bytes): the import refuses a fixture of another hash, and this script
 * rewrites the literal, which makes Lake re-check the module.
 *
 * Usage: node scripts/solc-ast.mjs [--solkey <checkout>] [--soljson <dir>] [--out <file>] [--no-wrapper]
 *   --solkey      the solkey checkout (default ../solkey, or SOLKEY_ROOT)
 *   --soljson     the directory holding the pinned soljson (default the
 *                 checkout's `keyext.solidity.core/build/soljson`; a fresh
 *                 clone has none, so point it at another checkout's)
 *   --out         where to write the fixture (default tests/solc/TestSuite.ast.json)
 *   --no-wrapper  leave the importing module's hash literal alone
 *   --compare-cache  also compare the trimmed AST with solkey's own cached solc
 *                 output for the same source (`~/.cache/solkey/solc/<soljson>/`,
 *                 keyed by the sha256 of `SolcWrapper`'s input), when there is one
 */

import { readFileSync, writeFileSync, mkdirSync, existsSync } from "node:fs";
import { join, dirname } from "node:path";
import { createHash } from "node:crypto";
import { createRequire } from "node:module";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const args = process.argv.slice(2);
const optionOf = (flag, fallback) => {
  const i = args.indexOf(flag);
  return i >= 0 && args[i + 1] ? args[i + 1] : fallback;
};

const ROOT = join(dirname(fileURLToPath(import.meta.url)), "..");
const SOLKEY = optionOf("--solkey", process.env.SOLKEY_ROOT || join(ROOT, "../solkey"));
const OUT = optionOf("--out", join(ROOT, "tests/solc/TestSuite.ast.json"));
const WRAPPER = join(ROOT, "Solidity/Solkey/TestSuite.lean");
const SOURCE = "keyext.solidity.examples/TestSuite.sol";
const UNIT = "TestSuite.sol";

const fail = (msg) => {
  console.error(`solc-ast: ${msg}`);
  process.exit(1);
};

// The pinned compiler, checked against the checkout's build script.
const gradle = readFileSync(join(SOLKEY, "keyext.solidity.core/build.gradle"), "utf8");
const soljsonFile = gradle.match(/ext\.soljsonFile\s*=\s*"([^"]+)"/)?.[1];
const soljsonSha = gradle.match(/ext\.soljsonSha256\s*=\s*"([0-9a-f]{64})"/)?.[1];
if (!soljsonFile || !soljsonSha) fail("no soljsonFile/soljsonSha256 in build.gradle");
const soljsonDir = optionOf("--soljson", join(SOLKEY, "keyext.solidity.core/build/soljson"));
const soljsonPath = join(soljsonDir, soljsonFile);
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

const source = readFileSync(join(SOLKEY, SOURCE), "utf8");
const input = {
  language: "Solidity",
  sources: { [UNIT]: { content: source } },
  settings: { outputSelection: { "*": { "": ["ast"] } } },
};
const output = JSON.parse(compile(JSON.stringify(input), 0, 0));
const errors = (output.errors || []).filter((e) => e.severity === "error");
if (errors.length) fail(errors.map((e) => e.formattedMessage || e.message).join("\n"));
const ast = output.sources?.[UNIT]?.ast;
if (!ast) fail("solc produced no AST");

// 1-based line of a character offset.
const lineStarts = [0];
for (let i = 0; i < source.length; i++) if (source[i] === "\n") lineStarts.push(i + 1);
// `src` counts bytes; the source is ASCII outside comments, so a byte offset is
// converted through the UTF-8 encoding to be safe.
const bytes = Buffer.from(source, "utf8");
const lineOfByte = (b) => {
  const chars = bytes.subarray(0, b).toString("utf8").length;
  let lo = 0;
  let hi = lineStarts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (lineStarts[mid] <= chars) lo = mid; else hi = mid - 1;
  }
  return lo + 1;
};

const NOISE = new Set([
  "isConstant", "isLValue", "isPure", "lValueRequested", "nameLocation", "nameLocations",
  "memberLocation", "keyNameLocation", "valueNameLocation", "keyName", "valueName", "scope",
  "functionSelector", "implemented", "virtual", "exportedSymbols", "contractDependencies",
  "linearizedBaseContracts", "usedErrors", "usedEvents", "canonicalName", "fullyImplemented",
  "argumentTypes", "overloadedDeclarations", "hexValue", "assignments",
  "functionReturnParameters", "abstract", "license", "absolutePath",
  "commonType", "tryCall",
]);
// Kept only when not empty, so a fixture without them does not change.
const KEPT_IF_ANY = new Set(["modifiers", "baseContracts"]);
// The declarations an `id` is kept on: what `referencedDeclaration` points to.
const DECLS = new Set([
  "VariableDeclaration", "StructDefinition", "FunctionDefinition", "ContractDefinition",
]);
// The nodes `src` and `line` are kept on.
const located = (n, parentKey) =>
  DECLS.has(n.nodeType) || parentKey === "statements" || n.nodeType === "TryCatchClause";

// solc's WebAssembly build prints builtin ids (`require` is -18) unsigned.
const signed = (v) =>
  Number.isInteger(v) && v > 2 ** 31 - 1 && v < 2 ** 32 ? v - 2 ** 32 : v;

function trim(n, parentKey) {
  if (Array.isArray(n)) return n.map((x) => trim(x, parentKey));
  if (!n || typeof n !== "object") return signed(n);
  const out = {};
  for (const [k, v] of Object.entries(n)) {
    if (NOISE.has(k)) continue;
    if (KEPT_IF_ANY.has(k) && Array.isArray(v) && v.length === 0) continue;
    if (k === "id" && !DECLS.has(n.nodeType)) continue;
    if (k === "src") {
      if (located(n, parentKey)) {
        out.src = v;
        out.line = lineOfByte(Number(v.split(":")[0]));
      }
      continue;
    }
    if (k === "typeDescriptions") {
      if (v && v.typeString !== undefined) out.typeDescriptions = { typeString: v.typeString };
      continue;
    }
    out[k] = trim(v, k);
  }
  return out;
}

let solkeyCommit = "unknown";
try {
  solkeyCommit = execFileSync("git", ["-C", SOLKEY, "rev-parse", "HEAD"], { encoding: "utf8" }).trim();
} catch {
  // not a git checkout: the header says so
}

const fixture = {
  header: {
    solcVersion: version,
    sourceSha256: sha256(Buffer.from(source, "utf8")),
    solkeyCommit,
    source: SOURCE,
  },
  ast: trim(ast, ""),
};
// Indented down to the statements, each statement on one line: small, and a
// diff names the statements that changed.
const isStatement = (n) => n && typeof n === "object" && !Array.isArray(n) &&
  n.line !== undefined && !DECLS.has(n.nodeType);
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
mkdirSync(dirname(OUT), { recursive: true });
writeFileSync(OUT, text);

// FNV-1a 64 over the bytes: what `solc_import … hash 0x…` checks.
let h = 0xcbf29ce484222325n;
for (const b of Buffer.from(text, "utf8")) {
  h ^= BigInt(b);
  h = (h * 0x100000001b3n) & 0xffffffffffffffffn;
}
const hash = `0x${h.toString(16).padStart(16, "0")}`;

if (!args.includes("--no-wrapper") && existsSync(WRAPPER)) {
  const w = readFileSync(WRAPPER, "utf8");
  // the import's literal, and the stale-fixture test's expected message
  const w2 = w.replace(/(solc_import\s+"[^"]*"\s+hash\s+)0x[0-9a-f]+/, `$1${hash}`)
    .replace(/(has the hash )0x[0-9a-f]+/g, `$1${hash}`);
  if (w2 !== w) writeFileSync(WRAPPER, w2);
}
let cacheDiffers = false;
if (args.includes("--compare-cache")) {
  // `SolcOutputCache`: the directory is the soljson's sha256 prefix, the file
  // the sha256 of the standard-JSON input `SolcWrapper` sends, whose unit name
  // is the source's absolute path; `astOf` and `build` select differently.
  const cacheRoot = process.env.XDG_CACHE_HOME || join(process.env.HOME || "", ".cache");
  const dir = join(cacheRoot, "solkey/solc", soljsonSha.slice(0, 16));
  const unit = join(SOLKEY, SOURCE);
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
