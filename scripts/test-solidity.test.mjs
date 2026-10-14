import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { runSolidityTests, solidityFiles, testsPassed } from "./test-solidity.mjs";

test("discovery deduplicates overlapping inputs", () => {
  const files = solidityFiles(["tests/solc", "tests/solc/Runner.sol"]);
  assert.equal(files.filter(f => f.endsWith("/Runner.sol")).length, 1);
  assert.deepEqual(files, [...files].sort());
});

test("empty and untested suites cannot pass", () => {
  assert.equal(testsPassed({ results: [], errors: [] }), false);
  assert.equal(testsPassed({ results: [{ status: "skipped" }], errors: [] }), false);
  assert.throws(() => runSolidityTests([], { build: false }), /no Solidity/);
});

test("Solidity source through solc and kernel-checked proof search", () => {
  const report = runSolidityTests(["tests/solc/Runner.sol"], { build: false });
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  assert.equal(status.passes, "proved");
  assert.equal(status.passesToo, "proved");
  assert.equal(status.staysOpen, "pending");
  assert.equal(status.ignored, "skipped");
  assert.equal(status.helper, "internal");
  assert.equal(status.assemblyGap, "unsupported");
  assert.equal(status.specified, "proved");
  assert.equal(status.badSpec, "pending");
  assert.equal(status.boxRevert, "proved");
  assert.equal(status.diamondRevert, "pending");
  assert.equal(status.breaksInvariant, "pending");
  assert.equal(status.constructor, "pending");
  assert.equal(status.preservesInvariant, "proved");
  assert.equal(status.payableSpec, "pending");
  assert.equal(status.misplacedInvariant, "unsupported");
  assert.equal(testsPassed(report), false);
});

test("implicit initializer omissions cannot silently pass", () => {
  const report = runSolidityTests(["tests/solc/InitGap.sol"], { build: false });
  assert.ok(report.errors.some(e => e.reason.includes("initializers are left out")));
  assert.equal(testsPassed(report), false);
});

test("a NatSpec expression cannot introduce another contract member", () => {
  const dir = mkdtempSync(join(tmpdir(), "solidity-clause-"));
  try {
    const source = join(dir, "BadClause.sol");
    writeFileSync(source, `pragma solidity ^0.8.0;
contract BadClause {
    /// @custom:key ensures false; requires false
    function bad() public pure {}
}`);
    const report = runSolidityTests([source], { build: false });
    assert.equal(report.errors.length, 1);
    assert.equal(testsPassed(report), false);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test("selection, listing and missing selections", () => {
  const options = { build: false, contract: "Runner", function: "passes" };
  const report = runSolidityTests(["tests/solc/Runner.sol"], options);
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.length, 1);
  assert.equal(testsPassed(report), true);
  const listed = runSolidityTests(["tests/solc/Runner.sol"], { ...options, list: true });
  assert.equal(listed.results[0].status, "ready");
  assert.equal(testsPassed(listed, true), true);
  const missing = runSolidityTests(["tests/solc/Runner.sol"], { ...options, function: "absent" });
  assert.equal(missing.errors.length, 1);
  assert.equal(testsPassed(missing), false);
});
