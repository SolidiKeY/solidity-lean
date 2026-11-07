#!/usr/bin/env node
// Guard regression: dry-run pin moves lose guards or silently alter their bytes.
// Produces JSON previews only; it never applies changes or certifies semantics.
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { lstatSync, readFileSync, realpathSync } from "node:fs";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { inventory } from "./pin_dry_run.mjs";

const sha = bytes => createHash("sha256").update(bytes).digest("hex");
function pathPresent(path) {
  try { lstatSync(path); return true; }
  catch (e) { if (e.code === "ENOENT") return false; throw e; }
}
export function preview(root, report, selected) {
  if (!Array.isArray(selected) || !selected.length || new Set(selected).size !== selected.length || !Array.isArray(report?.rows))
    throw new Error("unique selected source files required");
  root = realpathSync(root);
  const output = [], areas = new Set();
  for (const file of selected) {
    if (typeof file !== "string" || !/^Solidity\/(?:[A-Za-z_][A-Za-z0-9_]*\/)*[A-Za-z_][A-Za-z0-9_]*\.lean$/.test(file))
      throw new Error("invalid selected source path");
    const full = resolve(root, file);
    if (!lstatSync(full).isFile() || realpathSync(full) !== full) throw new Error(`noncanonical source: ${file}`);
    const bytes = readFileSync(full), text = bytes.toString("utf8");
    if (!Buffer.from(text).equals(bytes)) throw new Error(`invalid UTF-8: ${file}`);
    const fresh = inventory([{file, text}]).rows;
    const recorded = report.rows.filter(x => x.file === file);
    if (!fresh.length || JSON.stringify(fresh) !== JSON.stringify(recorded)) throw new Error(`source or pin report differs: ${file}`);
    const dest = fresh[0].suggested_destination;
    if (areas.has(dest) || pathPresent(resolve(root, dest))) throw new Error(`area not empty or selected twice: ${dest}`);
    areas.add(dest);
    if (fresh.some(r => r.axioms === null || r.target !== r.name || !r.name.includes(".")))
      throw new Error(`unqualified or unparsed guard: ${file}`);
    const out = Buffer.from(bytes);
    let end = 0;
    for (const row of fresh) {
      if (row.start_byte < end || row.end_byte > bytes.length || row.start_byte >= row.end_byte ||
          bytes.subarray(row.start_byte, row.end_byte).toString("utf8") !== row.observed_block ||
          sha(bytes.subarray(row.start_byte, row.end_byte)) !== row.block_sha256)
        throw new Error(`invalid or overlapping guard span: ${file}`);
      for (let i = row.start_byte; i < row.end_byte; i++) if (out[i] !== 10 && out[i] !== 13) out[i] = 32;
      end = row.end_byte;
    }
    const module = file.slice(0, -5).replaceAll("/", ".");
    const pinText = `-- Preview only: unresolved scope and semantics.\nimport ${module}\n\n` + fresh.map(r => r.observed_block).join("\n\n") + "\n";
    output.push({file, source_sha256:sha(bytes), preview_source_sha256:sha(out), preview_source:out.toString("utf8"),
                 suggested_destination:dest, preview_pin_sha256:sha(pinText), preview_pin_module:pinText,
                 count:fresh.length, relocation:"unresolved-not-applied"});
  }
  return output;
}
export function main() {
  if (process.argv.length < 4) throw new Error("usage: pin_preview.mjs REPORT.json FILE...");
  const reportBytes = readFileSync(process.argv[2]);
  const report = JSON.parse(reportBytes.toString("utf8"));
  const head = execFileSync("git", ["rev-parse", "HEAD"], {encoding:"utf8"}).trim();
  if (report.source_head_unverified !== head) throw new Error("report head differs from checkout");
  console.log(JSON.stringify({status:"preview-only-no-application-or-acceptance", head, report_sha256:sha(reportBytes),
                              rows:preview(process.cwd(), report, process.argv.slice(3))}, null, 2));
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { main(); } catch (e) { console.error(`pin preview failed: ${e.message}`); process.exitCode = 1; }
}
