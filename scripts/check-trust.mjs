#!/usr/bin/env node
// Source inventory complements Lean's transitive theorem-axiom audit.
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

function lexLean(src, mode) {
  // Work in UTF-16 indices, as RegExp and source offsets do.
  const out = Array.from({ length: src.length }, (_, i) => src[i] === '\n' ? '\n' : ' ');
  function string(i, interpolation, hashes = null) {
    for (i++; i < src.length; i++) {
      if (mode === 'text' && hashes === null) out[i] = src[i];
      if (hashes !== null) {
        if (src.startsWith('"' + hashes, i)) return i + 1 + hashes.length;
      } else if (src[i] === '\\') {
        i++;
        if (mode === 'text' && i < src.length) out[i] = src[i];
      }
      else if (src[i] === '"') return i + 1;
      else if (interpolation && src[i] === '{') {
        if (src[i + 1] === '{') i++;
        else i = code(i + 1, true) - 1;
      }
    }
    return src.length;
  }
  function code(i, interpolation = false) {
    let braces = 0;
    for (; i < src.length;) {
      if (src[i] === '«') {
        // Escaped identifiers contain literal quotes and comment delimiters.
        // Keep their contents visible (including dangerous constant names).
        while (i < src.length) {
          out[i] = src[i];
          if (src[i++] === '»') break;
        }
      } else if (src.startsWith('/-', i)) {
        let depth = 1; i += 2;
        while (i < src.length && depth) {
          if (src.startsWith('/-', i)) { depth++; i += 2; }
          else if (src.startsWith('-/', i)) { depth--; i += 2; }
          else i++;
        }
      } else if (src.startsWith('--', i)) {
        while (i < src.length && src[i] !== '\n') i++;
      } else {
        const raw = src[i] === 'r' && src.slice(i).match(/^r(#+)?"/u);
        const char = src[i] === "'" && src.slice(i).match(/^'(?:\\.|[^\\'\n])'/u);
        if (raw) i = string(i + raw[0].length - 1, false, raw[1] ?? '');
        else if (char) i += char[0].length;
        else if (src[i] === '"') i = string(i, mode === 'interpolated');
        else if (interpolation && src[i] === '}' && braces === 0) return i + 1;
        else {
          if (interpolation && src[i] === '{') braces++;
          if (interpolation && src[i] === '}') braces--;
          out[i] = src[i]; i++;
        }
      }
    }
    return i;
  }
  code(0);
  return out.join('');
}

export function blankLean(src) {
  // Lean macros may choose interpolatedStr after arbitrary syntax. Keep the
  // union of ordinary, potentially interpolated, and literal-text views.
  // The third catches mixed nesting without guessing which macro parses a
  // string. Suspicious literal text must use raw strings. This is a source
  // lint, not a substitute for Lean's transitive theorem dependency audit.
  const views = ['ordinary', 'interpolated', 'text'].map(mode => lexLean(src, mode));
  return Array.from({ length: src.length }, (_, i) =>
    views.every(v => v[i] === ' ') ? ' ' : src[i]).join('');
}

export function findings(src) {
  const out = [];
  const clean = blankLean(src);
  for (const [kind, re] of [
    ['forbidden', /\b(?:sorry|sorryAx|native_decide|axiom|ofReduceBool)\b|\bdecide\s*\+\s*native\b|(?<![\w.])admit\b/gu],
    ['override', /\bimplemented_by\s+[^\s\]]+/gu],
    ['opaque', /\bopaque\s+[\p{L}_«][^\s:(]*/gu],
    ['unsafe', /\bunsafe\b/gu],
    ['kernel-option', /\bskipKernelTC\b/gu],
    ['recovery', /\.admit\b|\bmkSorry\b|\bmkSyntheticSorry\b/gu],
  ]) for (const m of clean.matchAll(re)) {
    const line = clean.slice(0, m.index).split('\n').length;
    // Inventory the full source line as context, or a normalized multiline token.
    const start = clean.lastIndexOf('\n', m.index - 1) + 1;
    const end = clean.indexOf('\n', m.index + m[0].length);
    const context = clean.slice(start, end < 0 ? clean.length : end).trim().replace(/\s+/gu, ' ');
    out.push({ kind, code: kind === 'forbidden' ? m[0] : context, line });
  }
  return out;
}

export function audit(files, inventory) {
  const actual = [], errors = [];
  for (const [file, src] of files) for (const f of findings(src)) {
    if (f.kind === 'forbidden') errors.push(`${file}:${f.line}: forbidden ${f.code}`);
    else actual.push({ file, kind: f.kind, code: f.code });
  }
  const key = x => JSON.stringify(x);
  const counts = xs => {
    const m = new Map();
    for (const x of xs) m.set(key(x), (m.get(key(x)) ?? 0) + 1);
    return m;
  };
  const expected = counts(inventory), seen = counts(actual);
  for (const k of new Set([...expected.keys(), ...seen.keys()])) {
    if (expected.get(k) !== seen.get(k)) errors.push(`inventory drift: ${k}: expected ${expected.get(k) ?? 0}, found ${seen.get(k) ?? 0}`);
  }
  return { actual, errors };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
  const names = [...new Set(readFileSync(0, 'utf8').split('\0'))]
    .filter(p => p.endsWith('.lean') && (!p.includes('/') || p.startsWith('Solidity/') || p.startsWith('vendor/LeanTeX/'))).sort();
  if (!names.includes('Solidity.lean')) throw new Error('expected a NUL-delimited repository file list on stdin');
  const inventory = JSON.parse(readFileSync(resolve(root, 'tests/trust-inventory.json'), 'utf8'));
  const result = audit(names.map(p => [p, readFileSync(resolve(root, p), 'utf8')]), inventory);
  for (const error of result.errors) console.error(error);
  console.log(`trust: ${names.length} sources, ${result.actual.length} inventoried implementation/recovery sites, ${result.errors.length} findings`);
  process.exitCode = result.errors.length ? 1 : 0;
}
