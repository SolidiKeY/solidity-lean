'use strict';
const good = new Set(['proved', 'skip', 'skipped', 'internal', 'ready']);
function validRange(range) {
  const valid = p => p && Number.isSafeInteger(p.line) && p.line >= 0 && Number.isSafeInteger(p.character) && p.character >= 0;
  return !!range && valid(range.start) && valid(range.end) && (range.end.line > range.start.line || (range.end.line === range.start.line && range.end.character >= range.start.character));
}
function rangeOf(row) { return validRange(row.range) ? row.range : { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }; }
function label(row) { return `${row.contract}.${row.signature || row.function}`; }
function detail(row) {
  return `${label(row)}: ${row.status}${row.reason ? ` — ${row.reason}` : ''}${row.reading ? `\nObligation reading: ${row.reading}` : ''}`;
}
function diagnostics(report) {
  return [
    ...report.results.filter(row => !good.has(row.status)).map(row => ({ source: row.source, range: rangeOf(row), severity: ['error', 'notRun'].includes(row.status) ? 'error' : 'warning', message: detail(row), code: row.status })),
    ...report.errors.map(error => ({ source: error.source, range: rangeOf(error), severity: 'error', message: error.reason, code: error.stage || 'backend' }))
  ];
}
function resultKind(row) {
  if (row.status === 'proved') return 'passed';
  if (['skip', 'skipped', 'internal'].includes(row.status)) return 'skipped';
  if (row.status === 'pending') return 'failed';
  return 'errored';
}
module.exports = { validRange, rangeOf, label, detail, diagnostics, resultKind };
