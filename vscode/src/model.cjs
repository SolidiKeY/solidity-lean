'use strict';
const { counterexampleDetail } = require('./counterexample.cjs');
const good = new Set(['proved', 'skip', 'skipped', 'internal', 'ready']);
const incompleteAudit = new Set(['impossible', 'unknown', 'notRun']);
function validRange(range) {
  const valid = p => p && Number.isSafeInteger(p.line) && p.line >= 0 && Number.isSafeInteger(p.character) && p.character >= 0;
  return !!range && valid(range.start) && valid(range.end) && (range.end.line > range.start.line || (range.end.line === range.start.line && range.end.character >= range.start.character));
}
function rangeOf(row) { return validRange(row.range) ? row.range : { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } }; }
function label(row) { return `${row.contract}.${row.signature || row.function}`; }
function status(row) {
  if (row.status === 'refuted') return 'refuted; certified model prestate';
  if (row.preconditions === 'impossible') return `${row.status}; vacuous specification`;
  if (row.preconditions === 'unknown') return `${row.status}; entry audit unknown`;
  if (row.preconditions === 'notRun') return `${row.status}; entry audit incomplete`;
  return row.status;
}
function entryDetail(row) {
  if (['possible','impossible'].includes(row.preconditions)) return `\nEntry condition: ${row.preconditions} (kernel-checked)`;
  if (row.preconditions === 'unknown') return `\nEntry audit: unknown${row.preconditionReason ? ` — ${row.preconditionReason}` : ''}`;
  if (row.preconditions === 'notRun') return '\nEntry audit: not completed';
  return '';
}
function detail(row) {
  return `${label(row)}: ${row.status}${row.reason ? ` — ${row.reason}` : ''}${row.reading ? `\nObligation reading: ${row.reading}` : ''}${entryDetail(row)}${counterexampleDetail(row)}`;
}
function diagnostics(report) {
  return [
    ...report.results.filter(row => !good.has(row.status)).map(row => ({ source: row.source, range: rangeOf(row), severity: ['error', 'notRun', 'refuted'].includes(row.status) ? 'error' : 'warning', message: detail(row), code: row.status })),
    ...report.results.filter(row => incompleteAudit.has(row.preconditions)).map(row => ({
      source:row.source, range:rangeOf(row), severity:'warning', code:`preconditions-${row.preconditions}`,
      message:row.preconditions === 'impossible' ? `${label(row)}: entry condition is impossible; the specification is vacuous (kernel-checked).` : `${label(row)}: precondition audit is ${row.preconditions === 'notRun' ? 'not complete' : 'unknown'}${row.preconditionReason ? ` — ${row.preconditionReason}` : ''}`,
    })),
    ...report.errors.map(error => ({ source: error.source, range: rangeOf(error), severity: 'error', message: error.reason, code: error.stage || 'backend' }))
  ];
}
function resultKind(row) {
  if (row.status === 'proved') return incompleteAudit.has(row.preconditions) ? 'errored' : 'passed';
  if (['skip', 'skipped', 'internal'].includes(row.status)) return 'skipped';
  if (['pending', 'refuted'].includes(row.status)) return 'failed';
  return 'errored';
}
module.exports = { validRange, rangeOf, label, status, detail, diagnostics, resultKind };
