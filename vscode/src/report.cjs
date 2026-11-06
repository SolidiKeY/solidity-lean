'use strict';
const { validateCounterexample } = require('./counterexample.cjs');

const statuses = new Set(['proved', 'pending', 'skipped', 'skip', 'internal', 'unsupported', 'excluded', 'ready', 'notRun', 'error', 'refuted']);
const preconditions = new Set(['possible', 'impossible', 'unknown', 'notApplicable', 'notRun']);

function parseReport(stdout) {
  let report;
  try { report = JSON.parse(stdout); } catch { throw new Error('Verifier returned invalid JSON'); }
  if (!report || !Array.isArray(report.results) || !Array.isArray(report.errors)) throw new Error('Verifier returned an invalid report');
  for (const row of report.results) {
    if (!row || typeof row.source !== 'string' || typeof row.contract !== 'string' || typeof row.function !== 'string' || !statuses.has(row.status)) throw new Error('Verifier returned an invalid obligation');
    validateCounterexample(row);
    if (row.preconditions !== undefined && !preconditions.has(row.preconditions)) throw new Error('Verifier returned an invalid precondition audit');
    if (row.preconditionReason !== undefined && typeof row.preconditionReason !== 'string') throw new Error('Verifier returned an invalid precondition reason');
  }
  for (const error of report.errors) if (!error || typeof error.reason !== 'string') throw new Error('Verifier returned an invalid error');
  return report;
}

module.exports = { parseReport };
