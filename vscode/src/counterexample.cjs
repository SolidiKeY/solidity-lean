'use strict';
// Validate the runner's certificate envelope before presenting a refutation.
// The backend checks the Lean declaration; this adapter checks the transport.
const standardAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const wordLimit = 1n << 256n;
const signedLimit = 1n << 255n;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const nonempty = value => typeof value === 'string' && value.trim().length > 0;
function decimal(value, signed = false, bounded = true) {
  return typeof value === 'string' && (!bounded || value.length <= 79) && (signed ? /^(0|-?[1-9][0-9]*)$/ : /^(0|[1-9][0-9]*)$/).test(value);
}
function uint256(value) { return decimal(value) && BigInt(value) < wordLimit; }
function transaction(value) {
  return object(value) && ['msgSender', 'selfAddress', 'msgValue', 'timestamp'].every(field => uint256(value[field])) && Array.isArray(value.ext) && value.ext.length === 0;
}
function ledgerEntry(value) {
  return object(value) && uint256(value.address) && decimal(value.amount, true, false);
}
function outcome(value) {
  return object(value) && (value.kind === 'halt' && typeof value.halt === 'string' || value.kind === 'postStorage' && typeof value.storage === 'string');
}
function modelValue(argument) {
  if (!object(argument) || !nonempty(argument.modelName)) return false;
  if (argument.sourceName !== undefined && typeof argument.sourceName !== 'string') return false;
  if (argument.sourceType !== undefined && typeof argument.sourceType !== 'string') return false;
  if (argument.paramIndex !== undefined && (!Number.isSafeInteger(argument.paramIndex) || argument.paramIndex < 0)) return false;
  if (argument.type === 'bool') return typeof argument.value === 'boolean';
  if (argument.type === 'uint') return uint256(argument.value);
  if (argument.type === 'int') return decimal(argument.value, true) && BigInt(argument.value) >= -signedLimit && BigInt(argument.value) < signedLimit;
  return false;
}
function validateCounterexample(row) {
  const present = Object.prototype.hasOwnProperty.call(row, 'counterexample');
  if (row.status !== 'refuted') {
    if (present) throw new Error('Verifier attached counterexample evidence to a non-refuted obligation');
    return;
  }
  const evidence = row.counterexample;
  if (!object(evidence) || evidence.kind !== 'model-state' || evidence.certified !== true || evidence.goalKind !== 'fmlValid' || !nonempty(evidence.certificateDeclaration)
      || !Array.isArray(evidence.axioms) || !evidence.axioms.every(axiom => standardAxioms.has(axiom))
      || !Array.isArray(evidence.arguments) || !evidence.arguments.every(modelValue)
      || !transaction(evidence.transaction) || typeof evidence.initialStorage !== 'string'
      || !Array.isArray(evidence.initialLedger) || !evidence.initialLedger.every(ledgerEntry)
      || !uint256(evidence.initialBalance)
      || evidence.outcome !== undefined && !outcome(evidence.outcome)
      || !Array.isArray(evidence.lines) || !evidence.lines.every(line => typeof line === 'string')) {
    throw new Error('Verifier returned invalid certified model prestate evidence');
  }
}
// Keep control characters from forging output lines. Markdown is escaped by
// MarkdownString.appendText at the UI boundary; TestMessage strings are plain.
function escapedText(text) {
  return String(text).replace(/[\u0000-\u001F\u007F]/g, character => `\\u${character.charCodeAt(0).toString(16).padStart(4, '0')}`);
}
function counterexampleDetail(row) {
  if (row.status !== 'refuted') return '';
  const evidence = row.counterexample;
  const lines = [
    'certified model prestate',
    `Certificate: ${escapedText(evidence.certificateDeclaration)}`,
    ...evidence.arguments.map(argument => {
      const source = argument.sourceName ? `; source ${escapedText(argument.sourceName)}${argument.sourceType ? `: ${escapedText(argument.sourceType)}` : ''}` : '';
      return `${escapedText(argument.modelName)} (${argument.type}${source}) = ${escapedText(argument.value)}`;
    }),
    `Initial balance: ${evidence.initialBalance}`,
    `Initial storage: ${escapedText(evidence.initialStorage)}`,
    `Initial ledger: ${escapedText(JSON.stringify(evidence.initialLedger))}`,
    `Transaction: ${escapedText(JSON.stringify(evidence.transaction))}`,
    ...(evidence.outcome === undefined ? [] : [`Outcome: ${escapedText(JSON.stringify(evidence.outcome))}`]),
    ...evidence.lines.map(escapedText)
  ];
  return `\n${lines.join('\n')}`;
}
module.exports = { validateCounterexample, counterexampleDetail, escapedText };
