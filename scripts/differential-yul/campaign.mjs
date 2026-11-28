/** Campaign orchestration. The stateful Lean transport is supplied separately;
 * mock transport tests are never semantic validation. */
import {createHash} from 'node:crypto';
import {generate, reductions, sourceFor} from './generate.mjs';
import {compileSource, executeArtifact, compareObservations} from './reference.mjs';
export const stages = ['ir', 'irOptimized'];
const hash = value => createHash('sha256').update(value).digest('hex');
const reason = error => String(error?.message ?? error);

/** Run the SAME compiled program through both IR stages and its reference bytecode.
 * lean(request) is an injected JS adapter, not the prerequisite driver's wire API.
 * It must return {status:'ok', observation} or {status:'blocked', reason}.
 * Fuel, unsupported syntax, crashes, and malformed observations remain blocked. */
export async function runCase(record, {compile, lean, reference = executeArtifact, optimizer = true}) {
  if (typeof compile !== 'function' || typeof lean !== 'function') throw Error('missing execution endpoint');
  if (record.source !== sourceFor(record)) throw Error('record/source mismatch');
  const row = {index:record.index, sourceSha256:hash(record.source), optimizer, results:[]};
  let artifact, actual;
  try {
    ({artifact} = compileSource(compile, record.source, {optimizer}));
    actual = await reference(artifact);
    const selector = artifact.evm.methodIdentifiers?.['run()'];
    if (!/^[0-9a-f]{8}$/.test(selector ?? '') || actual.calldata !== '0x' + selector)
      throw Error('reference calldata differs from generated run() call');
    // Validate even if Lean later refuses both stages.
    compareObservations(actual, actual);
  } catch (error) {
    row.results = stages.map(stage => ({stage, status:'blocked', phase:'reference', reason:reason(error)}));
    return row;
  }
  row.reference = actual;
  for (const stage of stages) {
    const ir = artifact[stage];
    try {
      const result = await lean({ir, stage, calldata:actual.calldata, slots:['0','1'],
        initialStorage:['0','0'], sourceSha256:row.sourceSha256, irSha256:hash(ir)});
      if (result?.status === 'blocked' && typeof result.reason === 'string' && result.reason.length) {
        row.results.push({stage, status:'blocked', phase:'lean', reason:result.reason});
      } else {
        if (result?.status !== 'ok') throw Error('invalid Lean outcome envelope');
        const equal = compareObservations(result.observation, actual);
        row.results.push({stage, status:equal ? 'agree' : 'mismatch',
          irSha256:hash(ir), lean:result.observation});
      }
    } catch (error) {
      row.results.push({stage, status:'blocked', phase:'lean', reason:reason(error)});
    }
  }
  return row;
}

/** Bind a returned row to the exact submitted source and recheck its verdicts. */
export function validateRow(record, row) {
  if (record.source !== sourceFor(record) || row?.index !== record.index ||
      row.sourceSha256 !== hash(record.source) || typeof row.optimizer !== 'boolean' ||
      row.results?.length !== stages.length) throw Error('execution row does not match input');
  for (const [index,result] of row.results.entries()) {
    if (result.stage !== stages[index]) throw Error('invalid execution stages');
    if (result.status === 'blocked') {
      if (!['reference','lean'].includes(result.phase) || typeof result.reason !== 'string' || !result.reason.length)
        throw Error('invalid blocked result');
    } else {
      if (!['agree','mismatch'].includes(result.status)) throw Error('invalid execution verdict');
      const equal = compareObservations(result.lean, row.reference);
      if (equal !== (result.status === 'agree')) throw Error('verdict disagrees with observations');
    }
  }
  return row;
}

export function summarize(rows, requested) {
  if (!Number.isSafeInteger(requested) || requested < 1 || rows.length !== requested)
    throw Error('incomplete campaign');
  const summary = {requested, executedPrograms:0, agreeingPrograms:0,
    stages:Object.fromEntries(stages.map(s => [s,{agree:0,mismatch:0,blocked:0}]))};
  const seen = new Set();
  for (const [index,row] of rows.entries()) {
    if (row.index !== index || !/^[0-9a-f]{64}$/.test(row.sourceSha256) || seen.has(row.sourceSha256) ||
        row.results?.length !== stages.length) throw Error('missing, repeated or reordered program');
    seen.add(row.sourceSha256);
    for (const [i,result] of row.results.entries()) {
      if (result.stage !== stages[i] || !['agree','mismatch','blocked'].includes(result.status))
        throw Error('missing, repeated or invalid IR stage');
      summary.stages[result.stage][result.status]++;
    }
    if (row.results.every(r => r.status !== 'blocked')) summary.executedPrograms++;
    if (row.results.every(r => r.status === 'agree')) summary.agreeingPrograms++;
  }
  return summary;
}

/** Greedy strict operand descent, preserving stage and differing observation
 * fields. A blocked candidate never preserves a mismatch. Budget is explicit;
 * exhaustion is never reported as a completed local minimum. */
export async function minimize(record, original, execute, {maxAttempts = 256, stage} = {}) {
  if (!Number.isSafeInteger(maxAttempts) || maxAttempts < 1) throw Error('invalid shrink budget');
  validateRow(record, original);
  if (stage !== undefined && !stages.includes(stage)) throw Error('invalid shrink stage');
  const mismatch = original.results.find(r => r.status === 'mismatch' && (stage === undefined || r.stage === stage));
  if (!mismatch) throw Error('minimization requires a mismatch');
  const signature = (row, stage) => {
    const r = row.results.find(r => r.stage === stage);
    if (r?.status !== 'mismatch') return null;
    return ['failed','returnData','storage'].filter(k =>
      JSON.stringify(r.lean[k]) !== JSON.stringify(row.reference[k])).join(',');
  };
  const target = signature(original, mismatch.stage);
  let best = record, row = original, attempts = 0, blockedAttempts = 0;
  while (true) {
    let changed = false, unresolvedCandidates = 0;
    for (const candidate of reductions(best)) {
      if (attempts === maxAttempts) return {record:best, row, attempts, blockedAttempts, unresolvedCandidates, complete:false, stage:mismatch.stage, fields:target};
      const tested = validateRow(candidate, await execute(candidate)); attempts++;
      if (tested.optimizer !== original.optimizer) throw Error('compiler mode changed during minimization');
      if (tested.results.find(r => r.stage === mismatch.stage).status === 'blocked') {
        blockedAttempts++; unresolvedCandidates++;
      }
      if (signature(tested, mismatch.stage) === target) {
        best = candidate; row = tested; changed = true; break;
      }
    }
    if (!changed) return {record:best, row, attempts, blockedAttempts, unresolvedCandidates, complete:unresolvedCandidates === 0, stage:mismatch.stage, fields:target};
  }
}

/** sink is awaited before the next program; a failed write aborts the campaign.
 * The caller owns durable external storage, provenance, and mismatch triage.
 * No run output is written to the source tree by this module. */
export async function campaign({count = 2000, seed = 1128, execute, sink}) {
  if (typeof execute !== 'function' || typeof sink !== 'function') throw Error('missing campaign execution/sink');
  const records = generate(count, seed), rows = [];
  for (const record of records) {
    const row = validateRow(record, await execute(record));
    // Check each prefix before accepting it into evidence.
    summarize([...rows,row], rows.length + 1);
    await sink({record,row});
    rows.push(row);
  }
  return {summary:summarize(rows,count), rows};
}
