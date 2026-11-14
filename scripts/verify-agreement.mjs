/** Compare complete verdict reports; never promote a native verdict to a theorem. */
export function compareModes(fast, certified, expected) {
  const bugs = [];
  const assumptionKeys = ['callback','overflow','tails','order','hash','zeroAddress'];
  const identity = row => JSON.stringify([row.source, row.contract, row.sourceId,
    row.signature ?? row.function, row.reading, row.sourceSha256, row.requestSha256, assumptionKeys.map(k => row.assumptions[k])]);
  function validRow(row) {
    return row && typeof row === 'object' && typeof row.source === 'string' && row.source.length > 0
      && typeof row.contract === 'string' && row.contract.length > 0
      && typeof (row.signature ?? row.function) === 'string' && (row.signature ?? row.function).length > 0
      && Number.isSafeInteger(row.sourceId) && row.sourceId > 0
      && row.assumptions && assumptionKeys.every(k => typeof row.assumptions[k] === 'string' && row.assumptions[k].length > 0)
      && typeof row.reading === 'string' && row.reading.length > 0
      && /^[a-f0-9]{64}$/.test(row.sourceSha256 ?? '')
      && /^[a-f0-9]{64}$/.test(row.requestSha256 ?? '');
  }
  const manifest = new Set();
  if (!Array.isArray(expected) || !expected.length) bugs.push('missing expected workload');
  else for (const row of expected) {
    if (!validRow(row)) { bugs.push('invalid expected obligation'); continue; }
    const key = identity(row);
    if (manifest.has(key)) bugs.push(`duplicate expected obligation: ${key}`);
    manifest.add(key);
  }
  function index(report, mode) {
    const rows = new Map();
    if (!report || !Array.isArray(report.results) || !Array.isArray(report.errors)) {
      bugs.push(`${mode}: malformed report`);
      return rows;
    }
    for (const error of report.errors) bugs.push(`${mode}: runner error: ${error?.reason ?? 'unknown'}`);
    for (const row of report.results) {
      if (!validRow(row)) { bugs.push(`${mode}: invalid obligation identity`); continue; }
      const key = identity(row);
      if (!manifest.has(key)) bugs.push(`${mode}: unexpected obligation: ${key}`);
      if (row.status === 'error') bugs.push(`${mode}: failed obligation: ${key}`);
      if (rows.has(key)) bugs.push(`${mode}: duplicate obligation: ${key}`);
      const expected = mode === 'fast' ? 'native' : 'certified';
      if (row.verification !== expected) bugs.push(`${mode}: expected ${expected} marker: ${key}`);
      if (!['proved', 'refuted', 'pending', 'unsupported', 'skipped', 'skip', 'internal', 'error'].includes(row.status))
        bugs.push(`${mode}: invalid verdict: ${key}`);
      rows.set(key, row);
    }
    for (const key of manifest) if (!rows.has(key)) bugs.push(`${mode}: missing expected obligation: ${key}`);
    if (!rows.size) bugs.push(`${mode}: empty workload`);
    return rows;
  }
  const a = index(fast, 'fast'), b = index(certified, 'certified');
  for (const key of new Set([...a.keys(), ...b.keys()])) {
    if (!a.has(key) || !b.has(key)) bugs.push(`missing obligation in one mode: ${key}`);
    else if (a.get(key).status !== b.get(key).status)
      bugs.push(`verdict disagreement: ${key}: native=${a.get(key).status}, certified=${b.get(key).status}`);
  }
  return {status: bugs.length ? 'bug' : 'agree', obligations: a.size, bugs};
}
