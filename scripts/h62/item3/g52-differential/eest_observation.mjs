// Pure observation validation; synthetic controls never enter execution counts.
export function comparePost(expected, observed) {
  const fields = ['state_root', 'logs_hash'];
  for (const side of [expected, observed]) for (const key of fields) {
    if (typeof side[key] !== 'string' || !/^0x[0-9a-f]{64}$/.test(side[key])) throw new Error('invalid ' + key);
  }
  return fields.filter(key => expected[key] !== observed[key]);
}
export function validateConfig(config) {
  if (BigInt(config.chainid ?? '0x1') !== 1n) return false;
  const schedule = config.blobSchedule;
  if (!schedule || Object.keys(schedule).sort().join(',') !== 'Cancun,Osaka,Prague') return false;
  return Object.entries(schedule).every(([fork, value]) => {
    const cancun = fork === 'Cancun';
    return BigInt(value.target) === (cancun ? 3n : 6n) && BigInt(value.max) === (cancun ? 6n : 9n) &&
      BigInt(value.baseFeeUpdateFraction) === (cancun ? 3338477n : 5007716n);
  });
}

export function guardedResult(result, stopReason) {
  return stopReason ? { status: 'unsupported', reason: stopReason } : result;
}
