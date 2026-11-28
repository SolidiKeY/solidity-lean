/** Deterministic small Solidity programs. No expected-value oracle lives here. */
const MAX = (1n << 256n) - 1n;
export const families = ['add','sub','mul','bitwise','shift','divide','branch','loop','checked','revert'];
const word = value => {
  if (typeof value !== 'string' || !/^(0|[1-9][0-9]*)$/.test(value) || BigInt(value) > MAX)
    throw Error('operand must be a canonical uint256');
  return value;
};
export function sourceFor({family, a, b, rounds}) {
  word(a); word(b);
  if (!families.includes(family) || !Number.isInteger(rounds) || rounds < 0 || rounds > 8)
    throw Error('unsupported generator case');
  const body = {
    add:'unchecked { x = x + y; y = y + 1; }',
    sub:'unchecked { x = x - y; y = y - 1; }',
    mul:'unchecked { x = x * y; y = y * 2; }',
    bitwise:'x = (x ^ y) | (x & y); y = ~y;',
    shift:'x = x << (y % 257); y = y >> (x % 257);',
    divide:'if (y != 0) { x = x / y; y = x % y; }',
    branch:'if (x < y) { x = y; } else { y = x; }',
    loop:`unchecked { for (uint i = 0; i < ${rounds}; ++i) { x += y; y ^= i; } }`,
    checked:'x = x + y; y = y * 2;',
    revert:'x = y; if ((y & 1) == 0) { revert(); } y = 1;'
  }[family];
  return `// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.38;
contract Generated {
  uint256 x; uint256 y;
  function run() external returns (uint256, uint256) {
    x = ${a}; y = ${b};
    ${body}
    return (x, y);
  }
}`;
}
export function generate(count = 2000, seed = 1128) {
  if (!Number.isSafeInteger(count) || count < 1 || count > 10000) throw Error('count must be 1..10000');
  if (!Number.isSafeInteger(seed) || seed < 0 || seed >= 2 ** 32) throw Error('seed must be uint32');
  let state = BigInt(seed);
  const next = () => state = (6364136223846793005n * state + 1442695040888963407n) & ((1n << 64n) - 1n);
  const randomWord = () => [0,1,2,3].reduce(n => (n << 64n) | next(), 0n);
  const boundary = [0n, 1n, 2n, 255n, 256n, (1n << 255n), MAX];
  const seen = new Set();
  return Array.from({length:count}, (_, index) => {
    let a = randomWord(), b = randomWord();
    // Cover every family at every boundary before mixed random operands.
    if (index < families.length * boundary.length) {
      a = boundary[Math.floor(index / families.length)];
      b = boundary[boundary.length - 1 - Math.floor(index / families.length)];
    } else {
      const chooseA = next() >> 32n, chooseB = next() >> 32n;
      if (chooseA % 4n === 0n) a = boundary[Number((chooseA >> 2n) % BigInt(boundary.length))];
      if (chooseB % 4n === 0n) b = boundary[Number((chooseB >> 2n) % BigInt(boundary.length))];
    }
    const record = {index, seed, family:families[index % families.length], a:String(a), b:String(b), rounds:Number((next() >> 32n) % 9n)};
    let source = sourceFor(record);
    while (seen.has(source)) {
      record.a = String(randomWord());
      source = sourceFor(record);
    }
    seen.add(source);
    return {...record, source};
  });
}
/** Candidate inputs only; the caller must rerun both endpoints before accepting. */
export function reductions(record) {
  const candidates = [];
  for (const field of ['a','b','rounds']) {
    const value = BigInt(record[field]);
    for (const n of [...new Set([0n, 1n, value / 2n])]) if (n < value) {
      const candidate = {...record, [field]:field === 'rounds' ? Number(n) : String(n)};
      candidates.push({...candidate, source:sourceFor(candidate)});
    }
  }
  return candidates;
}
