/** solc byte ranges to editor positions. These are presentation metadata only. */
import { createHash } from 'node:crypto';

export function sourceHash(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

/** LSP positions use zero-based lines and UTF-16 code units, unlike solc's UTF-8 bytes. */
export function sourceRange(bytes, src) {
  const match = /^(\d+):(\d+):(-?\d+)$/.exec(src ?? '');
  if (!match || match[3] !== '0') return undefined;
  const start = Number(match[1]), length = Number(match[2]), end = start + length;
  if (![start, length, end].every(Number.isSafeInteger) || end > bytes.length) return undefined;
  // Refuse offsets inside a multi-byte sequence rather than emitting a misleading range.
  const boundary = offset => offset === bytes.length || (bytes[offset] & 0xc0) !== 0x80;
  if (!boundary(start) || !boundary(end)) return undefined;
  const position = offset => {
    const text = bytes.subarray(0, offset).toString('utf8').replace(/^\uFEFF/, '');
    const lines = text.split(/\r\n|\r|\n/);
    return { line: lines.length - 1, character: lines.at(-1).length };
  };
  return { start: position(start), end: position(end) };
}

/** Match declaration IDs, never source names: overloads and renamed declarations stay distinct. */
export function sourceLocations(ast, bytes) {
  const contracts = new Map();
  for (const contract of ast.nodes ?? []) {
    if (contract.nodeType !== 'ContractDefinition') continue;
    const functions = new Map((contract.nodes ?? [])
      .filter(node => node.nodeType === 'FunctionDefinition')
      .map(node => [node.id, sourceRange(bytes, node.src)]));
    contracts.set(contract.name, { functions, range: sourceRange(bytes, contract.src) });
  }
  return (contractName, row) => {
    const contract = contracts.get(contractName);
    if (!contract) return undefined;
    if (Number.isSafeInteger(row.sourceId) && row.sourceId >= 0)
      return contract.functions.get(row.sourceId);
    // Synthesized deployment has no function declaration: its location is the contract.
    if (row.sourceId === -1 && row.function === 'constructor') return contract.range;
    return undefined;
  };
}
