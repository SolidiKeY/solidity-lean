/** Protect source/report inputs before replacing a JSON evidence output. */
import fs from 'node:fs';
import path from 'node:path';

function canonical(file) {
  let current = path.resolve(file);
  const suffix = [];
  for (;;) {
    try { return path.join(fs.realpathSync(current), ...suffix.reverse()); }
    catch (error) {
      if (error.code !== 'ENOENT' && error.code !== 'ENOTDIR') throw error;
      const parent = path.dirname(current);
      if (parent === current) throw error;
      suffix.push(path.basename(current)); current = parent;
    }
  }
}

export function assertReportOutput(output, inputs) {
  const destination = canonical(output);
  if (path.extname(output) !== '.json' || path.extname(destination) !== '.json')
    throw new Error('Evidence output must be a JSON report, never a Solidity source');
  if (inputs.some(input => canonical(input) === destination))
    throw new Error('Output must not alias an input report or source');
}
