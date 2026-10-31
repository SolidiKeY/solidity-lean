// Task-local supplement: shared check-layers does not enumerate Creation modules.
import fs from 'node:fs';
import path from 'node:path';
const root = 'Solidity/Backend/Creation';
const seen = new Set();
function visit(name) {
  if (seen.has(name)) return;
  seen.add(name);
  if (!name.startsWith('Solidity.')) throw Error(`Unexpected external import ${name}`);
  if (!name.startsWith('Solidity.Backend.Creation.') &&
      !['Solidity.Backend.Assembler', 'Solidity.Backend.Jumpdest', 'Solidity.Backend.Opcode'].includes(name))
    throw Error(`Unapproved dependency ${name}`);
  const source = fs.readFileSync(name.replaceAll('.', '/') + '.lean', 'utf8');
  for (const match of source.matchAll(/^import\s+(\S+)/gm)) visit(match[1]);
}
for (const file of fs.readdirSync(root)) {
  if (path.extname(file) === '.lean') visit('Solidity.Backend.Creation.' + path.basename(file, '.lean'));
}
console.log(`Creation dependency closure PASS: ${[...seen].sort().join(', ')}`);
