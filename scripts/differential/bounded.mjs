#!/usr/bin/env node
/** Guards CI against overlong generation, compilation and shrinking. The existing
 * repository supervisor kills the complete process group; timeout is a failure. */
import {fileURLToPath} from 'node:url';
import {runTool} from '../test-solidity.mjs';
try {
  process.stdout.write(runTool(process.execPath,[fileURLToPath(new URL('./run.mjs',import.meta.url)),
    ...process.argv.slice(2)],840000));
} catch (e) {
  console.error(e.message);
  if (e.tool) console.error(JSON.stringify(e.tool));
  process.exitCode=1;
}
