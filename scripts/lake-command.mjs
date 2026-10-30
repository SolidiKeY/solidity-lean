import {accessSync, constants, statSync} from 'node:fs';
import {homedir} from 'node:os';
import {delimiter, join, resolve} from 'node:path';

/** Preserve PATH wrappers; fall back to Elan when its bin is absent from PATH. */
export function lakeCommand(env = process.env, cwd = process.cwd()) {
  const name = process.platform === 'win32' ? 'lake.exe' : 'lake';
  const directories = env.PATH === undefined ? [] : env.PATH.split(delimiter);
  directories.push(join(env.ELAN_HOME ?? join(homedir(), '.elan'), 'bin'));
  for (const directory of directories) {
    const candidate = resolve(cwd, directory, name);
    try {
      accessSync(candidate, constants.X_OK);
      if (statSync(candidate).isFile()) return candidate;
    } catch { /* Let a missing executable retain the normal spawn failure. */ }
  }
  return 'lake';
}
