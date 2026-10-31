import {test} from 'node:test';
import assert from 'node:assert/strict';
import {chmodSync, mkdirSync, mkdtempSync, rmSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {delimiter, join} from 'node:path';
import {lakeCommand} from './lake-command.mjs';

test('Lake resolution preserves PATH order and wrappers before the Elan fallback', () => {
  const root = mkdtempSync(join(tmpdir(), 'lake-resolution-'));
  const name = process.platform === 'win32' ? 'lake.exe' : 'lake';
  function executable(directory) {
    mkdirSync(directory, {recursive:true});
    const path = join(directory, name);
    writeFileSync(path, '#!/bin/sh\nexit 0\n');
    chmodSync(path, 0o700);
    return path;
  }
  try {
    const first = executable(join(root, 'first'));
    const second = executable(join(root, 'second'));
    const elan = join(root, 'elan');
    const fallback = executable(join(elan, 'bin'));
    const env = {PATH:[join(root, 'missing'), join(root, 'first'), join(root, 'second')].join(delimiter), ELAN_HOME:elan};
    assert.equal(lakeCommand(env), first);
    rmSync(first);
    assert.equal(lakeCommand(env), second);
    rmSync(second);
    assert.equal(lakeCommand(env), fallback);
    assert.equal(lakeCommand({PATH:join(root, 'missing'), ELAN_HOME:elan}), fallback);
    assert.equal(lakeCommand({ELAN_HOME:elan}), fallback);
    rmSync(fallback);
    assert.equal(lakeCommand(env), 'lake');
  } finally { rmSync(root, {recursive:true, force:true}); }
});

test('Lake resolution handles relative and empty PATH entries at the tool working directory', () => {
  const root = mkdtempSync(join(tmpdir(), 'lake-relative-'));
  const name = process.platform === 'win32' ? 'lake.exe' : 'lake';
  try {
    mkdirSync(join(root, 'relative'));
    const path = join(root, 'relative', name);
    writeFileSync(path, ''); chmodSync(path, 0o700);
    const env = {PATH:'relative', ELAN_HOME:join(root, 'missing')};
    assert.equal(lakeCommand(env, root), path);
    const local = join(root, name);
    writeFileSync(local, ''); chmodSync(local, 0o700);
    assert.equal(lakeCommand({...env, PATH:''}, root), local);
  } finally { rmSync(root, {recursive:true, force:true}); }
});

test('Lake resolution skips directories and non-executable files', {skip:process.platform === 'win32'}, () => {
  const root = mkdtempSync(join(tmpdir(), 'lake-executable-'));
  try {
    mkdirSync(join(root, 'directory', 'lake'), {recursive:true});
    mkdirSync(join(root, 'file'));
    writeFileSync(join(root, 'file', 'lake'), '');
    chmodSync(join(root, 'file', 'lake'), 0o600);
    assert.equal(lakeCommand({PATH:[join(root, 'directory'), join(root, 'file')].join(delimiter),
      ELAN_HOME:join(root, 'missing')}), 'lake');
  } finally { rmSync(root, {recursive:true, force:true}); }
});
