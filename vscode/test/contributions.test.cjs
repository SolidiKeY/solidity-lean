// Manifest and injected command-boundary evidence; does not establish rendered menu parity.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),manifest=require('../package.json'),{fixture}=require('./controller-fixture.cjs');
test('Solidity editor context exposes only registered truthful verification/status actions with trusted file scope',async()=>{
 const e=fixture();try{const c=manifest.contributes,submenu=c.submenus.find(item=>item.id==='solidityLean.context');assert.equal(submenu.label,'Solidity Lean');const entry=c.menus['editor/context'].find(item=>item.submenu===submenu.id);for(const scope of ['editorTextFocus','editorLangId == solidity','resourceScheme == file','isWorkspaceTrusted'])assert.ok(entry.when.includes(scope));const actions=c.menus[submenu.id];assert.deepEqual(actions.map(item=>item.command),['solidityLean.verify','solidityLean.list','solidityLean.cancel','solidityLean.showOutput','solidityLean.openStatusBarMenu','solidityLean.restartServer','solidityLean.build','solidityLean.run','solidityLean.test','solidityLean.buildCustomArgs']);for(const item of actions){assert.ok(e.commands.has(item.command));assert.equal(item.when,entry.when);}for(const command of ['build','run','test','buildCustomArgs'])assert.ok(c.commands.some(item=>item.command==='solidityLean.'+command));assert.ok(!c.commands.some(item=>/Trace/.test(item.command)));}finally{await e.api.dispose();}
});

test('build/run/test bindings use valid VS Code syntax for the source chords and registered local commands',async()=>{
 const e=fixture();try{
  const expected=[['build','ctrl+shift+b','shift+cmd+b'],['run','f5','f5'],['test','shift+f5','shift+f5'],['buildCustomArgs','f6','f6']];
  assert.ok(Array.isArray(manifest.contributes.keybindings),'execution keybindings must be contributed');
  assert.equal(manifest.contributes.keybindings.length,expected.length);
  for(const [command,key,mac] of expected){const row=manifest.contributes.keybindings.find(k=>k.command==='solidityLean.'+command);assert.ok(row);assert.equal(row.key,key);assert.equal(row.mac,mac);assert.match(row.mac,/^[a-z0-9+]+$/i,'configuration uses key tokens, never display glyphs');assert.equal(row.when,'editorTextFocus && editorLangId == solidity && resourceScheme == file && isWorkspaceTrusted');assert.ok(e.commands.has(row.command));}
  assert.ok(!manifest.contributes.keybindings.some(k=>['f7','f8'].includes(k.key)),'unsupported trace actions are not substituted with verification');
 }finally{await e.api.dispose();}
});
