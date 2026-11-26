'use strict';
const fs = require('node:fs');
const path = require('node:path');

// Features own their subscriptions; a failed activation is rolled back.
function activate(context, services, directory = __dirname) {
  const owned = [], commands = new Set();
  const log = message => services.output.appendLine(message);
  const dispose = items => { for (const item of items.reverse()) try { item?.dispose?.(); } catch (error) { log(`Feature disposal failed: ${error.message}`); } };
  for (const file of fs.readdirSync(directory).filter(name => name.endsWith('.cjs') && name !== 'index.cjs').sort()) {
    const subscriptions = [], registered = [];
    const featureContext = Object.create(context);
    featureContext.subscriptions = subscriptions;
    const registerCommand = (name, handler, ...rest) => {
      if (commands.has(name)) throw new Error(`Command already registered: ${name}`);
      const registration = services.vscode.commands.registerCommand(name, handler, ...rest);
      commands.add(name); registered.push(name); subscriptions.push(registration);
      return registration;
    };
    const commandsApi = Object.create(services.vscode.commands);
    commandsApi.registerCommand = registerCommand;
    const vscode = Object.create(services.vscode);
    vscode.commands = commandsApi;
    try {
      const feature = require(path.join(directory, file));
      if (typeof feature.activate !== 'function') throw new Error('missing activate(context, services)');
      const result = feature.activate(featureContext, {...services, vscode, registerCommand});
      if (result && typeof result.then === 'function') throw new Error('activation must be synchronous');
      if (result) subscriptions.push(result);
      owned.push(subscriptions);
    } catch (error) {
      dispose(subscriptions); for (const name of registered) commands.delete(name);
      log(`Feature ${file} failed: ${error?.message || error}`);
    }
  }
  for (const name of ['solidityLean.runFunction', 'solidityLean.showObligation', 'solidityLean.showCounterexample']) {
    if (!commands.has(name)) owned.push([services.vscode.commands.registerCommand(name, () => services.vscode.window.showInformationMessage(`${name} is not available in this build`))]);
  }
  let disposed = false;
  return {dispose() { if (disposed) return; disposed = true; for (const items of owned.reverse()) dispose(items); }};
}
module.exports = {activate};
