'use strict';
const fs = require('node:fs');
const path = require('node:path');

const contributed = ['solidityLean.runFunction', 'solidityLean.showObligation', 'solidityLean.showCounterexample'];

// Features register commands through services.registerCommand (or
// services.vscode.commands.registerCommand), so the stable dispatcher can
// provide a fallback before a lazy language client is ready.
function create(context, services, directory = __dirname) {
  const slots = new Map(), owned = [];
  let stopped = false, pending, finished;
  const log = message => services.output.appendLine(message);
  const disposeItems = async items => {for (const item of [...new Set(items)].reverse()) try {await item?.dispose?.();} catch (error) {log(`Feature disposal failed: ${error?.message || error}`);}};
  for (const name of contributed) {
    const slot = {handler:null}; slots.set(name, slot);
    owned.push(services.vscode.commands.registerCommand(name, (...args) => slot.handler ? slot.handler(...args) : services.vscode.window.showInformationMessage(`${name} is not available in this build`)));
  }
  async function activate(identity) {
    for (const file of fs.readdirSync(directory).filter(name => name.endsWith('.cjs') && name !== 'index.cjs').sort()) {
      if (stopped) break;
      const subscriptions = [], featureContext = Object.create(context);
      Object.defineProperty(featureContext, 'subscriptions', {value: subscriptions});
      const registerCommand = (name, handler, ...rest) => {
        if (stopped) throw new Error('Feature registry disposed');
        const slot = slots.get(name);
        let registration;
        if (slot) {
          if (slot.handler) throw new Error(`Command already registered: ${name}`);
          if (typeof handler !== 'function') throw new Error(`Invalid command handler: ${name}`);
          const bound = rest.length ? handler.bind(rest[0]) : handler;
          slot.handler = bound;
          registration = {dispose() {if (slot.handler === bound) slot.handler = null;}};
        } else registration = services.vscode.commands.registerCommand(name, handler, ...rest);
        subscriptions.push(registration); return registration;
      };
      const commandsApi = new Proxy({}, {get(_target, key) {return key === 'registerCommand' ? registerCommand : services.vscode.commands[key];}});
      const vscode = new Proxy({}, {get(_target, key) {return key === 'commands' ? commandsApi : services.vscode[key];}});
      try {
        const feature = require(path.join(directory, file));
        if (typeof feature.activate !== 'function') throw new Error('missing activate(context, services)');
        const result = await feature.activate(featureContext, {...services, vscode, registerCommand, identity});
        if (result) subscriptions.push(result);
        if (stopped) await disposeItems(subscriptions); else owned.push({dispose:()=>disposeItems(subscriptions)});
      } catch (error) {
        await disposeItems(subscriptions);
        if (!stopped) log(`Feature ${file} failed: ${error?.message || error}`);
      }
    }
  }
  return {
    start(identity) {if (!stopped && !pending) pending = activate(identity).catch(error=>{if (!stopped) log(`Feature registry failed: ${error?.message || error}`);});return pending;},
    dispose() {
      if (finished) return finished;
      stopped = true;
      finished = Promise.resolve(pending).finally(()=>disposeItems(owned));
      return finished;
    }
  };
}
module.exports = {create};
