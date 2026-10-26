'use strict';
// Transport fixtures, not Lean proofs. The real-backend host checks are separate.
function evidence(overrides = {}) {
  return {
    kind: 'model-state', certified: true, goalKind: 'fmlValid',
    certificateDeclaration: 'SolTests.C.f.counterexample', axioms: ['propext', 'Classical.choice', 'Quot.sound'],
    arguments: [
      { modelName: 'p0', type: 'uint', value: ((1n << 256n) - 1n).toString() },
      { modelName: 'p1', type: 'int', value: (-(1n << 255n)).toString() },
      { modelName: 'p2', type: 'bool', value: true }
    ],
    transaction: { msgSender: '0', selfAddress: '0', msgValue: '0', timestamp: '0', ext: [] },
    initialStorage: 'default', initialLedger: [], initialBalance: '0',
    outcome: { kind: 'halt', halt: 'panic' },
    lines: ['model assignment'], ...overrides
  };
}
module.exports = { evidence };
