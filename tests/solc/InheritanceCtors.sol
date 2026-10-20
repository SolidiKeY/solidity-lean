// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
// Base constructors with modifiers and `return`s: each constructor's
// modifiers wrap its own body, after the base constructors ran, and a
// `return` ends its own body (solc's legacy creation code).
contract BaseMod {
    uint n;
    uint seen;
    modifier once() { seen = n + 1; _; seen = seen * 10; }
    constructor(uint x) once { n = x; }
}
contract ModLeaf is BaseMod(7) {
    constructor() { assert(n == 7 && seen == 10); }
}
contract PlainCtor { uint m; constructor(uint x) { m = x; } }
contract CtorModLeaf is PlainCtor {
    uint seenM;
    modifier marked() { seenM = m; m += 1; _; }
    constructor() PlainCtor(2) marked { assert(seenM == 2 && m == 3); }
}
contract ReturnCtor { uint r; constructor(uint x) { if (x > 1) { return; } r = x; } }
contract CtorReturnLeaf is ReturnCtor(3) {
    uint later;
    constructor() { later = 1; assert(r == 0 && later == 1); }
}
contract CtorReturnFalse is ReturnCtor(3) {
    constructor() { assert(r == 3); }
}
contract CtorModFalse is PlainCtor {
    uint seenM;
    modifier marked() { seenM = m; _; }
    constructor() PlainCtor(2) marked { assert(seenM == 0); }
}
