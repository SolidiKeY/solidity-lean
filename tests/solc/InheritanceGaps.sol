// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract BaseCtor { uint n; modifier once() { _; } constructor(uint x) once { n = x; } }
contract CtorGap is BaseCtor(7) { function f() public pure { assert(true); } }
contract PlainCtor { uint m; constructor(uint x) { m = x; } }
contract CtorModifierGap is PlainCtor {
    modifier marked() { m += 1; _; }
    constructor() PlainCtor(2) marked { }
    function f() public pure { assert(true); }
}
contract ReturnCtor { uint r; constructor(uint x) { if (x > 1) { return; } r = x; } }
contract CtorReturnGap is ReturnCtor(3) { function f() public pure { assert(true); } }
contract PrivateRoot { uint private x; }
contract NameGap is PrivateRoot { uint private x; function f() public pure { assert(true); } }
