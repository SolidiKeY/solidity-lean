// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

library StructCallsA {
    struct Box { uint value; }
    function store(Box storage self, uint value) internal { self.value = value; }
    function bump(Box memory self) internal { self.value += 2; }
}
library StructCallsB {
    struct Box { uint8 value; }
    function bump(Box memory self) internal { self.value += 3; }
}
library StructCallsC {
    struct Box { uint value; }
    function bump(Box memory self) internal pure { self.value += 4; }
}
type StructNumber is uint;
using {structNumberPlus as +} for StructNumber global;
function structNumberPlus(StructNumber a, StructNumber b) pure returns (StructNumber) {
    StructCallsC.Box memory box;
    box.value = StructNumber.unwrap(a) + StructNumber.unwrap(b);
    StructCallsC.bump(box);
    return StructNumber.wrap(box.value);
}
// Unused recursive declarations must not enter the ordinary finite-layout model.
library UnusedStructCycle {
    struct A { B[] children; }
    struct B { A[] children; }
}
contract LibraryStructCalls {
    using StructCallsA for StructCallsA.Box;
    using StructCallsB for StructCallsB.Box;
    using StructCallsC for StructCallsC.Box;
    StructCallsA.Box stored;
    StructCallsA.Box[] aBoxes;
    StructCallsB.Box[] bBoxes;
    function frame(StructCallsA.Box memory box) internal returns (uint) {
        box.bump();
        return box.value;
    }
    /// @custom:key box
    function storageReceiver() public {
        stored.store(7);
        assert(stored.value == 7);
    }
    /// @custom:key box
    function memoryReceiver() public {
        StructCallsA.Box memory box;
        box.value = 3;
        assert(frame(box) == 5);
        assert(box.value == 5);
    }
    /// @custom:key box
    function distinctDeclarations() public {
        StructCallsA.Box memory a;
        StructCallsB.Box memory b;
        a.value = 5;
        b.value = 9;
        a.bump();
        b.bump();
        assert(a.value == 7 && b.value == 12);
    }
    /// @custom:key box
    function parenthesizedReceiver() public {
        StructCallsA.Box memory box;
        box.value = 3;
        ((box.bump))();
        assert(box.value == 5);
    }
    /// @custom:key box
    function sameLayoutDeclarations() public {
        StructCallsA.Box memory a;
        StructCallsC.Box memory c;
        a.value = 5;
        c.value = 9;
        a.bump();
        c.bump();
        assert(a.value == 7 && c.value == 13);
    }
    /// @custom:key box
    function pushedReceivers() public {
        StructCallsA.Box storage a = aBoxes.push();
        StructCallsB.Box storage b = bBoxes.push();
        a.value = 7;
        b.value = 9;
        aBoxes.pop;
        bBoxes.pop;
        assert(a.value == 7 && b.value == 9);
    }
    /// @custom:key box
    function directPushedA() public {
        aBoxes.push().value = 11;
        assert(aBoxes[aBoxes.length - 1].value == 11);
    }
    /// @custom:key box
    function directPushedB() public {
        bBoxes.push().value = 13;
        assert(bBoxes[bBoxes.length - 1].value == 13);
    }
    /// @custom:key box
    function operatorDependency() public {
        StructNumber a = StructNumber.wrap(1);
        StructNumber b = StructNumber.wrap(2);
        assert(StructNumber.unwrap(a + b) == 7);
    }
    /// @custom:key box
    function falsePost() public {
        StructCallsA.Box memory box;
        box.value = 3;
        assert(frame(box) == 6);
    }
}
