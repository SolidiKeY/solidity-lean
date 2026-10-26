// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract WorldBase {
    uint internal count = 2;
    constructor(uint x) { count = x; }
}

contract WorldProduct is WorldBase {
    uint internal offset = 3;
    constructor(uint x) payable WorldBase(x) {
        count += offset;
        payable(address(42)).transfer(1);
    }
    function checkTen() external view { assert(count == 10); }
    function bump() external { count++; }
    function checkEleven() external view { assert(count == 11); }
    function falseZero() external view { assert(count == 0); }
}

contract WorldFailingProduct {
    uint internal touched;
    constructor() payable {
        touched = 1;
        payable(address(42)).transfer(1);
        revert();
    }
}

contract WorldImplicitProduct { }

contract WorldExternalPeer {
    uint internal n;
    function bump() external { n++; }
}

contract WorldCallingProduct {
    constructor() { WorldExternalPeer(address(42)).bump(); }
}

contract WorldBalanceProduct {
    constructor() { assert(address(42).balance == 0); }
}

contract WorldFactory {
    function make() external payable returns (WorldProduct) {
        return new WorldProduct{value: 1}(7);
    }
    function trySuccess() external payable returns (bool) {
        try new WorldProduct{value: 1}(7) returns (WorldProduct child) {
            return true;
        } catch {
            return false;
        }
    }
    function tryMake() external payable returns (bool) {
        try new WorldFailingProduct{value: 1}() returns (WorldFailingProduct child) {
            return true;
        } catch {
            return false;
        }
    }
    function failMake() external payable returns (WorldFailingProduct) {
        return new WorldFailingProduct{value: 1}();
    }
    function readsBalance() external returns (WorldBalanceProduct) {
        return new WorldBalanceProduct();
    }
    function callsExternal() external returns (WorldCallingProduct) {
        return new WorldCallingProduct();
    }
    function implicitMake() external returns (WorldImplicitProduct) {
        return new WorldImplicitProduct();
    }
    function extra() external returns (WorldProduct) {
        uint ignored = 0;
        return new WorldProduct(7);
    }
    function dynamicArgument(uint x) external returns (WorldProduct) {
        return new WorldProduct(x);
    }
}

struct WorldBox { uint n; }

library WorldLibrary {
    function mutate(WorldBox storage box) external { box.n = 9; }
}

contract WorldLibraryUser {
    WorldBox internal box;
    function mutate() external payable { WorldLibrary.mutate(box); }
    function checkNine() external view { assert(box.n == 9); }
    function checkZero() external view { assert(box.n == 0); }
    function extra() external {
        uint ignored = 0;
        WorldLibrary.mutate(box);
    }
}
