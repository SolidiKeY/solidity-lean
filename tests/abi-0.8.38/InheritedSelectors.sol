// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.38;

// ABI identity of inherited and renamed function values (lane CF1 backfill).
// Each function returns a selector or encoding that names a base declaration
// the importer renames (overridden or shadowed), or an inherited one.

contract Base {
    function f(uint256 x) public virtual returns (uint256) { return x; }
    function g(uint8 x) external virtual returns (uint8) { return x; }
    function h(bool b) public returns (bool) { return b; }
    function k(uint256 x) public pure returns (uint256) { return x; }
    function k(bool b) public pure returns (bool) { return b; }
}

contract Derived is Base {
    function f(uint256 x) public override returns (uint256) { return x + 1; }
    function g(uint8 x) external override returns (uint8) { return x + 1; }
    function baseSelector() public pure returns (bytes4) { return Base.f.selector; }
    function derivedSelector() public view returns (bytes4) { return this.f.selector; }
    function inheritedSelector() public view returns (bytes4) { return this.h.selector; }
    function encodeOverride() public view returns (bytes memory) { return abi.encodeCall(this.g, (9)); }
    function encodeInherited() public view returns (bytes memory) { return abi.encodeCall(this.h, (true)); }
    function valueSelector() public view returns (bytes4) {
        function(uint256) external returns (uint256) p = this.f;
        return p.selector;
    }
    function encodeOverrideHead() public view returns (bytes4, uint256, uint8) {
        bytes memory e = abi.encodeCall(this.g, (9));
        return (bytes4(e), e.length, uint8(e[35]));
    }
    function encodeInheritedHead() public view returns (bytes4, uint256, uint8) {
        bytes memory e = abi.encodeCall(this.h, (true));
        return (bytes4(e), e.length, uint8(e[35]));
    }
    function inheritedValueSelector() public view returns (bytes4) {
        function(bool) external returns (bool) p = this.h;
        return p.selector;
    }
    function encodeValue() public view returns (bytes4, uint256) {
        bytes memory e = abi.encode(this.h);
        return (bytes4(bytes32(e) << 160), e.length);
    }
    function overloadCalls() public pure returns (uint256, bool) { return (k(3), k(true)); }
    function callValue() public returns (bool) {
        function(bool) external returns (bool) p = this.h;
        return p(true);
    }
    function callOwnValue() public returns (uint256) {
        function(uint256) external returns (uint256) p = this.f;
        return p(2);
    }
    function superCall() public returns (uint256) { return super.f(4); }
}
