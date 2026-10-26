// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
pragma abicoder v2;

contract SourceAdmission {
    uint x = block.number;
    event E(uint value);

    function clean() public pure { assert(true); }
    function bad() public view returns (uint) { return block.number; }
    function selectorOnly() public pure returns (bytes4) { return this.bad.selector; }
    function storedFunctionKind() public view {
        function() external h = this.clean;
        assert(abi.encodePacked(h.address).length == 32);
    }
    function calledBad() public view returns (uint) { return this.bad(); }
    function castSelf() public view returns (uint) { return SourceAdmission(address(this)).bad(); }
    function aliasSelf() public view returns (uint) {
        SourceAdmission self = SourceAdmission(address(this));
        return self.bad();
    }
    modifier checkedBlock() { require(block.number != 0); _; }
    function modified() public checkedBlock { assert(true); }
    function emitted() public { emit E(block.number); }
    function encoded() public view returns (bytes memory) { return abi.encode(block.number); }

    /// @custom:key requires block.number == 0
    function specified() public pure { assert(true); }
    /// @custom:key requires \forall uint block; block == block
    function quantified() public pure { assert(true); }
    /// @custom:key requires keccak256("block.number") == keccak256("block.number")
    function quoted() public pure { assert(true); }

    function rethrow(bytes memory data) public pure {
        assembly { revert(add(data, 32), mload(data)) }
    }
    function badRethrow(uint data) public pure {
        assembly { revert(add(data, 32), mload(data)) }
    }
    function dynamicTarget() internal view { require(block.number != 0); }
    modifier dynamicModifier() {
        function() internal view target = dynamicTarget;
        target();
        _;
    }
    function modifierDispatch() public dynamicModifier {}
    function loopExcluded() public pure {
        /// @custom:key invariant block.number == 0
        while (false) {}
    }
    function quantifiedLoop() public pure {
        /// @custom:key invariant \forall uint block; block == block
        while (false) {}
    }
    constructor() {}
}

contract ConstructorBase { constructor(uint) {} }
contract ConstructorArguments is ConstructorBase(gasleft()) {
    function clean() public pure { assert(true); }
}

/// @custom:key invariant msg.data == 0
contract InvariantBase {}
contract InvariantOwner is InvariantBase {
    struct Message { uint data; }
    Message msg;
    function clean() public pure { assert(true); }
}

contract ReceiveBase { receive() external payable {} }
contract InheritedPayment is ReceiveBase {
    function pay() public { (bool ok, ) = address(this).call{value: 0}(""); require(ok); }
}

contract VirtualBase {
    function g() public view virtual returns (uint) { return 0; }
}
contract VirtualOwner is VirtualBase {
    function g() public view override returns (uint) { return block.number; }
    function callBaseType() public view returns (uint) { return VirtualBase(address(this)).g(); }
}

contract LoopBase {
    function inheritedLoop() public pure {
        /// @custom:key invariant block.timestamp == 0
        while (false) {}
    }
}
contract LoopOwner is LoopBase {
    struct Block { uint timestamp; }
    Block block;
    function callLoop() public pure { inheritedLoop(); }
}

/// @custom:key invariant msg.sender == 0
contract InvariantParameter {
    struct Message { uint sender; }
    function parameterShadow(Message memory msg) public pure {}
}

contract ConstructorLoopBase {
    modifier loopModifier() {
        /// @custom:key invariant block.number == 0
        while (false) {}
        _;
    }
    constructor() loopModifier {}
}
contract ConstructorLoopOwner is ConstructorLoopBase { constructor() {} }

contract PaymentFallback {
    uint x;
    fallback() external payable { x = 1; }
    function pay() public {
        x = 0;
        (bool ok, ) = address(this).call{value: 0}("");
        assert(!ok || x == 0);
    }
}
