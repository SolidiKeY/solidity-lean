// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

contract ComputedRevert {
    uint result;

    function computed() public {
        string memory lead = "boom";
        string memory reason = string.concat(lead, "!");
        revert(reason);
    }

    function bounce() public {
        try this.computed() { }
        catch (bytes memory data) {
            assembly { revert(add(data, 32), mload(data)) }
        }
    }

    function observe() public {
        try this.bounce() { result = 99; }
        catch Error(string memory reason) {
            result = bytes(reason).length;
            assert(result == 5);
            assert(bytes(reason)[4] == bytes1(uint8(33)));
        }
        catch { assert(false); }
    }

    function makeReason() internal returns (string memory) {
        result++;
        return "made";
    }

    function eager() public {
        require(true, makeReason());
        assert(result == 1);
    }

    function failedConcat() public pure {
        require(false, string.concat("b", "!"));
    }

    function reasonFails() internal pure returns (string memory) {
        revert();
    }

    function eagerFailure() public pure {
        require(true, reasonFails());
    }
}
