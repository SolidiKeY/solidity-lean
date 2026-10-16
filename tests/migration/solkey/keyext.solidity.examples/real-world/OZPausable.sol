// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/utils/Pausable.sol
// and https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/mocks/PausableMock.sol
// Changes: PausableMock, Pausable and Context flattened into one contract; comments, events and
// custom errors dropped (a bare revert() instead). The modifiers inline the bodies of
// _requireNotPaused/_requirePaused and read _paused instead of calling paused(), since a
// function call inside a modifier fails to load (NullPointerException); paused() names its return.
contract OZPausable {
    bool private _paused;
    bool public drasticMeasureTaken;
    uint256 public count;

    /// @custom:key ensures _paused == false && drasticMeasureTaken == false && count == 0
    constructor() {
        _paused = false;
        drasticMeasureTaken = false;
        count = 0;
    }

    modifier whenNotPaused() {
        if (_paused) {
            revert();
        }
        _;
    }

    modifier whenPaused() {
        if (!_paused) {
            revert();
        }
        _;
    }

    /// @custom:key ensures p == _paused
    function paused() public view virtual returns (bool p) {
        return _paused;
    }

    function _requireNotPaused() internal view virtual {
        if (paused()) {
            revert();
        }
    }

    function _requirePaused() internal view virtual {
        if (!paused()) {
            revert();
        }
    }

    function _pause() internal virtual whenNotPaused {
        _paused = true;
    }

    function _unpause() internal virtual whenPaused {
        _paused = false;
    }

    /// @custom:key ensures \old(_paused) == false && count == \old(count) + 1 && _paused == false
    function normalProcess() external whenNotPaused {
        count++;
    }

    /// @custom:key ensures \old(_paused) == true && drasticMeasureTaken == true && _paused == true
    function drasticMeasure() external whenPaused {
        drasticMeasureTaken = true;
    }

    /// @custom:key ensures \old(_paused) == false && _paused == true
    function pause() external {
        _pause();
    }

    /// @custom:key ensures \old(_paused) == true && _paused == false
    function unpause() external {
        _unpause();
    }
}
