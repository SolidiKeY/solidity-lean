// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Source: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.0.0/contracts/utils/Nonces.sol
// Changes: comments and the custom error dropped; made concrete with the public wrappers useNonce
// and useCheckedNonce (as OpenZeppelin's generated test harness exposes them); returns are named.
// unchecked wrap-around is not modelled, so the two wrappers require the nonce below 2^256 - 1.
/// @custom:key invariant \forall address a; _nonces[a] >= 0
contract OZNonces {
    mapping(address account => uint256) private _nonces;

    /// @custom:key ensures n == _nonces[owner] && _nonces[owner] == \old(_nonces[owner])
    function nonces(address owner) public view virtual returns (uint256 n) {
        return _nonces[owner];
    }

    function _useNonce(address owner) internal virtual returns (uint256) {
        unchecked {
            return _nonces[owner]++;
        }
    }

    function _useCheckedNonce(address owner, uint256 nonce) internal virtual {
        uint256 current = _useNonce(owner);
        if (nonce != current) {
            revert();
        }
    }

    /// @custom:key requires _nonces[owner] < 115792089237316195423570985008687907853269984665640564039457584007913129639935
    /// @custom:key ensures n == \old(_nonces[owner]) && _nonces[owner] == \old(_nonces[owner]) + 1
    /// @custom:key ensures \forall address a; a != owner -> _nonces[a] == \old(_nonces[a])
    function useNonce(address owner) public returns (uint256 n) {
        return _useNonce(owner);
    }

    /// @custom:key requires _nonces[owner] < 115792089237316195423570985008687907853269984665640564039457584007913129639935
    /// @custom:key ensures nonce == \old(_nonces[owner]) && _nonces[owner] == \old(_nonces[owner]) + 1
    /// @custom:key ensures \forall address a; a != owner -> _nonces[a] == \old(_nonces[a])
    function useCheckedNonce(address owner, uint256 nonce) public {
        _useCheckedNonce(owner, nonce);
    }
}
