pragma solidity ^0.8.38;
error ByteView(bytes a, uint n);
error ArrayView(uint[] a, uint n);
contract ErrorCaptureLocations {
    function bytesSlice(bytes calldata b) external pure { revert ByteView({n:3,a:b[1:]}); }
    function arraySlice(uint[] calldata a) external pure { revert ArrayView({a:a[1:],n:3}); }
}
