pragma solidity =0.8.38;
contract PackedDynamic {
    uint16[] xs;
    uint256 marker;
    uint24[] ys;
    constructor() {
        assembly ("memory-safe") {
            mstore(0, xs.slot)
            let x := keccak256(0, 32)
            sstore(x, not(0))
            sstore(add(x, 1), 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc004d)
            mstore(0, ys.slot)
            let y := keccak256(0, 32)
            sstore(y, 0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            sstore(add(y, 1), 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddd000063)
            sstore(3, 999)
        }
    }
    function readAll() public view returns (uint256[] memory o) {
        uint16[] storage a = xs;
        uint16[] storage b = xs;
        uint24[] storage c = ys;
        o = new uint256[](23);
        o[0]=a.length; o[1]=b.length; o[2]=c.length; o[3]=ys.length;
        o[4]=a.length>0?a[0]:0; o[5]=b.length>15?b[15]:0;
        o[6]=a.length>16?a[16]:0; o[7]=b.length>17?b[17]:0;
        o[8]=c.length>0?c[0]:0; o[9]=c.length>9?c[9]:0; o[10]=ys.length>10?ys[10]:0;
        o[11]=marker;
        assembly ("memory-safe") {
            let p := add(o, 32)
            mstore(add(p,384),sload(xs.slot))
            mstore(add(p,416),sload(ys.slot))
            mstore(0,xs.slot)
            let x := keccak256(0,32)
            mstore(add(p,448),sload(x))
            mstore(add(p,480),sload(add(x,1)))
            mstore(0,ys.slot)
            let y := keccak256(0,32)
            mstore(add(p,512),sload(y))
            mstore(add(p,544),sload(add(y,1)))
            mstore(add(p,576),sload(3))
            mstore(add(p,608),x)
            mstore(add(p,640),y)
            mstore(add(p,672),a.slot)
            mstore(add(p,704),c.slot)
        }
    }
    function fill() external returns (uint256[] memory) {
        assembly ("memory-safe") { sstore(xs.slot,17) sstore(ys.slot,11) }
        return readAll();
    }
    function shrinkOne() external returns (uint256[] memory) {
        assembly ("memory-safe") { sstore(xs.slot,1) sstore(ys.slot,1) }
        return readAll();
    }
    function zero() external returns (uint256[] memory) {
        assembly ("memory-safe") { sstore(xs.slot,0) sstore(ys.slot,0) }
        return readAll();
    }
    function regrow() external returns (uint256[] memory) {
        assembly ("memory-safe") { sstore(xs.slot,18) sstore(ys.slot,11) }
        return readAll();
    }
    function writeMembers() external returns (uint256[] memory) {
        xs[15]=65534; xs[16]=78; ys[9]=0x123456; marker=555;
        return readAll();
    }
    function failAfterWrite() external {
        assembly ("memory-safe") { sstore(xs.slot,0) sstore(ys.slot,0) sstore(1,888) }
        revert("packed");
    }
    function outOfBounds() external view returns (uint16) { return xs[18]; }
    function staticProbe() external view returns (bool) {
        (bool ok,)=address(this).staticcall(abi.encodeCall(this.zero,())); return ok;
    }
}
