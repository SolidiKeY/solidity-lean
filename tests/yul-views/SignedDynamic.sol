pragma solidity =0.8.38;
contract SignedDynamic {
    int16[] xs;
    uint256 marker;
    int24[] ys;
    constructor() {
        assembly ("memory-safe") {
            mstore(0, xs.slot)
            let x := keccak256(0, 32)
            sstore(x, 0xffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000ffff7fff8000)
            sstore(add(x, 1), 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc8000ffff)
            mstore(0, ys.slot)
            let y := keccak256(0, 32)
            sstore(y, 0xaabb800000eeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000ffffff7fffff800000)
            sstore(add(y, 1), 0xddddddddddddddddddddddddddddddddddddddddddddddddddddddddddffffff)
            sstore(3, 999)
        }
    }
    function readAll() public view returns (uint256[] memory o) {
        int16[] storage a = xs;
        int16[] storage b = xs;
        int24[] storage c = ys;
        o = new uint256[](29);
        o[0]=a.length; o[1]=b.length; o[2]=c.length; o[3]=ys.length;
        o[4]=a.length>0?uint256(int256(a[0])):0; o[5]=b.length>15?uint256(int256(b[15])):0;
        o[6]=a.length>16?uint256(int256(a[16])):0; o[7]=b.length>17?uint256(int256(b[17])):0;
        o[8]=c.length>0?uint256(int256(c[0])):0; o[9]=c.length>9?uint256(int256(c[9])):0; o[10]=ys.length>10?uint256(int256(ys[10])):0;
        o[11]=marker;
        o[23]=a.length>1?uint256(int256(a[1])):0;
        o[24]=a.length>2?uint256(int256(a[2])):0;
        o[25]=a.length>3?uint256(int256(a[3])):0;
        o[26]=c.length>1?uint256(int256(c[1])):0;
        o[27]=c.length>2?uint256(int256(c[2])):0;
        o[28]=c.length>3?uint256(int256(c[3])):0;
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
        xs[0]=type(int16).max; xs[1]=type(int16).min; xs[15]=0;
        xs[16]=type(int16).min; xs[17]=-1;
        ys[0]=type(int24).max; ys[1]=type(int24).min; ys[9]=-1; marker=555;
        return readAll();
    }
    function failAfterWrite() external {
        assembly ("memory-safe") { sstore(xs.slot,0) sstore(ys.slot,0) sstore(1,888) }
        revert("signed");
    }
    function outOfBounds() external view returns (int16) { return xs[18]; }
    function staticProbe() external view returns (bool) {
        (bool ok,)=address(this).staticcall(abi.encodeCall(this.zero,())); return ok;
    }
}
