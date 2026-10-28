// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.34 <0.9.0;
contract SelfPowerData {
    uint saved;
    uint[] flat;
    uint[][] arrays;
    function power(uint x, uint y) external returns (uint r) { saved = 9; r = x ** y; }
    function declared(uint x, uint y) external returns (uint) { uint r = x ** y; return r; }
    function nested(uint x, uint y) external returns (uint) { return 1 + (x ** y); }
    function inner(uint x, uint y) internal returns (uint) { return x ** y; }
    function relay(uint x, uint y) external returns (uint) { return inner(x,y); }
    function small(uint8 x, uint y) external returns (uint8) { return x ** y; }
    function wrapping(uint x, uint y) external returns (uint) { unchecked { return x ** y; } }
    function baseFailure() internal returns (uint) { assert(false); return 2; }
    function exponentFailure() internal returns (uint) { uint z = 0; return 1 / z; }
    function zeroBaseFailure() external returns (uint) { return 0 ** exponentFailure(); }
    function oneBaseFailure() external returns (uint) { return 1 ** exponentFailure(); }
    function zeroExponentFailure() external returns (uint) { return baseFailure() ** 0; }
    function shortcutFailures() external {
        try this.zeroBaseFailure() returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 18); } catch { assert(false); }
        try this.oneBaseFailure() returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 18); } catch { assert(false); }
        try this.zeroExponentFailure() returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 1); } catch { assert(false); }
    }
    function compete() external returns (uint) { return baseFailure() ** exponentFailure(); }
    function cutoff() external {
        try this.power(2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
        assert(saved == 0);
    }
    function multiply() external {
        try this.power(2**255,2) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
        assert(saved == 0);
    }
    function declaration() external {
        try this.declared(2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
    }
    function nestedCode() external {
        try this.nested(2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
    }
    function internalCode() external {
        try this.relay(2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
    }
    function nestedPriority(uint x, uint y, uint z) external returns (uint) { return (1 / z) + (x ** y); }
    function nestedPriorityCode(uint expected) external {
        try this.nestedPriority(2,256,0) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == expected); } catch { assert(false); }
    }
    function narrowCode() external {
        try this.small(255,2) returns (uint8) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
    }
    function fit() external {
        try this.power(2**255,1) returns (uint r) { assert(r == 2**255); }
        catch { assert(false); }
        assert(saved == 9);
    }
    function shortcuts() external {
        try this.power(0,0) returns (uint r) { assert(r == 1); } catch { assert(false); }
        try this.power(0,type(uint).max) returns (uint r) { assert(r == 0); } catch { assert(false); }
        try this.power(1,type(uint).max) returns (uint r) { assert(r == 1); } catch { assert(false); }
    }
    function uncheckedCode() external {
        try this.wrapping(2,256) returns (uint r) { assert(r == 0); } catch { assert(false); }
    }
    function priority(uint expected) external {
        try this.compete() returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == expected); } catch { assert(false); }
    }
    function rawData() external {
        try this.power(2,256) returns (uint) { assert(false); }
        catch (bytes memory d) {
            assert(d.length == 36);
            assert(d[0] == 0x4e && d[1] == 0x48 && d[2] == 0x7b && d[3] == 0x71);
            // Every byte, including the complete zero padding, is checked.
            assert(d[4] == 0x00 && d[5] == 0x00 && d[6] == 0x00 && d[7] == 0x00);
            assert(d[8] == 0x00 && d[9] == 0x00 && d[10] == 0x00 && d[11] == 0x00);
            assert(d[12] == 0x00 && d[13] == 0x00 && d[14] == 0x00 && d[15] == 0x00);
            assert(d[16] == 0x00 && d[17] == 0x00 && d[18] == 0x00 && d[19] == 0x00);
            assert(d[20] == 0x00 && d[21] == 0x00 && d[22] == 0x00 && d[23] == 0x00);
            assert(d[24] == 0x00 && d[25] == 0x00 && d[26] == 0x00 && d[27] == 0x00);
            assert(d[28] == 0x00 && d[29] == 0x00 && d[30] == 0x00 && d[31] == 0x00);
            assert(d[32] == 0x00 && d[33] == 0x00 && d[34] == 0x00 && d[35] == 0x11);
        }
        assert(saved == 0);
    }
    function andPower(bool flag, uint x, uint y) external returns (bool) { return flag && (x ** y == 0); }
    function orPower(bool flag, uint x, uint y) external returns (bool) { return flag || (x ** y == 0); }
    function selectPower(bool flag, uint x, uint y) external returns (uint) { uint r = flag ? x ** y : 7; return r; }
    function indexPower(uint x, uint y) external returns (uint) { return flat[x ** y]; }
    function indexBase(uint x, uint y) external returns (uint) { return arrays[0][x ** y]; }
    function andCode() external {
        try this.andPower(false,2,256) returns (bool r) { assert(!r); } catch { assert(false); }
        try this.andPower(true,2,256) returns (bool) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
    }
    function orCode() external {
        try this.orPower(true,2,256) returns (bool r) { assert(r); } catch { assert(false); }
        try this.orPower(false,2,256) returns (bool) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
    }
    function ternaryCode() external {
        try this.selectPower(false,2,256) returns (uint r) { assert(r == 7); } catch { assert(false); }
        try this.selectPower(true,2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
    }
    function indexCode() external {
        try this.indexPower(2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 17); } catch { assert(false); }
        try this.indexBase(2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 50); } catch { assert(false); }
    }
    function wrongCode() external {
        try this.power(2,256) returns (uint) { assert(false); }
        catch Panic(uint c) { assert(c == 1); } catch { assert(false); }
    }
    function wrongRaw() external {
        try this.power(2,256) returns (uint) { assert(false); }
        catch (bytes memory d) { assert(d.length == 36); assert(d[35] == 0x01); }
    }
}
