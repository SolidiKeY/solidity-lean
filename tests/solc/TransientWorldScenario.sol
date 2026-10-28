// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.28;
import "./TransientFactory.sol";
// Reference composition of the same imported frames. General lowering of this
// multi-statement source-world body is deliberately not claimed by the model.
contract TransientWorldScenario {
    TransientProduct public last;
    function makeOnly() external returns (uint) {
        last = new TransientProduct(false);
        last.checkFrame();
        return last.saved();
    }
    function compose() external returns (uint) {
        last = new TransientProduct(false);
        last.checkFrame();
        TransientProduct other = new TransientProduct(false);
        last.write();
        last.checkWritten();
        other.checkFrame();
        return last.saved();
    }
    function checkFresh() external view returns (uint) { last.checkReset(); return last.saved(); }
    function checkLater() external view returns (uint) { last.checkLater(); return last.saved(); }
    function caught() external returns (bool) {
        last.write();
        bool result;
        try new TransientProduct(true) returns (TransientProduct child) { result = true; }
        catch { result = false; }
        last.checkWritten();
        return result;
    }
    function uncaught() external { last.write(); new TransientProduct(true); }
    function falseShared() external view { last.falseShared(); }
    function failWrite() external { last.fail(); }
}
