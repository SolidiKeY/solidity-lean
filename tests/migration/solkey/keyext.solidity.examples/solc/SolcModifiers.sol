// SPDX-License-Identifier: GPL-2.0-only
pragma solidity ^0.8.0;

/// Ports of `test/libsolidity/semanticTests/modifiers/` and
/// `test/libsolidity/smtCheckerTests/modifiers/` from the solc compiler test suite.
abstract contract SolcModifiersA {
    int level;
    bool flag;
    uint named;
    int checkedLevel;

    modifier linearized() virtual {
        _;
    }

    modifier overridable() virtual {
        _;
    }

    modifier viaLocal() virtual {
        _;
    }

    modifier pinned(uint u) virtual {
        _;
    }

    modifier maybeSkip() virtual {
        _;
    }

    modifier setsNamed() virtual {
        named = 2;
        _;
    }

    modifier checked() virtual {
        assert(checkedLevel == 0);
        _;
    }
}

abstract contract SolcModifiersB is SolcModifiersA {
    modifier linearized() virtual override {
        level = 1;
        _;
    }

    modifier overridable() virtual override {
        flag = false;
        _;
    }
}

abstract contract SolcModifiersC is SolcModifiersA {
    modifier linearized() virtual override {
        level = 2;
        _;
    }
}

contract SolcModifiers is SolcModifiersB, SolcModifiersC {
    struct S { uint v; }

    uint x;
    uint a;
    uint called;
    address owner;
    S s;

    modifier addThenRemove(uint y) {
        uint b = y;
        a += b;
        _;
        a -= b;
        assert(b == y);
    }

    function sumOfLocals(uint y) internal addThenRemove(2) addThenRemove(5) addThenRemove(y)
        returns (uint)
    {
        return a;
    }

    modifier incV(S storage t) {
        t.v++;
        _;
    }

    modifier setsx() {
        _;
        x = 9;
    }

    modifier addArg(uint y) {
        a += y;
        _;
    }

    modifier mod1() {
        uint p = 1;
        uint q = 2;
        _;
    }

    modifier nonFree() {
        if (msg.value > 0) _;
    }

    modifier ifCondition(bool condition) {
        if (condition) _;
    }

    modifier alwaysZeros(uint u, uint w) {
        x++;
        _;
        require(u == 0);
        require(w == 0);
    }

    modifier setX1() {
        x = 1;
        _;
    }

    modifier addTen(uint) {
        x += 10;
        _;
    }

    modifier countCalls() {
        called++;
        _;
    }

    modifier requirePositive() {
        require(x > 0);
        _;
    }

    modifier requireBounded() {
        require(x > 0);
        require(x < 10000);
        _;
        assert(x > 1);
    }

    modifier requireBoundedNoAssert() {
        require(x > 0);
        require(x < 10000);
        _;
    }

    modifier increments() {
        x = x + 1;
        _;
        assert(x > 2);
    }

    modifier ifZero() {
        if (x == 0)
            _;
    }

    modifier requireGreater(uint u, uint w) {
        require(u > w);
        _;
    }

    modifier requireArgPositive(uint u) {
        require(u > 0);
        _;
    }


    modifier onlyOwner() {
        if (msg.sender == owner) _;
    }

    modifier onlyOwnerPositive() {
        if (msg.sender == owner) {
            require(x > 0);
            _;
        }
    }

    modifier shadowLocal() {
        uint y = 2;
        _;
    }

    modifier linearized() override(SolcModifiersB, SolcModifiersC) {
        level = 3;
        _;
    }

    modifier overridable() override(SolcModifiersA, SolcModifiersB) {
        flag = true;
        _;
    }

    modifier viaLocal() override {
        bool t = true;
        flag = t;
        _;
    }

    modifier pinned(uint u) override {
        require(u == 42);
        _;
        assert(u == 42);
    }

    modifier maybeSkip() override {
        if (false) _;
    }

    modifier setsNamed() override {
        named = 1;
        _;
    }

    modifier checked() override {
        assert(checkedLevel == 1);
        _;
    }

    modifier passIf(uint u, bool b) {
        if (b) _;
    }

    modifier loopWhileMagic(uint u) {
        while (u == 1234567) _;
    }

    modifier onlyOwnerNoop() {
        if (msg.sender == owner) _;
    }


    function retTwo() internal setsx returns (uint) {
        return 2;
    }

    function sumOfArgs(uint y) internal addArg(2) addArg(5) addArg(y) returns (uint) {
        return a;
    }

    function localsThenSkip(bool flagged) internal pure mod1 ifCondition(!flagged) returns (uint r) {
        return 3;
    }

    function getOne() internal nonFree returns (uint256 r) {
        return 1;
    }

    function threeReturns() internal alwaysZeros(r1, r3) returns (uint r1, uint r2, uint r3) {
        r1 = 16;
        r2 = 32;
        r3 = 64;
    }

    function fourTimes() internal alwaysZeros(r, r) alwaysZeros(r, r) alwaysZeros(r + r, r - r)
        alwaysZeros(r * r, r * r) returns (uint r)
    {
        r = x;
    }

    function tupleAfterSet() internal setX1 returns (uint t, uint r) {
        t = x;
        x = 4;
        r = 10;
    }

    function timesTen() internal addTen(x) returns (uint) {
        x *= 10;
        return x;
    }

    function guarded(uint y) internal pure ifCondition(y >= 10) returns (uint r) {
        r = 3;
    }


    function skipped() internal pure maybeSkip returns (bool r) {
        return true;
    }

    function staticNine() internal SolcModifiersA.setsNamed returns (uint) {
        return 9;
    }

    function virtualTen() internal setsNamed returns (uint) {
        return 10;
    }

    function staticChecked() internal view SolcModifiersA.checked returns (uint) {
    }

    function zeroReturn(uint u) internal pure passIf(u, true) loopWhileMagic(r) returns (uint r) {
    }

    function ownerNoop() internal onlyOwnerNoop {
    }

    function recursive(uint u) internal countCalls returns (uint256 r) {
        return u == 0 ? 2 : recursive(u - 1) ** 2;
    }

    function ownerOnly() internal onlyOwner {
        x = 0;
    }

    function ownerDecrement() internal onlyOwnerPositive {
        if (x > 0)
            x -= 1;
    }

    function ownerDecrementThenAdd() internal onlyOwnerPositive {
        x -= 1;
        ownerAddTwo();
    }

    function ownerAddTwo() internal onlyOwnerPositive {
        require(x < 10000);
        x += 2;
    }


    /// solc: semanticTests/modifiers/return_does_not_skip_modifier.sol
    function returnDoesNotSkipModifier() public {
        x = 0;
        uint r = retTwo();
        assert(r == 2);
        assert(x == 9);
    }

    /// solc: semanticTests/modifiers/function_modifier_multiple_times.sol
    /// @custom:key box
    function modifierMultipleTimes(uint y) public {
        require(y == 3);
        a = 0;
        uint r = sumOfArgs(y);
        assert(r == 10);
        assert(a == 10);
    }

    /// solc: semanticTests/modifiers/function_modifier_local_variables.sol
    function modifierLocalVariablesTrue() public pure {
        uint r = localsThenSkip(true);
        assert(r == 0);
    }

    /// solc: semanticTests/modifiers/function_modifier_local_variables.sol
    function modifierLocalVariablesFalse() public pure {
        uint r = localsThenSkip(false);
        assert(r == 3);
    }

    /// solc: semanticTests/modifiers/function_modifier.sol
    function modifierOnMsgValue() public payable {
        uint r = getOne();
        if (msg.value > 0) {
            assert(r == 1);
        } else {
            assert(r == 0);
        }
    }

    /// solc: semanticTests/modifiers/function_modifier_overriding.sol
    function modifierSkipsBody() public pure {
        bool r = skipped();
        assert(r == false);
    }

    /// solc: semanticTests/modifiers/access_through_contract_name.sol
    function modifierAccessThroughContractName() public {
        named = 7;
        uint r = staticNine();
        assert(r == 9);
        assert(named == 2);
        r = virtualTen();
        assert(r == 10);
        assert(named == 1);
        r = staticNine();
        assert(r == 9);
        assert(named == 2);
    }

    /// solc: semanticTests/modifiers/function_return_parameter.sol
    /// @custom:key box
    function returnParameterIntoModifier(uint u) public pure {
        require(u == 5);
        uint r = zeroReturn(u);
        assert(r == 0);
    }

    /// solc: semanticTests/modifiers/modifer_recursive.sol
    function modifierRecursive() public {
        called = 0;
        uint r = recursive(5);
        assert(r == 0x0100000000);
        assert(called == 6);
    }

    /// solc: semanticTests/modifiers/function_return_parameter_complex.sol
    function returnParameterForwarded() public {
        x = 0;
        (uint r1, uint r2, uint r3) = threeReturns();
        assert(r1 == 16);
        assert(r2 == 32);
        assert(r3 == 64);
        assert(x == 1);
    }

    /// solc: semanticTests/modifiers/function_return_parameter_complex.sol
    function returnParameterForwardedFourTimes() public {
        x = 1;
        uint r = fourTimes();
        assert(r == 5);
        assert(x == 5);
    }

    /// solc: semanticTests/modifiers/access_through_module_name.sol
    function modifierRunsBeforeTupleBody() public {
        x = 0;
        (uint t, uint r) = tupleAfterSet();
        assert(t == 1);
        assert(r == 10);
        assert(x == 4);
    }

    /// solc: semanticTests/modifiers/transient_state_variable_value_type.sol
    function modifierArgumentReadsStateFirst() public {
        x = 0;
        uint r = timesTen();
        assert(r == 100);
        assert(x == 100);
    }

    /// solc: semanticTests/modifiers/modifier_init_return.sol
    /// @custom:key box
    function modifierConditionBelow(uint y) public pure {
        require(y == 9);
        uint r = guarded(y);
        assert(r == 0);
    }

    /// solc: semanticTests/modifiers/modifier_init_return.sol
    /// @custom:key box
    function modifierConditionAbove(uint y) public pure {
        require(y == 10);
        uint r = guarded(y);
        assert(r == 3);
    }

    /// solc: smtCheckerTests/modifiers/modifier_simple.sol
    /// @custom:key box
    function smtModifierSimple() public view requirePositive {
        assert(x > 0);
    }

    /// solc: smtCheckerTests/modifiers/modifier_overflow.sol
    /// @custom:key box
    function smtModifierOverflow() public requirePositive {
        assert(x > 0);
        x = x + 1;
    }

    /// solc: smtCheckerTests/modifiers/modifier_two_invocations.sol
    /// @custom:key box
    function smtTwoInvocations() public requireBounded requireBounded {
        x = x + 1;
    }

    /// solc: smtCheckerTests/modifiers/modifier_multi.sol
    /// @custom:key box
    function smtMulti() public requireBoundedNoAssert increments {
        x = x + 1;
    }

    /// solc: smtCheckerTests/modifiers/modifier_control_flow.sol
    function smtControlFlow() public view ifZero {
        assert(x == 0);
    }

    /// solc: smtCheckerTests/modifiers/modifier_multi_parameters.sol
    /// @custom:key box
    function smtMultiParameters(uint y) public pure requireGreater(y, 0) {
        assert(y > 0);
    }

    /// solc: smtCheckerTests/modifiers/modifier_parameters.sol
    /// @custom:key box
    function smtParameters(uint y) public view requireArgPositive(y) requireArgPositive(2)
        requireArgPositive(x)
    {
        assert(y > 0);
        assert(x > 0);
    }


    /// solc: smtCheckerTests/modifiers/modifier_same_local_variables.sol
    /// @custom:key box
    function smtSameLocalVariables(uint y) public pure shadowLocal {
        require(y == 5);
        assert(y == 5);
    }

    /// solc: smtCheckerTests/modifiers/modifier_inside_branch_assignment_branch.sol
    function smtInsideBranchAssignmentBranch(uint y) public {
        x = 2;
        if (y > 0)
            ownerDecrement();
        assert(x > 0);
    }

    /// solc: smtCheckerTests/modifiers/modifier_inside_branch_assignment_multi_branches.sol
    /// @custom:key box
    function smtInsideBranchMultiBranches(uint y) public {
        require(y > 0 && y < 10000);
        address o = owner;
        require(msg.sender == o);
        x = y;
        if (y > 1) {
            ownerDecrementThenAdd();
            uint expected = y + 1;
            assert(x == expected);
        }
    }

    /// solc: smtCheckerTests/modifiers/modifier_inside_branch.sol
    function smtInsideBranch(uint y) public {
        if (y > 0) ownerOnly();
    }

    /// solc: smtCheckerTests/modifiers/modifier_overriding_1.sol
    /// @custom:key box
    function smtOverriding1() public pinned(x) {
    }

    /// solc: smtCheckerTests/modifiers/modifier_overriding_2.sol
    function smtOverriding2() public overridable {
        assert(flag);
    }

    /// solc: smtCheckerTests/modifiers/modifier_overriding_3.sol
    function smtOverriding3() public viaLocal {
        assert(flag);
    }

    /// solc: smtCheckerTests/modifiers/modifier_overriding_4.sol
    function smtOverriding4() public linearized {
        assert(level != 0);
        assert(level != 1);
        assert(level != 2);
    }

    /// solc: smtCheckerTests/modifiers/modifier_virtual_static_call_2.sol
    function smtVirtualStaticCall2() public {
        checkedLevel = 0;
        staticChecked();
    }

    /// solc: smtCheckerTests/modifiers/modifier_assignment_outside_branch.sol
    function smtAssignmentOutsideBranch(uint y) public {
        y = 1;
        if (y > x) ownerNoop();
    }

    /// solc: smtCheckerTests/modifiers/modifier_code_after_placeholder.sol
    /// @custom:key box
    function smtCodeAfterPlaceholder() public requirePositive {
        assert(x > 0);
        unchecked { x = x + 1; }
    }

    function addHundred(S storage t) internal incV(t) {
        t.v += 0x100;
    }

    /// solc: semanticTests/modifiers/function_modifier_library.sol
    function storageModifierParameter() public {
        s.v = 0;
        addHundred(s);
        addHundred(s);
        assert(s.v == 0x202);
    }

    /// solc: semanticTests/modifiers/function_modifier_multiple_times_local_vars.sol
    /// @custom:key box
    function modifierMultipleTimesLocalVars(uint y) public {
        require(y == 3);
        a = 0;
        uint r = sumOfLocals(y);
        assert(r == 10);
        assert(a == 0);
    }
}
