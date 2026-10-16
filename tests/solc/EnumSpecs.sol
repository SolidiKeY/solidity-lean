pragma solidity ^0.8.26;
enum FileStatus { First, Last }
contract OtherEnumScope {
    enum Status { Last, First }
}
library EnumLibrary {
    enum Status { Last, First }
    /// @custom:key ensures \result == Status.Last
    function last() public pure returns (uint r) { return 0; }
}
contract EnumSpecs {
    enum Status { First, Last }
    Status status;
    /// @custom:key ensures status == Status.Last
    function set() public { status = Status.Last; }
    /// @custom:key ensures status == EnumSpecs.Status.First
    function reset() public { delete status; }
    /// @custom:key ensures status == Status.Last && FileStatus.Last == 1
    function qualifiedFile() public { status = Status.Last; }
    /// @custom:key ensures OtherEnumScope.Status.Last == 0
    function otherScope() public pure {}
    /// @custom:key ensures status == Status.First
    function falsePost() public { status = Status.Last; }
    /// @custom:key ensures \forall uint Status; Status == Status
    function quantifiedShadow() public pure {}
    /// @custom:key ensures \result == Status
    function parameterShadow(uint Status) public pure returns (uint r) { return Status; }
    /// @custom:key box
    function loopAnnotation() public pure {
        /// @custom:key invariant Status.Last == 1
        while (false) {}
        assert(uint(Status.First) == 0);
    }
    /// @custom:key ensures \result == EnumLibrary.Status.Last
    function libraryScope() public pure returns (uint r) { return EnumLibrary.last(); }
}
/// @custom:key invariant status == Status.First || status == Status.Last
contract EnumInvariant {
    enum Status { First, Last }
    Status status;
    /// @custom:key ensures status == Status.Last
    function set() public { status = Status.Last; }
    /// @custom:key ensures status == Status.First
    function falsePost() public { status = Status.Last; }
}
