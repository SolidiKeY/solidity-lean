pragma solidity ^0.8.0;
contract TryContinuePositive {
 function positive() public pure returns(uint){uint x;do{x++;continue;}while(x<2);return x;}
}
