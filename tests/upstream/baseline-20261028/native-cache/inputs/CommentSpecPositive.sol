pragma solidity ^0.8.0;
contract CommentSpecPositive {
 /// @custom:key requires from /- « ignored /- from -/ » -/ == 7
 /// @custom:key ensures from == 7
 function comments(uint from) public pure {}
}
