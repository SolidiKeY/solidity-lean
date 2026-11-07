// SPDX-License-Identifier: MIT
pragma solidity ^0.8.38;
contract C{function f() public{assembly{let a,b:=pair() let c a,b:=pair() a:=1 if a{pop(b)} for{let i:=0}lt(i,2){i:=add(i,1)}{if eq(i,1){continue}break} switch a case 0{} default{} switch b default{} function pair()->x,y{x:=0x10 y:=true leave} function identity(x)->y{y:=x} {}}}}
