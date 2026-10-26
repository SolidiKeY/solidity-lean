// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;

contract RecursiveCopyConformance {
    struct Node { uint value; Node[] children; }
    Node private source;
    Node private destination;
    Node private fresh;

    function recursiveCopy() external returns (uint, uint, uint, uint, uint, uint) {
        delete source;
        delete destination;
        source.value = 5;
        source.children.push();
        source.children[0].value = 7;
        source.children[0].children.push();
        source.children[0].children[0].value = 9;
        destination.children.push();
        destination.children.push();
        Node storage shortened = destination.children[1];
        shortened.value = 15;
        shortened.children.push();
        shortened.children[0].value = 19;
        destination = source;
        return (destination.value, destination.children.length,
            destination.children[0].value, destination.children[0].children[0].value,
            shortened.value, shortened.children.length);
    }

    function retainedDestination() external returns (uint) {
        delete source;
        delete destination;
        destination.children.push();
        Node storage retained = destination.children[0];
        destination.children.pop();
        retained.value = 13;
        destination = source;
        destination.children.push();
        return destination.children[0].value;
    }

    function ignoredSourceShadow() external returns (uint) {
        delete source;
        source.children.push();
        Node storage retained = source.children[0];
        source.children.pop();
        retained.value = 17;
        fresh = source;
        fresh.children.push();
        return fresh.children[0].value;
    }

    function ordinarySubtree() external returns (uint, uint) {
        delete destination;
        destination.children.push();
        uint ordinary = 31;
        destination.value = ordinary;
        destination.children[0].value = ordinary + 6;
        return (destination.value, destination.children[0].value);
    }
}
