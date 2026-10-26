// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;

contract RecursiveTypesConformance {
    struct MapNode { uint value; mapping(uint => MapNode) next; }
    struct Node { uint value; Node[] children; }
    struct A { B[] children; }
    struct B { A[] children; }
    struct FixedGuard { FixedGuard[][2] children; }
    MapNode private mapped;
    Node private tree;
    A private mutualRoot;

    function mappingDefault() external view returns (uint) {
        return mapped.next[1].next[2].next[3].value;
    }
    function mappingDelete() external returns (uint, uint, uint) {
        mapped.value = 5;
        mapped.next[1].value = 7;
        mapped.next[1].next[2].value = 9;
        delete mapped;
        return (mapped.value, mapped.next[1].value, mapped.next[1].next[2].value);
    }
    function arrayDelete() external returns (uint, uint, uint) {
        tree.value = 5;
        tree.children.push();
        tree.children[0].value = 7;
        tree.children[0].children.push();
        tree.children[0].children[0].value = 9;
        delete tree;
        uint oldLength = tree.children.length;
        tree.children.push();
        return (oldLength, tree.children[0].value, tree.children[0].children.length);
    }
    function retainedWrite() external returns (uint) {
        delete tree;
        tree.children.push();
        Node storage alias_ = tree.children[0];
        tree.children.pop();
        alias_.value = 7;
        tree.children.push();
        return tree.children[0].value;
    }
    function mutualDepth() external returns (uint) {
        mutualRoot.children.push();
        mutualRoot.children[0].children.push();
        return mutualRoot.children[0].children[0].children.length;
    }
    function memoryCycle() external pure returns (uint) {
        Node memory node = Node({value: 2, children: new Node[](1)});
        node.children[0] = node;
        node.children[0].value = 9;
        return node.value;
    }
}
