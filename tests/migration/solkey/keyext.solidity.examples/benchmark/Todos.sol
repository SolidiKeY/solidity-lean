// Source: https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/structs/Structs.sol
// Changes: create() is dropped (the struct constructors Todo(..) and Todo({..}) do not load;
// it takes a string, so it has no obligation either).
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract Todos {
    struct Todo {
        string text;
        bool completed;
    }

    // An array of 'Todo' structs
    Todo[] public todos;

    // Solidity automatically creates a getter for 'todos' so
    // you don't actually need this function.
    function get(uint256 _index)
        public
        view
        returns (string memory text, bool completed)
    {
        Todo storage todo = todos[_index];
        return (todo.text, todo.completed);
    }

    // update text
    function updateText(uint256 _index, string calldata _text) public {
        Todo storage todo = todos[_index];
        todo.text = _text;
    }

    // update completed
    /// @custom:key requires _index < todos.length
    /// @custom:key ensures todos[_index].completed == !\old(todos[_index].completed)
    /// @custom:key ensures todos.length == \old(todos.length)
    function toggleCompleted(uint256 _index) public {
        Todo storage todo = todos[_index];
        todo.completed = !todo.completed;
    }
}
