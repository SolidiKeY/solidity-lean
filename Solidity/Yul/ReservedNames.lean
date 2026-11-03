import Solidity.Yul.Builtins

/-! Strict inline-Yul identifier reservations for solc 0.8.38/Osaka.
Pinned EVMDialect.cpp createReservedIdentifiers takes all lowercased keys of
Instruction.cpp c_instructions, except SLOTNUM before Amsterdam, plus the six
object-related names below. Object-access-only verbatim prefixes are NOT
reserved in inline assembly. This is reservation policy, not executable builtins.
Instruction.cpp SHA256 9bd5f4c74aae55b771c4381b6134e71a875deec0039588e7b75c29157a8cc4ce.
The external source/corpus audit is separate from the kernel facts below. -/
namespace Solidity.Yul

def reservedNames : List String :=
  [
    "stop", "add", "sub", "mul", "div", "sdiv",
    "mod", "smod", "exp", "not", "lt", "gt",
    "slt", "sgt", "eq", "iszero", "and", "or",
    "xor", "byte", "shl", "shr", "sar", "clz",
    "addmod", "mulmod", "signextend", "keccak256", "address", "balance",
    "origin", "caller", "callvalue", "calldataload", "calldatasize", "calldatacopy",
    "codesize", "codecopy", "gasprice", "extcodesize", "extcodecopy", "returndatasize",
    "returndatacopy", "mcopy", "extcodehash", "blockhash", "blobhash", "coinbase",
    "timestamp", "number", "difficulty", "prevrandao", "gaslimit", "chainid",
    "selfbalance", "basefee", "blobbasefee", "pop", "mload", "mstore",
    "mstore8", "sload", "sstore", "tload", "tstore", "jump",
    "jumpi", "pc", "msize", "gas", "jumpdest", "push0",
    "push1", "push2", "push3", "push4", "push5", "push6",
    "push7", "push8", "push9", "push10", "push11", "push12",
    "push13", "push14", "push15", "push16", "push17", "push18",
    "push19", "push20", "push21", "push22", "push23", "push24",
    "push25", "push26", "push27", "push28", "push29", "push30",
    "push31", "push32", "dup1", "dup2", "dup3", "dup4",
    "dup5", "dup6", "dup7", "dup8", "dup9", "dup10",
    "dup11", "dup12", "dup13", "dup14", "dup15", "dup16",
    "swap1", "swap2", "swap3", "swap4", "swap5", "swap6",
    "swap7", "swap8", "swap9", "swap10", "swap11", "swap12",
    "swap13", "swap14", "swap15", "swap16", "log0", "log1",
    "log2", "log3", "log4", "create", "call", "callcode",
    "staticcall", "return", "delegatecall", "create2", "revert", "invalid",
    "selfdestruct", "linkersymbol", "datasize", "dataoffset", "datacopy", "setimmutable",
    "loadimmutable"
  ]

theorem reservedNames_count : reservedNames.length = 157 := rfl

theorem slotnum_not_reserved : "slotnum" ∉ reservedNames := by decide

end Solidity.Yul
