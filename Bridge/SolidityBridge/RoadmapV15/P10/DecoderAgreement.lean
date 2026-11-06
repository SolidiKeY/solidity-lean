import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer

/-! G45.05-BR: actual Backend opcode bytes versus the pinned reference decoder.
The pin has no CLZ constructor/parser entry: its actual INVALID fallback stays explicit.
This adapter asserts decoding only, never Osaka execution or profile exclusion. -/
namespace SolidityBridge.RoadmapV15.P10.DecoderAgreement
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Actual decode target in the EXISTING reference datatype. CLZ maps to INVALID,
not to a valid implementation of Osaka CLZ. -/
def referenceOp : Backend.Op → Operation .EVM
  | .STOP => .STOP
  | .ADD => .ADD
  | .MUL => .MUL
  | .SUB => .SUB
  | .DIV => .DIV
  | .SDIV => .SDIV
  | .MOD => .MOD
  | .SMOD => .SMOD
  | .ADDMOD => .ADDMOD
  | .MULMOD => .MULMOD
  | .EXP => .EXP
  | .SIGNEXTEND => .SIGNEXTEND
  | .LT => .LT
  | .GT => .GT
  | .SLT => .SLT
  | .SGT => .SGT
  | .EQ => .EQ
  | .ISZERO => .ISZERO
  | .AND => .AND
  | .OR => .OR
  | .XOR => .XOR
  | .NOT => .NOT
  | .BYTE => .BYTE
  | .SHL => .SHL
  | .SHR => .SHR
  | .SAR => .SAR
  | .CLZ => .INVALID
  | .KECCAK256 => .KECCAK256
  | .ADDRESS => .ADDRESS
  | .BALANCE => .BALANCE
  | .ORIGIN => .ORIGIN
  | .CALLER => .CALLER
  | .CALLVALUE => .CALLVALUE
  | .CALLDATALOAD => .CALLDATALOAD
  | .CALLDATASIZE => .CALLDATASIZE
  | .CALLDATACOPY => .CALLDATACOPY
  | .CODESIZE => .CODESIZE
  | .CODECOPY => .CODECOPY
  | .GASPRICE => .GASPRICE
  | .EXTCODESIZE => .EXTCODESIZE
  | .EXTCODECOPY => .EXTCODECOPY
  | .RETURNDATASIZE => .RETURNDATASIZE
  | .RETURNDATACOPY => .RETURNDATACOPY
  | .EXTCODEHASH => .EXTCODEHASH
  | .BLOCKHASH => .BLOCKHASH
  | .COINBASE => .COINBASE
  | .TIMESTAMP => .TIMESTAMP
  | .NUMBER => .NUMBER
  | .PREVRANDAO => .PREVRANDAO
  | .GASLIMIT => .GASLIMIT
  | .CHAINID => .CHAINID
  | .SELFBALANCE => .SELFBALANCE
  | .BASEFEE => .BASEFEE
  | .BLOBHASH => .BLOBHASH
  | .BLOBBASEFEE => .BLOBBASEFEE
  | .POP => .POP
  | .MLOAD => .MLOAD
  | .MSTORE => .MSTORE
  | .MSTORE8 => .MSTORE8
  | .SLOAD => .SLOAD
  | .SSTORE => .SSTORE
  | .JUMP => .JUMP
  | .JUMPI => .JUMPI
  | .PC => .PC
  | .MSIZE => .MSIZE
  | .GAS => .GAS
  | .JUMPDEST => .JUMPDEST
  | .TLOAD => .TLOAD
  | .TSTORE => .TSTORE
  | .MCOPY => .MCOPY
  | .CREATE => .CREATE
  | .CALL => .CALL
  | .CALLCODE => .CALLCODE
  | .RETURN => .RETURN
  | .DELEGATECALL => .DELEGATECALL
  | .CREATE2 => .CREATE2
  | .STATICCALL => .STATICCALL
  | .REVERT => .REVERT
  | .INVALID => .INVALID
  | .SELFDESTRUCT => .SELFDESTRUCT
  | .DUP n => dupCode n
  | .SWAP n => swapCode n
  | .LOG n => (match n.val with
      | 0 => .LOG0 | 1 => .LOG1 | 2 => .LOG2 | 3 => .LOG3 | _ => .LOG4)

theorem parser_agreement (op : Backend.Op) :
    EVM.parseInstr op.code = some (referenceOp op) := by
  cases op <;> try rfl
  all_goals rename_i n; fin_cases n <;> rfl

/-- Precisely identifies native INVALID mapping; no semantic profile exclusion. -/
theorem invalid_iff (op : Backend.Op) :
    referenceOp op = .INVALID ↔ op = .CLZ ∨ op = .INVALID := by
  cases op <;> try decide
  all_goals rename_i n; fin_cases n <;> decide

theorem no_immediate (op : Backend.Op) :
    EVM.argOnNBytesOfInstr (referenceOp op) = 0 := by
  cases op <;> try rfl
  all_goals rename_i n; fin_cases n <;> rfl

private theorem opcode_at {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some op.code := by
  change (Backend.encode (site.before ++ .op op :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

/-- All117 non-immediate Backend instructions, including actual CLZ→INVALID. -/
theorem decode_all {op : Backend.Op} (site : Site op) :
    EVM.decode site.state.executionEnv.code site.state.pc =
      some (referenceOp op,none) := by
  have byte := opcode_at site
  simp only [EVM.decode,Site.pc_nat,byte,bind,Option.bind,parser_agreement,
    no_immediate,beq_self_eq_true,ite_true]

/-- Actual fetched dispatch; resource, state and fuel behavior remain native. -/
theorem fetched_dispatch {op : Backend.Op} (site : Site op) (fuel cost : Nat) :
    EVM.step (fuel+1) cost none site.state =
      EVM.step (fuel+1) cost (some (referenceOp op,none)) site.state := by
  have decoded := decode_all site
  simp only [EVM.step,EVM.fetchInstr,decoded,Option.option,bind,Except.bind]
  rfl

/-- The unsupported Osaka instruction decodes as INVALID in this pin. -/
theorem clz_invalid (site : Site .CLZ) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.INVALID,none) :=
  decode_all site

#print axioms parser_agreement
#print axioms invalid_iff
#print axioms no_immediate
#print axioms decode_all
#print axioms fetched_dispatch
#print axioms clz_invalid
end SolidityBridge.RoadmapV15.P10.DecoderAgreement
