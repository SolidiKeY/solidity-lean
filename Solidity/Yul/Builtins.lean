/-!
# Arity-indexed Osaka inline-Yul builtins

Pinned to solc 0.8.38 / Osaka. This table describes syntax and tier requirements;
it does not certify physical or world-effect semantics. Compiler-dependent
operations and CALLCODE remain represented so admission can refuse them precisely.
-/
namespace Solidity.Yul

inductive Tier where
  | A | B | C
  deriving DecidableEq, Repr

/-- The pure operations; every result is exactly one EVM word. -/
inductive Pure : Nat → Type where
  | «iszero» : Pure 1
  | «not» : Pure 1
  | «clz» : Pure 1
  | «add» : Pure 2
  | «sub» : Pure 2
  | «mul» : Pure 2
  | «div» : Pure 2
  | «sdiv» : Pure 2
  | «mod» : Pure 2
  | «smod» : Pure 2
  | «exp» : Pure 2
  | «lt» : Pure 2
  | «gt» : Pure 2
  | «slt» : Pure 2
  | «sgt» : Pure 2
  | «eq» : Pure 2
  | «and» : Pure 2
  | «or» : Pure 2
  | «xor» : Pure 2
  | «byte» : Pure 2
  | «shl» : Pure 2
  | «shr» : Pure 2
  | «sar» : Pure 2
  | «signextend» : Pure 2
  | «addmod» : Pure 3
  | «mulmod» : Pure 3
  deriving DecidableEq, Repr

def Pure.name {a : Nat} (p : Pure a) : String :=
  Pure.casesOn (motive := fun _ _ => String) p
    («iszero» := "iszero")
    («not» := "not")
    («clz» := "clz")
    («add» := "add")
    («sub» := "sub")
    («mul» := "mul")
    («div» := "div")
    («sdiv» := "sdiv")
    («mod» := "mod")
    («smod» := "smod")
    («exp» := "exp")
    («lt» := "lt")
    («gt» := "gt")
    («slt» := "slt")
    («sgt» := "sgt")
    («eq» := "eq")
    («and» := "and")
    («or» := "or")
    («xor» := "xor")
    («byte» := "byte")
    («shl» := "shl")
    («shr» := "shr")
    («sar» := "sar")
    («signextend» := "signextend")
    («addmod» := "addmod")
    («mulmod» := "mulmod")

/-- Input and output arities belong to the builtin type. -/
inductive Builtin : Nat → Nat → Type where
  | pure {a : Nat} : Pure a → Builtin a 1
  | «stop» : Builtin 0 0
  | «invalid» : Builtin 0 0
  | «address» : Builtin 0 1
  | «origin» : Builtin 0 1
  | «caller» : Builtin 0 1
  | «callvalue» : Builtin 0 1
  | «calldatasize» : Builtin 0 1
  | «codesize» : Builtin 0 1
  | «gasprice» : Builtin 0 1
  | «returndatasize» : Builtin 0 1
  | «coinbase» : Builtin 0 1
  | «timestamp» : Builtin 0 1
  | «number» : Builtin 0 1
  | «prevrandao» : Builtin 0 1
  | «gaslimit» : Builtin 0 1
  | «chainid» : Builtin 0 1
  | «selfbalance» : Builtin 0 1
  | «basefee» : Builtin 0 1
  | «blobbasefee» : Builtin 0 1
  | «msize» : Builtin 0 1
  | «gas» : Builtin 0 1
  | «pc» : Builtin 0 1
  | «balance» : Builtin 1 1
  | «calldataload» : Builtin 1 1
  | «extcodesize» : Builtin 1 1
  | «extcodehash» : Builtin 1 1
  | «blockhash» : Builtin 1 1
  | «blobhash» : Builtin 1 1
  | «mload» : Builtin 1 1
  | «sload» : Builtin 1 1
  | «tload» : Builtin 1 1
  | «pop» : Builtin 1 0
  | «selfdestruct» : Builtin 1 0
  | «mstore» : Builtin 2 0
  | «mstore8» : Builtin 2 0
  | «sstore» : Builtin 2 0
  | «tstore» : Builtin 2 0
  | «return» : Builtin 2 0
  | «revert» : Builtin 2 0
  | «log0» : Builtin 2 0
  | «keccak256» : Builtin 2 1
  | «calldatacopy» : Builtin 3 0
  | «codecopy» : Builtin 3 0
  | «returndatacopy» : Builtin 3 0
  | «mcopy» : Builtin 3 0
  | «log1» : Builtin 3 0
  | «create» : Builtin 3 1
  | «extcodecopy» : Builtin 4 0
  | «log2» : Builtin 4 0
  | «create2» : Builtin 4 1
  | «log3» : Builtin 5 0
  | «log4» : Builtin 6 0
  | «delegatecall» : Builtin 6 1
  | «staticcall» : Builtin 6 1
  | «call» : Builtin 7 1
  | «callcode» : Builtin 7 1
  deriving DecidableEq, Repr

def Builtin.name {a r : Nat} (b : Builtin a r) : String :=
  Builtin.casesOn (motive := fun _ _ _ => String) b
    (pure := fun p => p.name)
    («stop» := "stop")
    («invalid» := "invalid")
    («address» := "address")
    («origin» := "origin")
    («caller» := "caller")
    («callvalue» := "callvalue")
    («calldatasize» := "calldatasize")
    («codesize» := "codesize")
    («gasprice» := "gasprice")
    («returndatasize» := "returndatasize")
    («coinbase» := "coinbase")
    («timestamp» := "timestamp")
    («number» := "number")
    («prevrandao» := "prevrandao")
    («gaslimit» := "gaslimit")
    («chainid» := "chainid")
    («selfbalance» := "selfbalance")
    («basefee» := "basefee")
    («blobbasefee» := "blobbasefee")
    («msize» := "msize")
    («gas» := "gas")
    («pc» := "pc")
    («balance» := "balance")
    («calldataload» := "calldataload")
    («extcodesize» := "extcodesize")
    («extcodehash» := "extcodehash")
    («blockhash» := "blockhash")
    («blobhash» := "blobhash")
    («mload» := "mload")
    («sload» := "sload")
    («tload» := "tload")
    («pop» := "pop")
    («selfdestruct» := "selfdestruct")
    («mstore» := "mstore")
    («mstore8» := "mstore8")
    («sstore» := "sstore")
    («tstore» := "tstore")
    («return» := "return")
    («revert» := "revert")
    («log0» := "log0")
    («keccak256» := "keccak256")
    («calldatacopy» := "calldatacopy")
    («codecopy» := "codecopy")
    («returndatacopy» := "returndatacopy")
    («mcopy» := "mcopy")
    («log1» := "log1")
    («create» := "create")
    («extcodecopy» := "extcodecopy")
    («log2» := "log2")
    («create2» := "create2")
    («log3» := "log3")
    («log4» := "log4")
    («delegatecall» := "delegatecall")
    («staticcall» := "staticcall")
    («call» := "call")
    («callcode» := "callcode")

inductive Refusal where
  | compilerDependent (name : String)
  | unsupportedCallcode
  | needsTier (required : Tier)
  | nonMemorySafe
  | unknownBuiltin (name : String)
  deriving DecidableEq, Repr

/-- Required tier; `none` identifies intentionally refused operations. -/
def Builtin.tier {a r : Nat} (b : Builtin a r) : Option Tier :=
  Builtin.casesOn (motive := fun _ _ _ => Option Tier) b
    (pure := fun _ => some .A)
    («stop» := some .C)
    («invalid» := some .C)
    («address» := some .B)
    («origin» := some .B)
    («caller» := some .B)
    («callvalue» := some .B)
    («calldatasize» := some .B)
    («codesize» := none)
    («gasprice» := some .B)
    («returndatasize» := some .C)
    («coinbase» := some .B)
    («timestamp» := some .B)
    («number» := some .B)
    («prevrandao» := some .B)
    («gaslimit» := some .B)
    («chainid» := some .B)
    («selfbalance» := some .B)
    («basefee» := some .B)
    («blobbasefee» := some .B)
    («msize» := none)
    («gas» := none)
    («pc» := none)
    («balance» := some .B)
    («calldataload» := some .B)
    («extcodesize» := some .C)
    («extcodehash» := some .C)
    («blockhash» := some .B)
    («blobhash» := some .B)
    («mload» := some .B)
    («sload» := some .B)
    («tload» := some .B)
    («pop» := some .A)
    («selfdestruct» := some .C)
    («mstore» := some .B)
    («mstore8» := some .B)
    («sstore» := some .B)
    («tstore» := some .B)
    («return» := some .C)
    («revert» := some .C)
    («log0» := some .C)
    («keccak256» := some .B)
    («calldatacopy» := some .B)
    («codecopy» := none)
    («returndatacopy» := some .C)
    («mcopy» := some .B)
    («log1» := some .C)
    («create» := some .C)
    («extcodecopy» := some .C)
    («log2» := some .C)
    («create2» := some .C)
    («log3» := some .C)
    («log4» := some .C)
    («delegatecall» := some .C)
    («staticcall» := some .C)
    («call» := some .C)
    («callcode» := none)

def Tier.includes : Tier → Tier → Bool
  | .A, .A | .B, .A | .B, .B | .C, _ => true
  | _, _ => false

/-- Admission does not silently downgrade a compiler-dependent operation. -/
def Builtin.admit {a r : Nat} (tier : Tier) (b : Builtin a r) : Except Refusal Unit :=
  if b.name = "callcode" then .error .unsupportedCallcode
  else match b.tier with
    | none => .error (.compilerDependent b.name)
    | some required => if tier.includes required then .ok () else .error (.needsTier required)

/-- Metadata admission for general blocks. The pre-existing whole-buffer rethrow
exception is handled separately by its existing frontend contract. -/
def admitSafety (memorySafe : Bool) : Except Refusal Unit :=
  if memorySafe then .ok () else .error .nonMemorySafe

abbrev Entry := (a : Nat) × (r : Nat) × Builtin a r

/-- Exhaustive table of inline EVM builtins; object-dialect builtins are absent. -/
def builtins : List Entry := [
  ⟨1, 1, .pure .«iszero»⟩,
  ⟨1, 1, .pure .«not»⟩,
  ⟨1, 1, .pure .«clz»⟩,
  ⟨2, 1, .pure .«add»⟩,
  ⟨2, 1, .pure .«sub»⟩,
  ⟨2, 1, .pure .«mul»⟩,
  ⟨2, 1, .pure .«div»⟩,
  ⟨2, 1, .pure .«sdiv»⟩,
  ⟨2, 1, .pure .«mod»⟩,
  ⟨2, 1, .pure .«smod»⟩,
  ⟨2, 1, .pure .«exp»⟩,
  ⟨2, 1, .pure .«lt»⟩,
  ⟨2, 1, .pure .«gt»⟩,
  ⟨2, 1, .pure .«slt»⟩,
  ⟨2, 1, .pure .«sgt»⟩,
  ⟨2, 1, .pure .«eq»⟩,
  ⟨2, 1, .pure .«and»⟩,
  ⟨2, 1, .pure .«or»⟩,
  ⟨2, 1, .pure .«xor»⟩,
  ⟨2, 1, .pure .«byte»⟩,
  ⟨2, 1, .pure .«shl»⟩,
  ⟨2, 1, .pure .«shr»⟩,
  ⟨2, 1, .pure .«sar»⟩,
  ⟨2, 1, .pure .«signextend»⟩,
  ⟨3, 1, .pure .«addmod»⟩,
  ⟨3, 1, .pure .«mulmod»⟩,
  ⟨0, 0, .«stop»⟩,
  ⟨0, 0, .«invalid»⟩,
  ⟨0, 1, .«address»⟩,
  ⟨0, 1, .«origin»⟩,
  ⟨0, 1, .«caller»⟩,
  ⟨0, 1, .«callvalue»⟩,
  ⟨0, 1, .«calldatasize»⟩,
  ⟨0, 1, .«codesize»⟩,
  ⟨0, 1, .«gasprice»⟩,
  ⟨0, 1, .«returndatasize»⟩,
  ⟨0, 1, .«coinbase»⟩,
  ⟨0, 1, .«timestamp»⟩,
  ⟨0, 1, .«number»⟩,
  ⟨0, 1, .«prevrandao»⟩,
  ⟨0, 1, .«gaslimit»⟩,
  ⟨0, 1, .«chainid»⟩,
  ⟨0, 1, .«selfbalance»⟩,
  ⟨0, 1, .«basefee»⟩,
  ⟨0, 1, .«blobbasefee»⟩,
  ⟨0, 1, .«msize»⟩,
  ⟨0, 1, .«gas»⟩,
  ⟨0, 1, .«pc»⟩,
  ⟨1, 1, .«balance»⟩,
  ⟨1, 1, .«calldataload»⟩,
  ⟨1, 1, .«extcodesize»⟩,
  ⟨1, 1, .«extcodehash»⟩,
  ⟨1, 1, .«blockhash»⟩,
  ⟨1, 1, .«blobhash»⟩,
  ⟨1, 1, .«mload»⟩,
  ⟨1, 1, .«sload»⟩,
  ⟨1, 1, .«tload»⟩,
  ⟨1, 0, .«pop»⟩,
  ⟨1, 0, .«selfdestruct»⟩,
  ⟨2, 0, .«mstore»⟩,
  ⟨2, 0, .«mstore8»⟩,
  ⟨2, 0, .«sstore»⟩,
  ⟨2, 0, .«tstore»⟩,
  ⟨2, 0, .«return»⟩,
  ⟨2, 0, .«revert»⟩,
  ⟨2, 0, .«log0»⟩,
  ⟨2, 1, .«keccak256»⟩,
  ⟨3, 0, .«calldatacopy»⟩,
  ⟨3, 0, .«codecopy»⟩,
  ⟨3, 0, .«returndatacopy»⟩,
  ⟨3, 0, .«mcopy»⟩,
  ⟨3, 0, .«log1»⟩,
  ⟨3, 1, .«create»⟩,
  ⟨4, 0, .«extcodecopy»⟩,
  ⟨4, 0, .«log2»⟩,
  ⟨4, 1, .«create2»⟩,
  ⟨5, 0, .«log3»⟩,
  ⟨6, 0, .«log4»⟩,
  ⟨6, 1, .«delegatecall»⟩,
  ⟨6, 1, .«staticcall»⟩,
  ⟨7, 1, .«call»⟩,
  ⟨7, 1, .«callcode»⟩]

def lookupBuiltin (name : String) : Option Entry :=
  builtins.find? (fun e => e.2.2.name == name)

end Solidity.Yul
