import Solidity.Source.Syntax

/-!
# Tokens of the checked lexer (G08)

The lexical classes of the pinned ANTLR lexer (`SolidityLexer.g4` of solc
0.8.38, vendored as `tests/upstream/grammar-0.8.38/`), as the values the
parser reads.  A token holds what the parse needs and nothing of its
spelling: `uint` and `uint256` are one token (`Elem.int false 256`), a
string literal is its bytes after escapes, a decimal number its exact
mantissa, fractional digit count and exponent (S00's `NumLit`).  The
spelling is kept in the lexer's pieces (`Piece.raw`,
`Solidity/Frontend/Checked/Lexer.lean`), which re-print the input exactly.

Words the grammar's `identifier` rule admits (`from`, `error`, `revert`,
`global`, `transient`, `layout`, `at`) are identifiers here; the parser reads
them by context, as the grammar does.  The reserved keywords
(`ReservedKeywords`) are not tokens: the lexer refuses them.  Yul keywords
(`YulKw`) are tokens only inside an assembly block, where Solidity keywords
are identifiers.

The source is bytes (G05's `SourceUnit.bytes`), not characters: every
lexical class is ASCII except comments and `unicode"…"` literals, whose
content is kept as bytes.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- Source bytes. -/
abbrev Bytes := List UInt8

/-- The bytes of an ASCII string. -/
def ascii (s : String) : Bytes := s.toList.map fun c => c.toNat.toUInt8

/-- The string of ASCII bytes (identifiers and pragma words). -/
def Bytes.str (b : Bytes) : String := ⟨b.map fun c => Char.ofNat c.toNat⟩

/-- The Solidity keywords that are tokens of their own (the lexer's keyword
rules, without the elementary type names, the units and the booleans). -/
inductive Kw where
  | abstract | anonymous | as_ | assembly | break_ | calldata | catch_ | constant
  | constructor | continue_ | contract | delete | do_ | else_ | emit | enum | event
  | external | fallback | for_ | function | hex | if_ | immutable | import_ | indexed
  | interface | internal | is | library | mapping | memory | modifier | new | override
  | payable | pragma | private_ | public_ | pure | receive | return_ | returns | storage
  | struct | try_ | type_ | unchecked | unicode | using | view | virtual | while_
  deriving DecidableEq, Repr

/-- Every keyword. -/
def Kw.all : List Kw :=
  [.abstract, .anonymous, .as_, .assembly, .break_, .calldata, .catch_, .constant,
    .constructor, .continue_, .contract, .delete, .do_, .else_, .emit, .enum, .event,
    .external, .fallback, .for_, .function, .hex, .if_, .immutable, .import_, .indexed,
    .interface, .internal, .is, .library, .mapping, .memory, .modifier, .new, .override,
    .payable, .pragma, .private_, .public_, .pure, .receive, .return_, .returns, .storage,
    .struct, .try_, .type_, .unchecked, .unicode, .using, .view, .virtual, .while_]

/-- A keyword's spelling. -/
def Kw.spell : Kw → String
  | .abstract => "abstract" | .anonymous => "anonymous" | .as_ => "as"
  | .assembly => "assembly" | .break_ => "break" | .calldata => "calldata"
  | .catch_ => "catch" | .constant => "constant" | .constructor => "constructor"
  | .continue_ => "continue" | .contract => "contract" | .delete => "delete"
  | .do_ => "do" | .else_ => "else" | .emit => "emit" | .enum => "enum"
  | .event => "event" | .external => "external" | .fallback => "fallback"
  | .for_ => "for" | .function => "function" | .hex => "hex" | .if_ => "if"
  | .immutable => "immutable" | .import_ => "import" | .indexed => "indexed"
  | .interface => "interface" | .internal => "internal" | .is => "is"
  | .library => "library" | .mapping => "mapping" | .memory => "memory"
  | .modifier => "modifier" | .new => "new" | .override => "override"
  | .payable => "payable" | .pragma => "pragma" | .private_ => "private"
  | .public_ => "public" | .pure => "pure" | .receive => "receive"
  | .return_ => "return" | .returns => "returns" | .storage => "storage"
  | .struct => "struct" | .try_ => "try" | .type_ => "type" | .unchecked => "unchecked"
  | .unicode => "unicode" | .using => "using" | .view => "view" | .virtual => "virtual"
  | .while_ => "while"

/-- The keywords reserved for future use (`ReservedKeywords`): refused. -/
def reservedKeywords : List String :=
  ["after", "alias", "apply", "auto", "byte", "case", "copyof", "default", "define", "final",
    "implements", "in", "inline", "let", "macro", "match", "mutable", "null", "of",
    "partial", "promise", "reference", "relocatable", "sealed", "sizeof", "static",
    "supports", "switch", "typedef", "typeof", "var"]

/-- The keywords of Yul (`YulMode`), tokens inside assembly only.  `true` and
`false` are `Tok.bool`, `hex"…"` a `Tok.hexStr`. -/
inductive YulKw where
  | break_ | case | continue_ | default | for_ | function | if_ | leave | let_ | switch
  deriving DecidableEq, Repr

def YulKw.all : List YulKw :=
  [.break_, .case, .continue_, .default, .for_, .function, .if_, .leave, .let_, .switch]

def YulKw.spell : YulKw → String
  | .break_ => "break" | .case => "case" | .continue_ => "continue" | .default => "default"
  | .for_ => "for" | .function => "function" | .if_ => "if" | .leave => "leave"
  | .let_ => "let" | .switch => "switch"

/-- Punctuation and operators, Solidity's and Yul's (`:=`). -/
inductive Punct where
  | lparen | rparen | lbrack | rbrack | lbrace | rbrace | colon | semi | period
  | question | doubleArrow | rightArrow | assign | assignBitOr | assignBitXor
  | assignBitAnd | assignShl | assignSar | assignShr | assignAdd | assignSub | assignMul
  | assignDiv | assignMod | comma | or | and | bitOr | bitXor | bitAnd | shl | sar | shr
  | add | sub | mul | div | mod | exp | equal | notEqual | lt | gt | le | ge | not
  | bitNot | inc | dec | yulAssign
  deriving DecidableEq, Repr

/-- Every punctuation token, longest spellings first (maximal munch). -/
def Punct.all : List Punct :=
  [.assignShr, .assignShl, .assignSar, .shr, .doubleArrow, .rightArrow, .assignBitOr,
    .assignBitXor, .assignBitAnd, .assignAdd, .assignSub, .assignMul, .assignDiv, .assignMod,
    .or, .and, .shl, .sar, .exp, .equal, .notEqual, .le, .ge, .inc, .dec, .yulAssign,
    .lparen, .rparen, .lbrack, .rbrack, .lbrace, .rbrace, .colon, .semi, .period,
    .question, .assign, .comma, .bitOr, .bitXor, .bitAnd, .add, .sub, .mul, .div, .mod,
    .lt, .gt, .not, .bitNot]

def Punct.spell : Punct → String
  | .lparen => "(" | .rparen => ")" | .lbrack => "[" | .rbrack => "]" | .lbrace => "{"
  | .rbrace => "}" | .colon => ":" | .semi => ";" | .period => "." | .question => "?"
  | .doubleArrow => "=>" | .rightArrow => "->" | .assign => "=" | .assignBitOr => "|="
  | .assignBitXor => "^=" | .assignBitAnd => "&=" | .assignShl => "<<="
  | .assignSar => ">>=" | .assignShr => ">>>=" | .assignAdd => "+=" | .assignSub => "-="
  | .assignMul => "*=" | .assignDiv => "/=" | .assignMod => "%=" | .comma => ","
  | .or => "||" | .and => "&&" | .bitOr => "|" | .bitXor => "^" | .bitAnd => "&"
  | .shl => "<<" | .sar => ">>" | .shr => ">>>" | .add => "+" | .sub => "-" | .mul => "*"
  | .div => "/" | .mod => "%" | .exp => "**" | .equal => "==" | .notEqual => "!="
  | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">=" | .not => "!" | .bitNot => "~"
  | .inc => "++" | .dec => "--" | .yulAssign => ":="

/-- A token. -/
inductive Tok where
  | kw (k : Kw)
  | punct (p : Punct)
  /-- An elementary type keyword: `address`, `bool`, `string`, `bytes`,
  `intM`/`uintM`, `bytesN`, `fixed…`/`ufixed…`.  Never `addressPayable`. -/
  | elem (e : Elem)
  /-- A `SubDenomination` keyword. -/
  | denom (d : Denom)
  | bool (b : Bool)
  | ident (s : String)
  | num (n : NumLit)
  /-- One string-literal fragment's bytes after escapes. -/
  | str (b : Bytes)
  | hexStr (b : Bytes)
  | unicodeStr (b : Bytes)
  /-- A whitespace-separated word of a pragma. -/
  | pragmaWord (w : String)
  | yulKw (k : YulKw)
  /-- A Yul decimal or hexadecimal number. -/
  | yulDec (n : Nat)
  | yulHex (n : Nat)
  deriving DecidableEq, Repr

/-- The lexical classes of tokens, for the coverage table. -/
inductive TokClass where
  | kw | punct | elem | denom | bool | ident | num | str | hexStr | unicodeStr
  | pragmaWord | yulKw | yulDec | yulHex
  deriving DecidableEq, Repr

def Tok.cls : Tok → TokClass
  | .kw _ => .kw | .punct _ => .punct | .elem _ => .elem | .denom _ => .denom
  | .bool _ => .bool | .ident _ => .ident | .num _ => .num | .str _ => .str
  | .hexStr _ => .hexStr | .unicodeStr _ => .unicodeStr | .pragmaWord _ => .pragmaWord
  | .yulKw _ => .yulKw | .yulDec _ => .yulDec | .yulHex _ => .yulHex

def TokClass.all : List TokClass :=
  [.kw, .punct, .elem, .denom, .bool, .ident, .num, .str, .hexStr, .unicodeStr,
    .pragmaWord, .yulKw, .yulDec, .yulHex]

/-- Whitespace and comments.  A NatSpec comment (`///…`, `/** … */`) is
trivia too, flagged: the parse does not read documentation. -/
inductive Trivia where
  | ws
  | line (natspec : Bool)
  | block (natspec : Bool)
  deriving DecidableEq, Repr

/-- What a piece of source is. -/
inductive Kind where
  | trivia (t : Trivia)
  | tok (t : Tok)
  deriving DecidableEq, Repr

/-- A piece of the source: its kind and its exact bytes. -/
structure Piece where
  kind : Kind
  raw : Bytes
  deriving DecidableEq, Repr

/-- A token with its source range `[start, stop)`, byte offsets. -/
structure Located where
  tok : Tok
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- A located error: the byte offset and a message. -/
structure Error where
  pos : Nat
  msg : String
  deriving DecidableEq, Repr

end Solidity.Frontend.Checked
