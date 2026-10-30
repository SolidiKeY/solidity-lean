import Solidity.Frontend.Checked.Lexer

/-!
# Lexer controls and coverage (G08)

Kernel-checked witnesses for the checked lexer
(`Solidity/Frontend/Checked/Lexer.lean`):

* **coverage of the pinned lexical classes**: `lexRules` names every lexer
  rule of `SolidityLexer.g4` (all four modes; `scripts/check-checked-frontend.mjs`
  checks the names against the file) with a sample lexeme and what the
  lexer makes of it, and `lexRules_classified` proves each sample is
  classified so (`decide +kernel`); `lexRules_cover` proves every token class
  is produced by some rule;
* the byte tables agree with the spellings (`Kw.bytes_spell`, …);
* nontrivial accepted inputs with their tokens and ranges, and negative
  controls: each refused class with its located error.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- What a lexer rule yields. -/
inductive LexRule where
  | tok (c : TokClass)
  | trivia
  /-- Scanned by the ANTLR lexer but used by no parser rule, or reserved:
  refused. -/
  | refused
  deriving DecidableEq, Repr

def LexRule.accepts : LexRule → Option Kind → Bool
  | .tok c, some (.tok t) => t.cls == c
  | .trivia, some (.trivia _) => true
  | .refused, none => true
  | _, _ => false

/-- Every rule of `SolidityLexer.g4`, its mode, a sample lexeme and its
class. -/
def lexRules : List (String × Mode × String × LexRule) := [
  ("ReservedKeywords", .sol, "after", .refused),
  ("Abstract", .sol, "abstract", .tok .kw),
  ("Address", .sol, "address", .tok .elem),
  ("Anonymous", .sol, "anonymous", .tok .kw),
  ("As", .sol, "as", .tok .kw),
  ("Assembly", .sol, "assembly", .tok .kw),
  ("At", .sol, "at", .tok .ident),
  ("Bool", .sol, "bool", .tok .elem),
  ("Break", .sol, "break", .tok .kw),
  ("Bytes", .sol, "bytes", .tok .elem),
  ("Calldata", .sol, "calldata", .tok .kw),
  ("Catch", .sol, "catch", .tok .kw),
  ("Constant", .sol, "constant", .tok .kw),
  ("Constructor", .sol, "constructor", .tok .kw),
  ("Continue", .sol, "continue", .tok .kw),
  ("Contract", .sol, "contract", .tok .kw),
  ("Delete", .sol, "delete", .tok .kw),
  ("Do", .sol, "do", .tok .kw),
  ("Else", .sol, "else", .tok .kw),
  ("Emit", .sol, "emit", .tok .kw),
  ("Enum", .sol, "enum", .tok .kw),
  ("Error", .sol, "error", .tok .ident),
  ("Event", .sol, "event", .tok .kw),
  ("External", .sol, "external", .tok .kw),
  ("Fallback", .sol, "fallback", .tok .kw),
  ("False", .sol, "false", .tok .bool),
  ("Fixed", .sol, "fixed128x18", .tok .elem),
  ("FixedBytes", .sol, "bytes32", .tok .elem),
  ("For", .sol, "for", .tok .kw),
  ("From", .sol, "from", .tok .ident),
  ("Function", .sol, "function", .tok .kw),
  ("Global", .sol, "global", .tok .ident),
  ("Hex", .sol, "hex", .tok .kw),
  ("If", .sol, "if", .tok .kw),
  ("Immutable", .sol, "immutable", .tok .kw),
  ("Import", .sol, "import", .tok .kw),
  ("Indexed", .sol, "indexed", .tok .kw),
  ("Interface", .sol, "interface", .tok .kw),
  ("Internal", .sol, "internal", .tok .kw),
  ("Is", .sol, "is", .tok .kw),
  ("Layout", .sol, "layout", .tok .ident),
  ("Library", .sol, "library", .tok .kw),
  ("Mapping", .sol, "mapping", .tok .kw),
  ("Memory", .sol, "memory", .tok .kw),
  ("Modifier", .sol, "modifier", .tok .kw),
  ("New", .sol, "new", .tok .kw),
  ("SubDenomination", .sol, "gwei", .tok .denom),
  ("Override", .sol, "override", .tok .kw),
  ("Payable", .sol, "payable", .tok .kw),
  ("Pragma", .sol, "pragma", .tok .kw),
  ("Private", .sol, "private", .tok .kw),
  ("Public", .sol, "public", .tok .kw),
  ("Pure", .sol, "pure", .tok .kw),
  ("Receive", .sol, "receive", .tok .kw),
  ("Return", .sol, "return", .tok .kw),
  ("Returns", .sol, "returns", .tok .kw),
  ("Revert", .sol, "revert", .tok .ident),
  ("SignedIntegerType", .sol, "int8", .tok .elem),
  ("Storage", .sol, "storage", .tok .kw),
  ("String", .sol, "string", .tok .elem),
  ("Struct", .sol, "struct", .tok .kw),
  ("Transient", .sol, "transient", .tok .ident),
  ("True", .sol, "true", .tok .bool),
  ("Try", .sol, "try", .tok .kw),
  ("Type", .sol, "type", .tok .kw),
  ("Ufixed", .sol, "ufixed", .tok .elem),
  ("Unchecked", .sol, "unchecked", .tok .kw),
  ("Unicode", .sol, "unicode", .tok .kw),
  ("UnsignedIntegerType", .sol, "uint256", .tok .elem),
  ("Using", .sol, "using", .tok .kw),
  ("View", .sol, "view", .tok .kw),
  ("Virtual", .sol, "virtual", .tok .kw),
  ("While", .sol, "while", .tok .kw),
  ("LParen", .sol, "(", .tok .punct),
  ("RParen", .sol, ")", .tok .punct),
  ("LBrack", .sol, "[", .tok .punct),
  ("RBrack", .sol, "]", .tok .punct),
  ("LBrace", .sol, "{", .tok .punct),
  ("RBrace", .sol, "}", .tok .punct),
  ("Colon", .sol, ":", .tok .punct),
  ("Semicolon", .sol, ";", .tok .punct),
  ("Period", .sol, ".", .tok .punct),
  ("Conditional", .sol, "?", .tok .punct),
  ("DoubleArrow", .sol, "=>", .tok .punct),
  ("RightArrow", .sol, "->", .tok .punct),
  ("Assign", .sol, "=", .tok .punct),
  ("AssignBitOr", .sol, "|=", .tok .punct),
  ("AssignBitXor", .sol, "^=", .tok .punct),
  ("AssignBitAnd", .sol, "&=", .tok .punct),
  ("AssignShl", .sol, "<<=", .tok .punct),
  ("AssignSar", .sol, ">>=", .tok .punct),
  ("AssignShr", .sol, ">>>=", .tok .punct),
  ("AssignAdd", .sol, "+=", .tok .punct),
  ("AssignSub", .sol, "-=", .tok .punct),
  ("AssignMul", .sol, "*=", .tok .punct),
  ("AssignDiv", .sol, "/=", .tok .punct),
  ("AssignMod", .sol, "%=", .tok .punct),
  ("Comma", .sol, ",", .tok .punct),
  ("Or", .sol, "||", .tok .punct),
  ("And", .sol, "&&", .tok .punct),
  ("BitOr", .sol, "|", .tok .punct),
  ("BitXor", .sol, "^", .tok .punct),
  ("BitAnd", .sol, "&", .tok .punct),
  ("Shl", .sol, "<<", .tok .punct),
  ("Sar", .sol, ">>", .tok .punct),
  ("Shr", .sol, ">>>", .tok .punct),
  ("Add", .sol, "+", .tok .punct),
  ("Sub", .sol, "-", .tok .punct),
  ("Mul", .sol, "*", .tok .punct),
  ("Div", .sol, "/", .tok .punct),
  ("Mod", .sol, "%", .tok .punct),
  ("Exp", .sol, "**", .tok .punct),
  ("Equal", .sol, "==", .tok .punct),
  ("NotEqual", .sol, "!=", .tok .punct),
  ("LessThan", .sol, "<", .tok .punct),
  ("GreaterThan", .sol, ">", .tok .punct),
  ("LessThanOrEqual", .sol, "<=", .tok .punct),
  ("GreaterThanOrEqual", .sol, ">=", .tok .punct),
  ("Not", .sol, "!", .tok .punct),
  ("BitNot", .sol, "~", .tok .punct),
  ("Inc", .sol, "++", .tok .punct),
  ("Dec", .sol, "--", .tok .punct),
  ("DoubleQuote", .sol, "\"", .refused),
  ("SingleQuote", .sol, "'", .refused),
  ("NonEmptyStringLiteral", .sol, "\"a\\n\"", .tok .str),
  ("EmptyStringLiteral", .sol, "''", .tok .str),
  ("UnicodeStringLiteral", .sol, "unicode\"\\u00e9\"", .tok .unicodeStr),
  ("HexString", .sol, "hex\"00_ff\"", .tok .hexStr),
  ("HexNumber", .sol, "0x1_f", .tok .num),
  ("OctalNumber", .sol, "017", .refused),
  ("DecimalNumber", .sol, "1_0.5e-3", .tok .num),
  ("DecimalNumberFollowedByIdentifier", .sol, "1a", .refused),
  ("Identifier", .sol, "$x_1", .tok .ident),
  ("WS", .sol, " \t", .trivia),
  ("COMMENT", .sol, "/* c */", .trivia),
  ("LINE_COMMENT", .sol, "// c", .trivia),
  ("AssemblyDialect", .asm, "\"evmasm\"", .tok .str),
  ("AssemblyLBrace", .asm, "{", .tok .punct),
  ("AssemblyFlagString", .asm, "\"memory-safe\"", .tok .str),
  ("AssemblyBlockLParen", .asm, "(", .tok .punct),
  ("AssemblyBlockRParen", .asm, ")", .tok .punct),
  ("AssemblyBlockComma", .asm, ",", .tok .punct),
  ("AssemblyBlockWS", .asm, " ", .trivia),
  ("AssemblyBlockCOMMENT", .asm, "/**/", .trivia),
  ("AssemblyBlockLINE_COMMENT", .asm, "//", .trivia),
  ("YulBreak", (.yul 0), "break", .tok .yulKw),
  ("YulCase", (.yul 0), "case", .tok .yulKw),
  ("YulContinue", (.yul 0), "continue", .tok .yulKw),
  ("YulDefault", (.yul 0), "default", .tok .yulKw),
  ("YulFalse", (.yul 0), "false", .tok .bool),
  ("YulFor", (.yul 0), "for", .tok .yulKw),
  ("YulFunction", (.yul 0), "function", .tok .yulKw),
  ("YulIf", (.yul 0), "if", .tok .yulKw),
  ("YulLeave", (.yul 0), "leave", .tok .yulKw),
  ("YulLet", (.yul 0), "let", .tok .yulKw),
  ("YulSwitch", (.yul 0), "switch", .tok .yulKw),
  ("YulTrue", (.yul 0), "true", .tok .bool),
  ("YulHex", (.yul 0), "hex", .refused),
  ("YulEVMBuiltin", (.yul 0), "mstore", .tok .ident),
  ("YulLBrace", (.yul 0), "{", .tok .punct),
  ("YulRBrace", (.yul 0), "}", .tok .punct),
  ("YulLParen", (.yul 0), "(", .tok .punct),
  ("YulRParen", (.yul 0), ")", .tok .punct),
  ("YulAssign", (.yul 0), ":=", .tok .punct),
  ("YulPeriod", (.yul 0), ".", .tok .punct),
  ("YulComma", (.yul 0), ",", .tok .punct),
  ("YulArrow", (.yul 0), "->", .tok .punct),
  ("YulIdentifier", (.yul 0), "x$1", .tok .ident),
  ("YulHexNumber", (.yul 0), "0xfF", .tok .yulHex),
  ("YulDecimalNumber", (.yul 0), "10", .tok .yulDec),
  ("YulStringLiteral", (.yul 0), "'ab'", .tok .str),
  ("YulHexStringLiteral", (.yul 0), "hex\"0a\"", .tok .hexStr),
  ("YulWS", (.yul 0), "\n", .trivia),
  ("YulCOMMENT", (.yul 0), "/* */", .trivia),
  ("YulLINE_COMMENT", (.yul 0), "// x", .trivia),
  ("PragmaToken", .pragma, "^0.8.0", .tok .pragmaWord),
  ("PragmaSemicolon", .pragma, ";", .tok .punct),
  ("PragmaWS", .pragma, " ", .trivia),
  ("PragmaCOMMENT", .pragma, "/* */", .trivia),
  ("PragmaLINE_COMMENT", .pragma, "//", .trivia)
]

/-- **Coverage, by rule**: each rule's sample is classified as the rule says. -/
theorem lexRules_classified :
    lexRules.all (fun r => r.2.2.2.accepts (classify r.2.1 (ascii r.2.2.1))) = true := by
  decide +kernel

/-- **Coverage, by class**: every token class comes from some rule. -/
theorem lexRules_cover :
    TokClass.all.all (fun c => lexRules.any (·.2.2.2 == .tok c)) = true := by decide +kernel

theorem TokClass.mem_all (c : TokClass) : c ∈ TokClass.all := by cases c <;> decide

/-! ## The tables agree with the spellings -/

theorem Kw.mem_all (k : Kw) : k ∈ Kw.all := by cases k <;> decide
theorem Punct.mem_all (p : Punct) : p ∈ Punct.all := by cases p <;> decide
theorem YulKw.mem_all (k : YulKw) : k ∈ YulKw.all := by cases k <;> decide

theorem Kw.bytes_spell : Kw.all.all (fun k => k.bytes == ascii k.spell) = true := by decide +kernel
theorem Punct.bytes_spell : Punct.all.all (fun p => p.bytes == ascii p.spell) = true := by
  decide +kernel
theorem YulKw.bytes_spell : YulKw.all.all (fun k => k.bytes == ascii k.spell) = true := by
  decide +kernel

/-- Every keyword lexes to itself in Solidity mode. -/
theorem classify_kw : Kw.all.all (fun k => classify .sol (ascii k.spell) == some (.tok (.kw k))) = true := by
  decide +kernel

/-- Every Solidity punctuation lexes to itself. -/
theorem classify_punct :
    solPuncts.all (fun p => classify .sol (ascii p.spell) == some (.tok (.punct p))) = true := by
  decide +kernel

/-- Every reserved keyword is refused in Solidity mode, and is an
identifier or keyword in Yul. -/
theorem classify_reserved :
    reservedKeywords.all (fun r => classify .sol (ascii r) == none &&
      (classify (.yul 0) (ascii r)).isSome) = true := by
  decide +kernel

/-! ## Accepted inputs -/

/-- The token classes of an accepted source. -/
def lexToks (s : String) : Option (List Tok) :=
  (tokens (ascii s)).toOption.map (·.map Located.tok)

theorem lex_contract :
    lexToks "contract C { uint x = 0x1F; }" = some [.kw .contract, .ident "C", .punct .lbrace,
      .elem (.int false 256 (by decide)), .ident "x", .punct .assign,
      .num (.hex [1, 15] false), .punct .semi, .punct .rbrace] := by decide +kernel

/-- Units, exponents, fractions, `_` separators. -/
theorem lex_numbers :
    lexToks "1_000 2.5e-3 .5 7 ether" = some [.num (.dec 1000 0 0), .num (.dec 25 1 (-3)),
      .num (.dec 5 1 0), .num (.dec 7 0 0), .denom .ether] := by decide +kernel

/-- Escapes: `\x41`, `\n`, a `\u` escape as UTF-8, an escaped line break. -/
theorem lex_escapes :
    lexToks "\"\\x41\\n\\u00e9\\\n!\" 'q\"'" =
      some [.str [65, 10, 195, 169, 33], .str [113, 34]] := by decide +kernel

theorem lex_hex_unicode :
    lexToks "hex\"00_ff\" hex'' unicode\"\\t\"" =
      some [.hexStr [0, 255], .hexStr [], .unicodeStr [9]] := by decide +kernel

/-- Comments, NatSpec included, are trivia. -/
theorem lex_comments :
    ((lex (ascii "/// doc\n/** d */ /* c */ x // e")).toOption.map (·.map Piece.kind)) =
      some [.trivia (.line true), .trivia .ws, .trivia (.block true), .trivia .ws,
        .trivia (.block false), .trivia .ws, .tok (.ident "x"), .trivia .ws,
        .trivia (.line false)] := by decide +kernel

/-- Type keywords inside solc's bounds; others are identifiers. -/
theorem lex_types :
    lexToks "int8 uint bytes1 fixed8x80 ufixed int7 bytes33 fixed8x81 uint08" = some [
      .elem (.int true 8 (by decide)), .elem (.int false 256 (by decide)),
      .elem (.fixedBytes 1 (by decide)), .elem (.fixed true (some ⟨8, 80, by decide⟩)),
      .elem (.fixed false none), .ident "int7", .ident "bytes33", .ident "fixed8x81",
      .ident "uint08"] := by decide +kernel

/-- A pragma's words; Yul keywords and numbers inside assembly only. -/
theorem lex_modes :
    lexToks "pragma solidity >=0.8.0 <0.9.0; assembly \"evmasm\" { let x := 0x20 } let" = none ∧
    lexToks "pragma abicoder v2; assembly { let x := 0x20 }" = some [.kw .pragma,
      .pragmaWord "abicoder", .pragmaWord "v2", .punct .semi, .kw .assembly, .punct .lbrace,
      .yulKw .let_, .ident "x", .punct .yulAssign, .yulHex 32, .punct .rbrace] := by
  decide +kernel

/-- An EIP-55 checksummed address literal carries the flag; one letter's
case changed, it does not. -/
theorem lex_checksum :
    (lexToks "0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed").map (·.map fun
      | .num (.hex _ c) => c | _ => false) = some [true] ∧
    (lexToks "0x5aaeb6053F3E94C9b9A09f33669435E7Ef1BeAed").map (·.map fun
      | .num (.hex _ c) => c | _ => false) = some [false] := by decide +kernel

/-- **Ranges re-locate** (`lex_locate` instantiated): the bytes at each
token's range. -/
theorem lex_ranges :
    (tokens (ascii "a /*x*/ += 0x1")).toOption.map (·.map fun l => (l.start, l.stop)) =
      some [(0, 1), (8, 10), (11, 14)] := by decide +kernel

/-! ## Negative controls: refused, located -/

def lexErr (s : String) : Option (Nat × String) :=
  match lex (ascii s) with
  | .error e => some (e.pos, e.msg)
  | .ok _ => none

theorem refuse_reserved : lexErr "uint after;" = some (5, "reserved keyword") := by decide +kernel
theorem refuse_octal : lexErr "x = 017;" = some (4, "malformed number") := by decide +kernel
theorem refuse_glued : lexErr "x = 1wei;" = some (4, "number followed by an identifier character") := by
  decide +kernel
theorem refuse_underscore : lexErr "1__0 1_" = some (0, "malformed number") := by decide +kernel
theorem refuse_hex_empty : lexErr "0x" = some (0, "malformed number") := by decide +kernel
theorem refuse_unterminated_string : lexErr "s = \"ab" = some (4, "unterminated string literal") := by
  decide +kernel
theorem refuse_newline_in_string : lexErr "\"a\nb\"" = some (0, "unterminated string literal") := by
  decide +kernel
theorem refuse_bad_escape : lexErr "\"\\q\"" = some (0, "malformed string literal") := by decide +kernel
theorem refuse_nonprintable : lexErr "\"\t\"" = some (0, "malformed string literal") := by decide +kernel
theorem refuse_odd_hex : lexErr "hex\"abc\"" = some (0, "malformed hex or unicode string literal") := by
  decide +kernel
theorem refuse_comment : lexErr "x /* y" = some (2, "unterminated comment") := by decide +kernel
theorem refuse_char : lexErr "x # y" = some (2, "invalid character") := by decide +kernel
theorem refuse_pragma : lexErr "x; pragma solidity" = some (3, "unterminated pragma") := by decide +kernel
theorem refuse_assembly : lexErr "x assembly { let" = some (2, "unterminated assembly block") := by
  decide +kernel
/-- Not a refusal: `:=` is Yul's only, two tokens outside. -/
theorem yul_assign_outside : lexErr "a := b" = none ∧
    lexToks "a := b" = some [.ident "a", .punct .colon, .punct .assign, .ident "b"] := by decide +kernel

/-- A wrong output fails: the scanner's pieces without the last two (`x`,
`;`) are not a certificate of the source. -/
theorem lexed_wrong :
    (match lex (ascii "uint x;") with
      | .ok ps => decide (Lexed (ascii "uint x;") (ps.take 2)) | .error _ => true) = false := by
  decide +kernel

/-- solc's scanner refuses form feed and vertical tab outside strings, irregular
line breaks in single-line comments and unicode literals, and unbalanced
Unicode direction overrides (`\u202E` without `\u202C`) in comments and
unicode literals; it accepts an escaped CR LF; `hex` alone is no Yul token;
an assembly dialect or flag is a non-empty double-quoted string. -/
theorem solc_scanner_rules :
    (lexErr "a\x0cb").isSome ∧
    (lex [97, 12, 98]).toOption.isNone ∧
    (lex (ascii "// a" ++ [11] ++ ascii " b")).toOption.isNone ∧
    (lex (ascii "// x " ++ [0xE2, 0x80, 0xAE])).toOption.isNone ∧
    (lex (ascii "// x " ++ [0xE2, 0x80, 0xAE, 0xE2, 0x80, 0xAC])).toOption.isSome ∧
    (lex (ascii "unicode\"" ++ [0xE2, 0x80, 0xAC] ++ ascii "\"")).toOption.isNone ∧
    lexToks "\"a\\\r\nb\"" = some [.str (ascii "ab")] ∧
    (lex (ascii "assembly { let hex := 1 }")).toOption.isNone ∧
    (lex (ascii "assembly \"\" { }")).toOption.isNone ∧
    (lex (ascii "assembly 'evmasm' { }")).toOption.isNone ∧
    (lex (ascii "assembly \"evmasm\" (\"memory-safe\") { }")).toOption.isSome := by
  decide +kernel

/-- The other fixed words of the tables classify as their tokens. -/
theorem classify_words :
    ([("address", Tok.elem .address), ("bool", .elem .bool), ("string", .elem .string),
      ("bytes", .elem .bytes), ("wei", .denom .wei), ("gwei", .denom .gwei),
      ("ether", .denom .ether), ("seconds", .denom .seconds), ("minutes", .denom .minutes),
      ("hours", .denom .hours), ("days", .denom .days), ("weeks", .denom .weeks),
      ("years", .denom .years), ("true", .bool true), ("false", .bool false)].all
      fun (w, t) => classify .sol (ascii w) == some (.tok t)) = true ∧
    yulPuncts.all (fun p => classify (.yul 0) (ascii p.spell) == some (.tok (.punct p))) ∧
    YulKw.all.all (fun k => classify (.yul 0) (ascii k.spell) == some (.tok (.yulKw k))) := by
  decide +kernel

/-- **Maximal munch decides the cut**: re-printing, classified splits that
are not maximal fail the certificate (`1|.5`, `hex|"00"`, `ui|nt`). -/
theorem lexed_not_maximal :
    decide (Lexed (ascii "1.5") [⟨.tok (.num (.dec 1 0 0)), ascii "1"⟩,
      ⟨.tok (.num (.dec 5 1 0)), ascii ".5"⟩]) = false ∧
    decide (Lexed (ascii "hex\"00\"") [⟨.tok (.kw .hex), ascii "hex"⟩,
      ⟨.tok (.str (ascii "00")), ascii "\"00\""⟩]) = false ∧
    decide (Lexed (ascii "uint") [⟨.tok (.ident "ui"), ascii "ui"⟩, ⟨.tok (.ident "nt"), ascii "nt"⟩]) =
      false ∧
    decide (Lexed (ascii "uint") [⟨.tok (.elem (.int false 256 (by decide))), ascii "uint"⟩]) = true := by
  decide +kernel

/-- NatSpec is `///` and `/** … */`, not `////` or `/***/`. -/
theorem natspec_flags :
    (["///a", "////a", "/** a */", "/***/", "/**/"].map fun c => trivia (ascii c)) =
      [some (.line true), some (.line false), some (.block true), some (.block false),
        some (.block false)] := by decide +kernel

end Solidity.Frontend.Checked

/-- info: 'Solidity.Frontend.Checked.lex_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.lex_sound
/-- info: 'Solidity.Frontend.Checked.lex_locate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.lex_locate
/-- info: 'Solidity.Frontend.Checked.lex_error_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.lex_error_pos
/-- info: 'Solidity.Frontend.Checked.lexRules_classified' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.lexRules_classified
