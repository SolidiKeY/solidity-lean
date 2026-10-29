import Solidity.Frontend.Checked.Tables
import Solidity.Keccak

/-!
# The checked lexer (G08)

`lex : Bytes → Except Error (List Piece)` cuts a source unit into pieces
(tokens and trivia), each with its exact bytes.  It is two functions and a
check:

* `split` decides where the next lexeme ends (maximal munch, per lexer mode);
* `classify` decides what a whole lexeme is.  It is the specification of the
  lexical classes of `SolidityLexer.g4`, one clause per rule, read on a
  complete lexeme: identifiers (`IdentifierStart IdentifierPart*`, minus the
  keywords), `DecimalNumber`, `HexNumber`, the string, hex-string and unicode
  string literals with their escapes, punctuation, comments and whitespace,
  pragma words, and the `AssemblyBlockMode`/`YulMode` lexemes;
* the result is re-checked (`Lexed`): its pieces concatenate to the input,
  each is classified in the mode its predecessors leave
  (`Mode.next`, the lexer's `pushMode`/`popMode`), no token extends by a
  prefix of the next one into a longer lexeme of its mode (`munchFrom`,
  maximal munch), and no number is glued to
  a following identifier character (`DecimalNumberFollowedByIdentifier`).

So `lex_sound` holds by the check, and `lex_locate` derives from it that each
token's byte range re-locates it: the bytes at `[start, stop)` of the input
classify as that token.

**Refused input** is a located `Error`: an invalid byte, an unterminated
comment, string or pragma, a reserved keyword, a malformed number (octal,
misplaced `_`, `0x` without digits), a number followed by an identifier
character, a bad escape, a non-printable byte in a plain string.

**Deviations, recorded.**  Comments inside a pragma are trivia (the ANTLR
`PragmaToken` would absorb them; solc's scanner skips them), and a pragma
word is a maximal run of bytes without whitespace, `;` or a comment start, so
maximal munch is not claimed in pragma mode.  `intM`, `bytesN` and `fixedMxN`
spellings with leading zeros, or outside solc's bounds, are identifiers, as
solc's scanner reads them (`Elem`, `FixDims`).  A hexadecimal literal's
EIP-55 flag is computed for 40-digit literals only (the only ones it types,
S01); it is `false` for every other length.  Bytes of `unicode"…"` literals
and comments are not checked to be valid UTF-8.  Where the ANTLR lexer and
solc's scanner differ (form feed, irregular line breaks, Unicode direction
overrides, an escaped CR LF, `hex` alone in Yul), solc decides; the list is
in `docs/feature-work/frontend-parse.md`.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-! ## Byte classes -/

def isWs (b : UInt8) : Bool :=
  let n := b.toNat; n == 32 || n == 9 || n == 10 || n == 13
def isDigit (b : UInt8) : Bool := let n := b.toNat; 48 ≤ n && n ≤ 57
def isAlpha (b : UInt8) : Bool :=
  let n := b.toNat; (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)
def isIdStart (b : UInt8) : Bool := isAlpha b || b.toNat == 36 || b.toNat == 95
def isIdPart (b : UInt8) : Bool := isIdStart b || isDigit b
def isHexDigit (b : UInt8) : Bool :=
  let n := b.toNat; isDigit b || (65 ≤ n && n ≤ 70) || (97 ≤ n && n ≤ 102)
def hexVal (b : UInt8) : Nat :=
  let n := b.toNat
  if n ≤ 57 then n - 48 else if n ≤ 70 then n - 55 else n - 87
def isNewline (b : UInt8) : Bool := b.toNat == 10 || b.toNat == 13

/-- The value of a list of decimal digit bytes. -/
def digitsVal (ds : Bytes) : Nat := ds.foldl (fun a d => 10 * a + (d.toNat - 48)) 0

/-! ## Lexer modes -/

/-- The lexer's modes: Solidity, a pragma's words, the head of an assembly
block, and Yul at a brace depth. -/
inductive Mode where
  | sol
  | pragma
  | asm
  | yul (depth : Nat)
  deriving DecidableEq, Repr

/-- The mode after a piece: `pragma` and `assembly` push a mode, `;` ends a
pragma, braces nest inside Yul and the outermost `}` returns to Solidity. -/
def Mode.next : Mode → Kind → Mode
  | .sol, .tok (.kw .pragma) => .pragma
  | .sol, .tok (.kw .assembly) => .asm
  | .pragma, .tok (.punct .semi) => .sol
  | .asm, .tok (.punct .lbrace) => .yul 0
  | .yul d, .tok (.punct .lbrace) => .yul (d + 1)
  | .yul 0, .tok (.punct .rbrace) => .sol
  | .yul (d + 1), .tok (.punct .rbrace) => .yul d
  | m, _ => m

/-! ## Classification of a whole lexeme -/

/-- Decimal digits with single underscores between them, maximal: the
digits read and the rest (`DecimalDigits` without its first digit). -/
def digitsTail : Bytes → Bytes × Bytes
  | [] => ([], [])
  | b :: r =>
    if isDigit b then
      let p := digitsTail r; (b :: p.1, p.2)
    else if b.toNat == 95 then
      match r with
      | c :: r' =>
        if isDigit c then let p := digitsTail r'; (c :: p.1, p.2) else ([], b :: r)
      | [] => ([], [b])
    else ([], b :: r)

/-- `DecimalDigits`: at least one digit. -/
def digits1 : Bytes → Option (Bytes × Bytes)
  | b :: r => if isDigit b then let p := digitsTail r; some (b :: p.1, p.2) else none
  | [] => none

/-- `DecimalNumber`, refusing `OctalNumber` (a leading `0` followed by a
digit), as the exact `NumLit.dec`. -/
def decNumber (raw : Bytes) : Option NumLit :=
  let (ip, r1) := match digits1 raw with
    | some p => p
    | none => ([], raw)
  let frac : Option (Bytes × Bytes) := match r1 with
    | 46 :: r => digits1 r
    | r => some ([], r)
  match frac with
  | none => none
  | some (fp, r2) =>
    if ip.isEmpty && fp.isEmpty then none
    else if ip.length > 1 && ip.head? == some 48 then none
    else
      let expo : Option Int := match r2 with
        | [] => some 0
        | e :: r =>
          if e.toNat == 101 || e.toNat == 69 then
            match r with
            | 45 :: r' => match digits1 r' with
              | some (ds, []) => some (-(digitsVal ds : Int))
              | _ => none
            | r' => match digits1 r' with
              | some (ds, []) => some (digitsVal ds : Int)
              | _ => none
          else none
      expo.map fun x => .dec (digitsVal (ip ++ fp)) fp.length x

/-- Hexadecimal digits with single underscores between them, all of the
input (`HexDigits`). -/
def hexDigits : Bytes → Option Bytes
  | [b] => if isHexDigit b then some [b] else none
  | b :: 95 :: r => if isHexDigit b && !r.isEmpty then (hexDigits r).map (b :: ·) else none
  | b :: r => if isHexDigit b then (hexDigits r).map (b :: ·) else none
  | [] => none

def toFin16 (b : UInt8) : Fin 16 := ⟨hexVal b % 16, Nat.mod_lt _ (by decide)⟩

/-- The lowercase ASCII byte of a hex digit. -/
def lowerHex (b : UInt8) : Nat := let n := b.toNat; if 65 ≤ n && n ≤ 70 then n + 32 else n

/-- EIP-55: the case of each letter digit is upper exactly when the
corresponding nibble of the Keccak-256 of the lowercase spelling is at least 8. -/
def eip55 (ds : Bytes) : Bool :=
  ds.length == 40 &&
    let h := Solidity.Keccak.keccak256 (ds.map lowerHex)
    let nib (i : Nat) : Nat :=
      let byte := h.getD (i / 2) 0
      if i % 2 == 0 then byte / 16 else byte % 16
    (List.range 40).all fun i =>
      let d := (ds.getD i 0).toNat
      if 97 ≤ d && d ≤ 102 then nib i < 8
      else if 65 ≤ d && d ≤ 70 then 8 ≤ nib i
      else true

/-- `HexNumber`: `0x` and hex digits. -/
def hexNumber : Bytes → Option NumLit
  | 48 :: 120 :: r => (hexDigits r).map fun ds => .hex (ds.map toFin16) (eip55 ds)
  | _ => none

/-- The UTF-8 bytes of a code point below `0x10000` (a `\uXXXX` escape). -/
def utf8 (cp : Nat) : Bytes :=
  if cp < 0x80 then [cp.toUInt8]
  else if cp < 0x800 then [(0xC0 + cp / 64).toUInt8, (0x80 + cp % 64).toUInt8]
  else [(0xE0 + cp / 4096).toUInt8, (0x80 + cp / 64 % 64).toUInt8, (0x80 + cp % 64).toUInt8]

/-- A string literal's body (`DoubleQuotedStringCharacter*` and the others),
decoded: the bytes `allowed` admits stand for themselves, and the
`EscapeSequence`s `\' \" \\ \n \r \t`, an escaped line break (nothing),
`\xNN` and `\uNNNN` (UTF-8). -/
def strBody (allowed : UInt8 → Bool) : Bytes → Option Bytes
  | [] => some []
  | 92 :: 120 :: h1 :: h2 :: r =>
    if isHexDigit h1 && isHexDigit h2 then
      (strBody allowed r).map ((hexVal h1 * 16 + hexVal h2).toUInt8 :: ·)
    else none
  | 92 :: 117 :: h1 :: h2 :: h3 :: h4 :: r =>
    if isHexDigit h1 && isHexDigit h2 && isHexDigit h3 && isHexDigit h4 then
      (strBody allowed r).map
        (utf8 (((hexVal h1 * 16 + hexVal h2) * 16 + hexVal h3) * 16 + hexVal h4) ++ ·)
    else none
  | 92 :: 13 :: 10 :: r => strBody allowed r
  | 92 :: c :: r =>
    let n := c.toNat
    let out : Option Bytes :=
      if n == 39 || n == 34 || n == 92 then some [c]
      else if n == 110 then some [10]
      else if n == 114 then some [13]
      else if n == 116 then some [9]
      else if n == 10 || n == 13 then some []
      else none
    match out with
    | some o => (strBody allowed r).map (o ++ ·)
    | none => none
  | b :: r => if allowed b && b.toNat != 92 then (strBody allowed r).map (b :: ·) else none

/-- The single-character escapes (`\' \" \\ \n \r \t`, an escaped line break). -/
def escapeChar (c : UInt8) : Option Bytes :=
  let n := c.toNat
  if n == 39 || n == 34 || n == 92 then some [c]
  else if n == 110 then some [10]
  else if n == 114 then some [13]
  else if n == 116 then some [9]
  else if n == 10 || n == 13 then some []
  else none

/-- **The string-body grammar** (`…StringCharacter*` with `EscapeSequence`),
transcribed from `SolidityLexer.g4` as a relation between a body and its
decoded bytes; `strBody_sound` proves the decoder against it. -/
inductive StrBody (allowed : UInt8 → Bool) : Bytes → Bytes → Prop where
  | nil : StrBody allowed [] []
  | char {b : UInt8} {r out : Bytes} : allowed b = true → b.toNat ≠ 92 →
      StrBody allowed r out → StrBody allowed (b :: r) (b :: out)
  | crlf {r out : Bytes} : StrBody allowed r out → StrBody allowed (92 :: 13 :: 10 :: r) out
  | esc {c : UInt8} {r out o : Bytes} : escapeChar c = some o →
      StrBody allowed r out → StrBody allowed (92 :: c :: r) (o ++ out)
  | hex {h1 h2 : UInt8} {r out : Bytes} : isHexDigit h1 = true → isHexDigit h2 = true →
      StrBody allowed r out →
      StrBody allowed (92 :: 120 :: h1 :: h2 :: r) ((hexVal h1 * 16 + hexVal h2).toUInt8 :: out)
  | uni {h1 h2 h3 h4 : UInt8} {r out : Bytes} : isHexDigit h1 = true → isHexDigit h2 = true →
      isHexDigit h3 = true → isHexDigit h4 = true → StrBody allowed r out →
      StrBody allowed (92 :: 117 :: h1 :: h2 :: h3 :: h4 :: r)
        (utf8 (((hexVal h1 * 16 + hexVal h2) * 16 + hexVal h3) * 16 + hexVal h4) ++ out)

/-- **The decoder is sound for the string-body grammar.** -/
theorem strBody_sound (allowed : UInt8 → Bool) (raw : Bytes) :
    ∀ out, strBody allowed raw = some out → StrBody allowed raw out := by
  fun_induction strBody allowed raw <;> intro out h
  case case1 => cases h; exact .nil
  case case2 hh ih =>
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true] at hh
    exact .hex hh.1 hh.2 (ih x hx)
  case case4 hh ih =>
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true] at hh
    exact .uni hh.1.1.1 hh.1.1.2 hh.1.2 hh.2 (ih x hx)
  case case6 ih => exact .crlf (ih out h)
  case case7 c r _ _ _ o ho ih =>
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .esc (by simpa only [escapeChar] using ho) (ih x hx)
  case case9 hh ih =>
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
    exact .char hh.1 hh.2 (ih x hx)
  all_goals cases h

/-- Printable ASCII except the quote (`DoubleQuotedPrintable`,
`SingleQuotedPrintable`). -/
def printable (q : UInt8) (b : UInt8) : Bool :=
  let n := b.toNat; 32 ≤ n && n ≤ 126 && b != q
/-- Any byte except the quote and a line break (`…UnicodeStringCharacter`). -/
def unicodeChar (q : UInt8) (b : UInt8) : Bool := b != q && !isNewline b

/-- A quoted literal `q body q` with `q` a double or single quote: its body. -/
def quotedBody : Bytes → Option (UInt8 × Bytes)
  | q :: r =>
    if (q.toNat == 34 || q.toNat == 39) && r.getLast? == some q then some (q, r.dropLast)
    else none
  | [] => none

/-- `EvenHexDigits?`: pairs of hex digits with single underscores between
pairs, decoded. -/
def hexBody : Bytes → Option Bytes
  | [] => some []
  | a :: b :: 95 :: t =>
    if isHexDigit a && isHexDigit b && !t.isEmpty then
      (hexBody t).map ((hexVal a * 16 + hexVal b).toUInt8 :: ·)
    else none
  | a :: b :: t =>
    if isHexDigit a && isHexDigit b then (hexBody t).map ((hexVal a * 16 + hexVal b).toUInt8 :: ·)
    else none
  | [_] => none

/-- A canonical decimal spelling (no leading zero) and its value. -/
def canonNat (ds : Bytes) : Option Nat :=
  if !ds.isEmpty && ds.all isDigit && (ds.length == 1 || ds.head? != some 48) then
    some (digitsVal ds)
  else none

/-- The `intM`/`uintM` width after the prefix, inside the bounds. -/
def intElem (signed : Bool) (rest : Bytes) : Option Elem :=
  if rest.isEmpty then some (.int signed 256 (by decide))
  else match canonNat rest with
    | some n => if h : n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 then some (.int signed n h) else none
    | none => none

def bytesElem (rest : Bytes) : Option Elem :=
  if rest.isEmpty then some .bytes
  else match canonNat rest with
    | some n => if h : 1 ≤ n ∧ n ≤ 32 then some (.fixedBytes n h) else none
    | none => none

def fixedElem (signed : Bool) (rest : Bytes) : Option Elem :=
  if rest.isEmpty then some (.fixed signed none)
  else
    let m := rest.takeWhile (·.toNat != 120)
    match rest.drop m.length with
    | 120 :: n =>
      match canonNat m, canonNat n with
      | some a, some b =>
        if h : a % 8 = 0 ∧ 8 ≤ a ∧ a ≤ 256 ∧ b ≤ 80 then some (.fixed signed (some ⟨a, b, h⟩))
        else none
      | _, _ => none
    | _ => none

/-- A numbered elementary type keyword (`SignedIntegerType`,
`UnsignedIntegerType`, `FixedBytes`, `Fixed`, `Ufixed`, and `bytes`). -/
def elemWord (w : Bytes) : Option Elem :=
  match w with
  | 117 :: 105 :: 110 :: 116 :: r => intElem false r
  | 105 :: 110 :: 116 :: r => intElem true r
  | 98 :: 121 :: 116 :: 101 :: 115 :: r => bytesElem r
  | 117 :: 102 :: 105 :: 120 :: 101 :: 100 :: r => fixedElem false r
  | 102 :: 105 :: 120 :: 101 :: 100 :: r => fixedElem true r
  | _ => none

/-- A word of Solidity mode: a keyword, a type, a unit, a boolean or an
identifier; `none` for a reserved keyword. -/
def solWord (w : Bytes) : Option Tok :=
  match solWordTable w with
  | .tok t => some t
  | .reserved => none
  | .other =>
    match elemWord w with
    | some e => some (.elem e)
    | none => some (.ident w.str)

/-- A word of Yul mode: a Yul keyword, a boolean or an identifier. -/
def yulWord (w : Bytes) : Tok :=
  match yulWordTable w with
  | some t => t
  | none => .ident w.str

/-- `IdentifierStart IdentifierPart*`. -/
def isWord : Bytes → Bool
  | b :: r => isIdStart b && r.all isIdPart
  | [] => false

/-- An irregular line break solc refuses inside a single-line comment or a
string: form feed, vertical tab, U+2028, U+2029. -/
def irregularBreak (b : Bytes) : Bool :=
  b.any (fun c => c.toNat == 11 || c.toNat == 12) ||
    (List.range b.length).any fun i =>
      let t := (b.drop i).take 3; t == [0xE2, 0x80, 0xA8] || t == [0xE2, 0x80, 0xA9]

/-- Unicode directional formatting is balanced (solc's scanner): LRE, RLE,
LRO, RLO and LRI, RLI, FSI open; PDF and PDI close; no close without an open,
nothing left open. -/
def bidiBalanced (b : Bytes) : Bool :=
  let rec walk : Bytes → Nat → Bool
    | 0xE2 :: 0x80 :: c :: r, d =>
      let n := c.toNat
      if n == 0xAA || n == 0xAB || n == 0xAD || n == 0xAE then walk r (d + 1)
      else if n == 0xAC then (d != 0 && walk r (d - 1))
      else walk (0x80 :: c :: r) d
    | 0xE2 :: 0x81 :: c :: r, d =>
      let n := c.toNat
      if n == 0xA6 || n == 0xA7 || n == 0xA8 then walk r (d + 1)
      else if n == 0xA9 then (d != 0 && walk r (d - 1))
      else walk (0x81 :: c :: r) d
    | _ :: r, d => walk r d
    | [], d => d == 0
  walk b 0

/-- Whitespace and comments: `WS`, `LINE_COMMENT`, `COMMENT` (`.*?`, so the
body has no `*/`). -/
def trivia (raw : Bytes) : Option Trivia :=
  match raw with
  | 47 :: 47 :: r =>
    if r.any isNewline || irregularBreak r || !bidiBalanced r then none
    else some (.line (r.head? == some 47 && (r.drop 1).head? != some 47))
  | 47 :: 42 :: r =>
    if r.length ≥ 2 && r.drop (r.length - 2) == [42, 47] then
      let body := r.take (r.length - 2)
      if (List.range body.length).any (fun i => (body.drop i).take 2 == [42, 47]) ||
        !bidiBalanced body then none
      else some (.block (body.head? == some 42 && body.length ≥ 2))
    else none
  | [] => none
  | _ => if raw.all isWs then some .ws else none

/-- A punctuation token among `ps` spelled exactly `raw`. -/
def punctOf (ps : List Punct) (raw : Bytes) : Option Punct :=
  (punctExact raw).filter (ps.contains ·)

/-- Solidity mode's punctuation: all but Yul's `:=`. -/
def solPuncts : List Punct := Punct.all.filter (· != .yulAssign)
/-- Assembly-head punctuation (`AssemblyBlockLParen`, …, `AssemblyLBrace`). -/
def asmPuncts : List Punct := [.lparen, .rparen, .comma, .lbrace]
/-- Yul punctuation. -/
def yulPuncts : List Punct :=
  [.yulAssign, .rightArrow, .lbrace, .rbrace, .lparen, .rparen, .period, .comma]

/-- `"…"` or `'…'` with printable characters and escapes. -/
def plainString (raw : Bytes) : Option Bytes :=
  match quotedBody raw with
  | some (q, body) => strBody (printable q) body
  | none => none

/-- A token of Solidity mode. -/
def solTok (raw : Bytes) : Option Tok :=
  if isWord raw then solWord raw
  else match punctOf solPuncts raw with
  | some p => some (.punct p)
  | none =>
    match plainString raw with
    | some b => some (.str b)
    | none =>
      match raw with
      | 104 :: 101 :: 120 :: r =>
        match quotedBody r with
        | some (_, body) => (hexBody body).map .hexStr
        | none => none
      | 117 :: 110 :: 105 :: 99 :: 111 :: 100 :: 101 :: r =>
        match quotedBody r with
        | some (q, body) =>
          if irregularBreak body || !bidiBalanced body then none
          else (strBody (unicodeChar q) body).map .unicodeStr
        | none => none
      | _ =>
        match hexNumber raw with
        | some n => some (.num n)
        | none => (decNumber raw).map .num

/-- A pragma word: no whitespace, no `;`, no comment start. -/
def pragmaWordOk (raw : Bytes) : Bool :=
  !raw.isEmpty && raw.all (fun b => !isWs b && b.toNat != 59 && 32 < b.toNat && b.toNat < 127) &&
    !(List.range raw.length).any (fun i =>
      let t := (raw.drop i).take 2; t == [47, 47] || t == [47, 42])

/-- `YulDecimalNumber` (`0` or no leading zero), `YulHexNumber`. -/
def yulNumber : Bytes → Option Tok
  | 48 :: 120 :: r =>
    if !r.isEmpty && r.all isHexDigit then
      some (.yulHex (r.foldl (fun a d => 16 * a + hexVal d) 0))
    else none
  | raw => (canonNat raw).map .yulDec

/-- A token of Yul mode. -/
def yulTok (raw : Bytes) : Option Tok :=
  if raw == ascii "hex" then none
  else if isWord raw then some (yulWord raw)
  else match punctOf yulPuncts raw with
  | some p => some (.punct p)
  | none =>
    match plainString raw with
    | some b => some (.str b)
    | none =>
      match raw with
      | 104 :: 101 :: 120 :: r =>
        match quotedBody r with
        | some (_, body) => (hexBody body).map .hexStr
        | none => none
      | _ => yulNumber raw

/-- **The lexical classes**: what a whole lexeme is in a mode. -/
def classify (m : Mode) (raw : Bytes) : Option Kind :=
  match trivia raw with
  | some t => some (.trivia t)
  | none =>
    (match m with
      | .sol => solTok raw
      | .pragma =>
        if raw == [59] then some (.punct .semi)
        else if pragmaWordOk raw then some (.pragmaWord raw.str) else none
      | .asm =>
        match punctOf asmPuncts raw with
        | some p => some (.punct p)
        | none =>
          -- `AssemblyDialect`/`AssemblyFlagString`: double-quoted, non-empty.
          if raw.head? == some 34 && raw.length > 2 then (plainString raw).map .str else none
      | .yul _ => yulTok raw).map .tok

/-! ## Splitting off the next lexeme -/

/-- The bytes up to and including the first `*/` (after `/*`). -/
def untilCommentEnd : Bytes → Option (Bytes × Bytes)
  | 42 :: 47 :: r => some ([42, 47], r)
  | b :: r => (untilCommentEnd r).map fun p => (b :: p.1, p.2)
  | [] => none

/-- A quoted literal's bytes after the opening quote, through the closing
one; `none` at a line break or the end. -/
def untilQuote (q : UInt8) : Bytes → Option (Bytes × Bytes)
  | [] => none
  | 92 :: 13 :: 10 :: r => (untilQuote q r).map fun p => (92 :: 13 :: 10 :: p.1, p.2)
  | 92 :: c :: r => (untilQuote q r).map fun p => (92 :: c :: p.1, p.2)
  | b :: r =>
    if b == q then some ([b], r)
    else if isNewline b then none
    else (untilQuote q r).map fun p => (b :: p.1, p.2)

/-- A number's bytes: hex digits after `0x` (with `_`) for a hex number;
otherwise digits and `_`, a `.` followed by a digit, and an exponent
`e`/`E` (`-`) followed by a digit. -/
def numberSpan (yul : Bool) (l : Bytes) : Bytes × Bytes :=
  match l with
  | 48 :: 120 :: r =>
    let ds := r.takeWhile (fun b => isHexDigit b || (!yul && b.toNat == 95))
    (48 :: 120 :: ds, r.drop ds.length)
  | _ =>
    let ip := l.takeWhile (fun b => isDigit b || (!yul && b.toNat == 95))
    let r1 := l.drop ip.length
    if yul then (ip, r1) else
    let fp : Bytes := match r1 with
      | 46 :: d :: _ => if isDigit d then 46 :: (r1.drop 1).takeWhile (fun b => isDigit b || b.toNat == 95) else []
      | _ => []
    let r2 := r1.drop fp.length
    let ep : Bytes := match r2 with
      | e :: 45 :: d :: _ =>
        if (e.toNat == 101 || e.toNat == 69) && isDigit d then
          e :: 45 :: (r2.drop 2).takeWhile (fun b => isDigit b || b.toNat == 95)
        else []
      | e :: d :: _ =>
        if (e.toNat == 101 || e.toNat == 69) && isDigit d then
          e :: (r2.drop 1).takeWhile (fun b => isDigit b || b.toNat == 95)
        else []
      | _ => []
    (ip ++ fp ++ ep, r2.drop ep.length)

/-- The longest punctuation spelling among `ps` at the head of `l` (at
most four bytes). -/
def punctSpan (ps : List Punct) (l : Bytes) : Option (Bytes × Bytes) :=
  ([4, 3, 2, 1].find? fun n => (punctOf ps (l.take n)).isSome).map fun n => (l.take n, l.drop n)

/-- Split off the next lexeme: `(raw, rest)`, or the error message. -/
def split (m : Mode) (l : Bytes) : Except String (Bytes × Bytes) :=
  match l with
  | [] => .error "end of input"
  | 47 :: 47 :: r =>
    let c := r.takeWhile (!isNewline ·); .ok (47 :: 47 :: c, r.drop c.length)
  | 47 :: 42 :: r =>
    match untilCommentEnd r with
    | some (c, rest) => .ok (47 :: 42 :: c, rest)
    | none => .error "unterminated comment"
  | b :: r =>
    if isWs b then
      let w := r.takeWhile isWs; .ok (b :: w, r.drop w.length)
    else match m with
    | .pragma =>
      if b.toNat == 59 then .ok ([b], r)
      else
        let stop (x : Bytes) : Bool := match x with
          | 47 :: 47 :: _ => true | 47 :: 42 :: _ => true
          | c :: _ => isWs c || c.toNat == 59 | [] => true
        let n := (List.range l.length).find? (fun i => stop (l.drop i)) |>.getD l.length
        .ok (l.take n, l.drop n)
    | _ =>
      let quoted (pre : Bytes) (q : UInt8) (t : Bytes) : Except String (Bytes × Bytes) :=
        match untilQuote q t with
        | some (s, rest) => .ok (pre ++ q :: s, rest)
        | none => .error "unterminated string literal"
      let isQ (x : UInt8) : Bool := x.toNat == 34 || x.toNat == 39
      if isQ b then quoted [] b r
      else if isIdStart b && m != .asm then
        let w := l.takeWhile isIdPart
        let rest := l.drop w.length
        match rest with
        | q :: t =>
          if isQ q && (w == ascii "hex" || (w == ascii "unicode" && m == .sol)) then quoted w q t
          else .ok (w, rest)
        | [] => .ok (w, rest)
      else if (isDigit b || (b.toNat == 46 && m == .sol && (r.head?.map isDigit |>.getD false)))
          && m != .asm then
        let (n, rest) := numberSpan (m != .sol) l
        match rest with
        | c :: _ => if isIdPart c then .error "number followed by an identifier character"
                    else .ok (n, rest)
        | [] => .ok (n, rest)
      else
        let ps := match m with
          | .sol => solPuncts | .asm => asmPuncts | _ => yulPuncts
        match punctSpan ps l with
        | some p => .ok p
        | none => .error "invalid character"

/-! ## The scan and its check -/

/-- Scan with fuel (each step consumes at least one byte). -/
def scan (total : Nat) : Nat → Mode → Bytes → List Piece → Except Error (List Piece × Mode)
  | _, m, [], acc => .ok (acc.reverse, m)
  | 0, _, l, _ => .error ⟨total - l.length, "out of fuel"⟩
  | fuel + 1, m, l, acc =>
    match split m l with
    | .error msg => .error ⟨total - l.length, msg⟩
    | .ok (raw, rest) =>
      match classify m raw with
      | none =>
        .error ⟨total - l.length,
          if isWord raw && m == .sol then "reserved keyword"
          else match raw with
            | b :: _ =>
              if isDigit b || b.toNat == 46 then "malformed number"
              else if b.toNat == 34 || b.toNat == 39 then "malformed string literal"
              else if isIdStart b then "malformed hex or unicode string literal"
              else "invalid lexeme"
            | [] => "invalid lexeme"⟩
      | some k => scan total fuel (m.next k) rest (⟨k, raw⟩ :: acc)

/-- Pieces classified in the modes their predecessors leave, from `m`. -/
def classifiedFrom : Mode → List Piece → Bool
  | _, [] => true
  | m, p :: ps => classify m p.raw == some p.kind && classifiedFrom (m.next p.kind) ps

/-- The mode after a list of pieces. -/
def Mode.after : Mode → List Piece → Mode
  | m, [] => m
  | m, p :: ps => Mode.after (m.next p.kind) ps

/-- No extension of `raw` by a prefix of the next piece's bytes `next` is a
lexeme of mode `m` (prefixes of a comment are tried up to two bytes, of
whitespace one byte: no longer one can complete a lexeme). -/
def maximal (m : Mode) (raw : Bytes) (next : Piece) : Bool :=
  let n := match next.kind with
    | .trivia .ws => 1
    | .trivia _ => 2
    | .tok _ => next.raw.length
  (List.range (min n next.raw.length)).all fun k => classify m (raw ++ next.raw.take (k + 1)) == none

/-- **Maximal munch**: no token or whitespace run extends into a longer
lexeme of its mode by any prefix of the next piece (pragma mode excepted). -/
def munchFrom : Mode → List Piece → Bool
  | m, p :: q :: ps =>
    (m == .pragma || (match p.kind with
      | .tok _ => maximal m p.raw q
      | .trivia .ws => maximal m p.raw q
      | .trivia _ => true)) && munchFrom (m.next p.kind) (q :: ps)
  | _, _ => true

/-- No number is followed by an identifier character. -/
def noGlue : List Piece → Bool
  | p :: q :: ps =>
    (match p.kind with
      | .tok (.num _) | .tok (.yulDec _) | .tok (.yulHex _) =>
        !(q.raw.head?.map isIdPart |>.getD false)
      | _ => true) && noGlue (q :: ps)
  | _ => true

/-- **The lexer's certificate**: the pieces re-print the input, each is
classified, maximal and unglued, and the modes return to Solidity. -/
def Lexed (s : Bytes) (ps : List Piece) : Prop :=
  (ps.map Piece.raw).flatten = s ∧ classifiedFrom .sol ps = true ∧ munchFrom .sol ps = true ∧
    noGlue ps = true ∧ Mode.after .sol ps = .sol

instance (s : Bytes) (ps : List Piece) : Decidable (Lexed s ps) := by
  unfold Lexed; exact inferInstance

/-- The offset where the mode last left Solidity mode (the start of an
open pragma or assembly block). -/
def openAt : Mode → Nat → Nat → List Piece → Nat
  | _, at_, _, [] => at_
  | m, at_, o, p :: ps =>
    let m' := m.next p.kind
    openAt m' (if m == .sol && m' != .sol then o else at_) (o + p.raw.length) ps

/-- The offset of the first piece failing the per-piece checks. -/
def firstBad : Mode → Nat → List Piece → Nat
  | _, o, [] => o
  | m, o, p :: ps =>
    let ok := classify m p.raw == some p.kind && munchFrom m (p :: ps.take 1) &&
      noGlue (p :: ps.take 1)
    if ok then firstBad (m.next p.kind) (o + p.raw.length) ps else o

/-- **The checked lexer.** -/
def lex (s : Bytes) : Except Error (List Piece) :=
  match scan s.length (s.length + 1) .sol s [] with
  | .error e => .error e
  | .ok (ps, m) =>
    if m != .sol then
      .error ⟨min (openAt .sol 0 0 ps) s.length, match m with
        | .pragma => "unterminated pragma" | _ => "unterminated assembly block"⟩
    else if Lexed s ps then .ok ps
    else .error ⟨min (firstBad .sol 0 ps) s.length, "malformed lexeme"⟩

/-! ## Located tokens -/

/-- The tokens of a piece list with their byte ranges and modes, from offset
`o` in mode `m`; trivia is dropped. -/
def locate : Mode → Nat → List Piece → List (Located × Mode)
  | _, _, [] => []
  | m, o, p :: ps =>
    let rest := locate (m.next p.kind) (o + p.raw.length) ps
    match p.kind with
    | .tok t => (⟨t, o, o + p.raw.length⟩, m) :: rest
    | .trivia _ => rest

/-- The located tokens of a source unit. -/
def tokens (s : Bytes) : Except Error (List Located) :=
  (lex s).map fun ps => (locate .sol 0 ps).map Prod.fst

/-! ## Soundness -/

/-- **Soundness**: an accepted source is cut into pieces carrying the
certificate. -/
theorem lex_sound {s : Bytes} {ps : List Piece} (h : lex s = .ok ps) : Lexed s ps := by
  unfold lex at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · next hl => cases h; exact hl
      · cases h

/-- **Re-printing**: the pieces of an accepted source concatenate to it. -/
theorem lex_reprint {s : Bytes} {ps : List Piece} (h : lex s = .ok ps) :
    (ps.map Piece.raw).flatten = s :=
  (lex_sound h).1

theorem slice_append (pre raw rest : Bytes) :
    ((pre ++ raw ++ rest).drop pre.length).take raw.length = raw := by
  simp only [List.append_assoc, List.drop_left, List.take_left]

/-- Every located token re-locates in `pre ++ pieces`: its range holds
bytes that classify as it, in its mode. -/
theorem locate_spec :
    ∀ (ps : List Piece) (m : Mode) (pre : Bytes), classifiedFrom m ps = true →
    ∀ x, x ∈ locate m pre.length ps →
      classify x.2 (((pre ++ (ps.map Piece.raw).flatten).drop x.1.start).take
        (x.1.stop - x.1.start)) = some (.tok x.1.tok) ∧
      x.1.stop ≤ (pre ++ (ps.map Piece.raw).flatten).length := by
  intro ps
  induction ps with
  | nil => intro m pre _ x hx; simp only [locate, List.not_mem_nil] at hx
  | cons p ps ih =>
    intro m pre hc x hx
    simp only [classifiedFrom, Bool.and_eq_true, beq_iff_eq] at hc
    have hrest : ∀ y, y ∈ locate (m.next p.kind) (pre ++ p.raw).length ps →
        classify y.2 ((((pre ++ p.raw) ++ (ps.map Piece.raw).flatten).drop y.1.start).take
          (y.1.stop - y.1.start)) = some (.tok y.1.tok) ∧
        y.1.stop ≤ ((pre ++ p.raw) ++ (ps.map Piece.raw).flatten).length :=
      ih (m.next p.kind) (pre ++ p.raw) hc.2
    have heq : pre ++ (List.map Piece.raw (p :: ps)).flatten =
        (pre ++ p.raw) ++ (ps.map Piece.raw).flatten := by
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    rw [heq]
    have hlen : (pre ++ p.raw).length = pre.length + p.raw.length := List.length_append
    simp only [locate] at hx
    split at hx
    · next t hk =>
      rcases List.mem_cons.mp hx with hx | hx
      · subst hx
        refine ⟨?_, ?_⟩
        · simp only [Nat.add_sub_cancel_left]
          rw [slice_append, hc.1, hk]
        · simp only [List.length_append]; omega
      · rw [← hlen] at hx; exact hrest x hx
    · rw [← hlen] at hx; exact hrest x hx

/-- **Re-location**: each token of an accepted source occupies a range of
it whose bytes classify as that token. -/
theorem lex_locate {s : Bytes} {ps : List Piece} (h : lex s = .ok ps) :
    ∀ x, x ∈ locate .sol 0 ps →
      classify x.2 ((s.drop x.1.start).take (x.1.stop - x.1.start)) = some (.tok x.1.tok) ∧
      x.1.stop ≤ s.length := by
  intro x hx
  have hs := lex_sound h
  have := locate_spec ps .sol [] hs.2.1 x hx
  rw [List.nil_append, hs.1] at this
  exact this

theorem scan_error_pos (total : Nat) :
    ∀ (fuel : Nat) (m : Mode) (l : Bytes) (acc : List Piece) (e : Error),
      scan total fuel m l acc = .error e → e.pos ≤ total := by
  intro fuel
  induction fuel with
  | zero =>
    intro m l acc e h
    cases l with
    | nil => simp only [scan, reduceCtorEq] at h
    | cons b r =>
      simp only [scan, Except.error.injEq] at h
      rw [← h]; exact Nat.sub_le _ _
  | succ n ih =>
    intro m l acc e h
    cases l with
    | nil => simp only [scan, reduceCtorEq] at h
    | cons b r =>
      simp only [scan] at h
      split at h
      · cases h; exact Nat.sub_le _ _
      · split at h
        · cases h; exact Nat.sub_le _ _
        · exact ih _ _ _ e h

/-- **Errors are located**: a refused source is refused at an offset inside
it, or at its end. -/
theorem lex_error_pos {s : Bytes} {e : Error} (h : lex s = .error e) : e.pos ≤ s.length := by
  unfold lex at h
  split at h
  · next he => cases h; exact scan_error_pos s.length _ _ _ _ e he
  · split at h
    · cases h; exact Nat.min_le_right _ _
    · split at h
      · cases h
      · cases h; exact Nat.min_le_right _ _

end Solidity.Frontend.Checked
