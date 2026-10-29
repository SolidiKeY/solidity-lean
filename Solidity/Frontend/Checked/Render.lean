import Solidity.Frontend.Checked.Print
import Solidity.Frontend.Checked.Lexer

/-!
# Printing source text (G09)

`Tok.render` spells a token canonically, `renderToks` separates tokens by
one space, and `Syn.print t L` is the source text of a tree under a layout.
The lexer reads a rendered token back as the same token: checked on the
witnesses (`Solidity/Frontend/Checked/TypeExamples.lean`) and over the corpus
by the round-trip regression (`scripts/check-parse-corpus.mjs`); with
`parse_sound` this makes `parse (print t L)` return `t` for every tested `t`.

Canonical spellings: decimal numbers as their exact mantissa with the
fraction point and exponent (`2.5e-3`), hexadecimal numbers with EIP-55
casing when the token is checksummed and lowercase otherwise (so the flag
survives), strings with `\xNN` for every byte outside printable ASCII and for
quotes and backslashes, hex strings as lowercase digit pairs.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- The decimal digits of a number. -/
def natDigits (n : Nat) : Bytes := ascii (toString n)

def hexByte (d : Nat) (upper : Bool) : UInt8 :=
  if d < 10 then (48 + d).toUInt8 else if upper then (55 + d).toUInt8 else (87 + d).toUInt8

/-- The digits of a hexadecimal literal: EIP-55 cased when checksummed. -/
def hexLitDigits (ds : List (Fin 16)) (checksummed : Bool) : Bytes :=
  let lower := ds.map fun d => hexByte d.val false
  if checksummed && ds.length == 40 then
    let h := Solidity.Keccak.keccak256 (lower.map UInt8.toNat)
    (List.range ds.length).zip ds |>.map fun (i, d) =>
      let byte := h.getD (i / 2) 0
      let nib := if i % 2 == 0 then byte / 16 else byte % 16
      hexByte d.val (8 ≤ nib)
  else lower

/-- A decimal literal's exact spelling. -/
def decSpell (m f : Nat) (e : Int) : Bytes :=
  let ds := natDigits m
  let ds := List.replicate (f + 1 - ds.length) 48 ++ ds
  let body := if f == 0 then ds else ds.take (ds.length - f) ++ [46] ++ ds.drop (ds.length - f)
  body ++ (if e == 0 then [] else ascii "e" ++ (if e < 0 then [45] else []) ++ natDigits e.natAbs)

/-- A string body: printable ASCII verbatim except quote and backslash. -/
def escapeBytes (keepHigh : Bool) : Bytes → Bytes
  | [] => []
  | b :: r =>
    let n := b.toNat
    (if 32 ≤ n && n ≤ 126 && n != 34 && n != 92 || (keepHigh && 128 ≤ n) then [b]
     else [92, 120, hexByte (n / 16) false, hexByte (n % 16) false]) ++ escapeBytes keepHigh r

def Elem.render : Elem → Bytes
  | .address => ascii "address" | .addressPayable => ascii "address payable"
  | .bool => ascii "bool" | .string => ascii "string" | .bytes => ascii "bytes"
  | .int s n _ => ascii (if s then "int" else "uint") ++ natDigits n
  | .fixedBytes n _ => ascii "bytes" ++ natDigits n
  | .fixed s none => ascii (if s then "fixed" else "ufixed")
  | .fixed s (some d) =>
    ascii (if s then "fixed" else "ufixed") ++ natDigits d.bits ++ ascii "x" ++ natDigits d.digits

def Denom.render : Denom → Bytes
  | .wei => ascii "wei" | .gwei => ascii "gwei" | .ether => ascii "ether"
  | .seconds => ascii "seconds" | .minutes => ascii "minutes" | .hours => ascii "hours"
  | .days => ascii "days" | .weeks => ascii "weeks" | .years => ascii "years"

/-- A token's canonical spelling. -/
def Tok.render : Tok → Bytes
  | .kw k => k.bytes
  | .punct p => p.bytes
  | .elem e => Elem.render e
  | .denom d => Denom.render d
  | .bool b => ascii (if b then "true" else "false")
  | .ident s => ascii s
  | .num (.dec m f e) => decSpell m f e
  | .num (.hex ds c) => ascii "0x" ++ hexLitDigits ds c
  | .str b => [34] ++ escapeBytes false b ++ [34]
  | .hexStr b => ascii "hex\"" ++ b.flatMap (fun x => [hexByte (x.toNat / 16) false,
      hexByte (x.toNat % 16) false]) ++ [34]
  | .unicodeStr b => ascii "unicode\"" ++ escapeBytes true b ++ [34]
  | .pragmaWord w => ascii w
  | .yulKw k => k.bytes
  | .yulDec n => natDigits n
  | .yulHex n => ascii "0x" ++ ascii (String.mk (Nat.toDigits 16 n))

/-- Tokens separated by one space. -/
def renderToks (ts : List Tok) : Bytes := ((ts.map Tok.render).intersperse [32]).flatten

end Solidity.Frontend.Checked

namespace Solidity.Source

open Solidity.Frontend.Checked

/-- **The printer**: a tree's source text under a layout. -/
def Syn.print {c : Cat} (t : Syn c) (L : List Choice) : Option Bytes := (t.toks L).map renderToks

end Solidity.Source
