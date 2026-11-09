import Solidity.Frontend.SolcJson.Contract
import Solidity.Frontend.SolcJson.YulMetadata
import Solidity.Frontend.SourceUnits
import Solidity.Hashes

/-!
# Source-derived NatSpec origins, V1

Guards the editor regression where a duplicate clause's text is used to guess
its location. This isolated companion reuses the admitted compiler AST and the
legacy parser. Triple-slash documentation is mapped by byte offsets, with exact
normalized-document and clause-sequence checks; unsupported layouts yield no
origins. Legacy parsing, including its errors, is unchanged. These raw origins
do not establish correspondence with renamed or otherwise transformed canonical
postconditions, nor do they certify compiler correctness or a counterexample.
-/

namespace Solidity.Frontend
open Lean (Json)

/-- An exact raw directive extent; ordinals count every legacy key clause. -/
structure SpecClauseOriginV1 where
  ordinal : Nat
  clause : KeyClause
  span : YulJson.SourceSpan

/-- The exact legacy fields, including lexical bindings, used for alignment. -/
def specClauseFieldsV1 (clause : KeyClause) : String × String × List String :=
  (clause.kind, clause.text, clause.lexicalNames)

/-- The original parser result survives unsupported origin layouts. Every
retained table carries a kernel-typed equality of its fields to that result;
this is not yet a theorem about source elaboration into canonical formulas. -/
structure SpecOriginsV1 where
  legacy : Except String (List KeyClause)
  checkedOrigins : Option { rows : List SpecClauseOriginV1 //
    legacy.toOption.map (List.map specClauseFieldsV1) =
      some (rows.map fun row => specClauseFieldsV1 row.clause) }

def SpecOriginsV1.origins (result : SpecOriginsV1) : Option (List SpecClauseOriginV1) :=
  result.checkedOrigins.map Subtype.val

private structure DocLineV1 where
  text : String
  start : Nat
  stop : Nat

private def sourceSliceV1? (bytes : ByteArray) (span : YulJson.SourceSpan) : Option String := do
  guard (span.file ≥ 0 && span.start + span.length ≤ bytes.size)
  String.fromUTF8? (bytes.extract span.start (span.start + span.length))

/-- Only a fully matching triple-slash representation is admitted. In particular,
block comments and legacy documentation without `src` do not get guessed spans. -/
private def docLinesV1? (bytes : ByteArray) (span : YulJson.SourceSpan)
    (expected : String) : Option (List DocLineV1) := do
  let raw ← sourceSliceV1? bytes span
  let mut offset := span.start
  let mut first := true
  let mut lines : List DocLineV1 := []
  for originalLine in raw.splitOn "\n" do
    let line := if originalLine.endsWith "\r" then originalLine.take (originalLine.length - 1) else originalLine
    let stripped := line.dropWhile fun c => c == ' ' || c == '\t'
    guard (stripped.startsWith "///")
    let body := stripped.drop 3
    let text := if first then body.dropWhile Char.isWhitespace else body
    let prefixBytes := line.utf8ByteSize - text.utf8ByteSize
    lines := lines ++ [⟨text, offset + prefixBytes, offset + line.utf8ByteSize⟩]
    offset := offset + originalLine.utf8ByteSize + 1
    first := false
  guard ("\n".intercalate (lines.map (·.text)) == expected)
  pure lines

private def rawOriginsV1 (file : Int) (lines : List DocLineV1) :
    Except String (List SpecClauseOriginV1) := do
  let mut out : List SpecClauseOriginV1 := []
  let mut current : Option (String × Nat × Nat) := none
  for line in lines do
    match tagWord? line.text with
    | some (tag, rest) =>
      if let some (body, start, stop) := current then
        let clause ← keyClause body
        out := out ++ [⟨out.length, clause, ⟨start, stop - start, file⟩⟩]
      let stripped := line.text.dropWhile fun c => c == ' ' || c == '\t'
      let start := line.start + line.text.utf8ByteSize - stripped.utf8ByteSize
      current := if tag == "@custom:key" then some (rest, start, line.stop) else none
    | none => current := current.map fun (body, start, _) =>
        (body ++ "\n" ++ line.text, start, line.stop)
  if let some (body, start, stop) := current then
    let clause ← keyClause body
    out := out ++ [⟨out.length, clause, ⟨start, stop - start, file⟩⟩]
  pure out

private def sameClauseV1 (a b : KeyClause) : Bool :=
  a.kind == b.kind && a.text == b.text && a.lexicalNames == b.lexicalNames

private def originsForNodeV1? (owner : Json) (bytes : ByteArray)
    (legacy : Except String (List KeyClause)) : Option (List SpecClauseOriginV1) := do
  let clauses ← legacy.toOption
  let declaration ← (J.str? owner "src").bind (YulJson.sourceSpan · |>.toOption)
  let doc ← J.opt owner "documentation"
  let span ← (J.str? doc "src").bind (YulJson.sourceSpan · |>.toOption)
  guard (span.file == declaration.file)
  let lines ← docLinesV1? bytes span (docText owner)
  let origins ← (rawOriginsV1 span.file lines).toOption
  guard (origins.length == clauses.length &&
    (origins.zip clauses).all fun (origin, clause) => sameClauseV1 origin.clause clause)
  pure origins

/-- Projection preserves the exact old parser, regardless of origin support.
Call `admittedSpecOriginsV1?` to establish source admission and byte identity. -/
def specOriginsV1 (owner : Json) (bytes : ByteArray) : SpecOriginsV1 :=
  let legacy := keyClauses (docText owner)
  let checked := do
    let rows ← originsForNodeV1? owner bytes legacy
    if h : legacy.toOption.map (List.map specClauseFieldsV1) =
        some (rows.map fun row => specClauseFieldsV1 row.clause) then
      some ⟨rows, h⟩ else none
  ⟨legacy, checked⟩

theorem specOriginsV1_forget (owner : Json) (bytes : ByteArray) :
    (specOriginsV1 owner bytes).legacy = keyClauses (docText owner) := rfl

private def nodesWithIdV1 : Nat → Json → Int → List Json
  | 0, _, _ => []
  | fuel + 1, node, id =>
    let here := if J.id? node == some id then [node] else []
    here ++ match node with
      | .arr items => items.toList.flatMap fun child => nodesWithIdV1 fuel child id
      | .obj fields => fields.toList.flatMap fun (_, child) => nodesWithIdV1 fuel child id
      | _ => []

private def digestNatV1? (digest : String) : Option Nat := do
  guard (digest.length == 64)
  let mut value := 0
  for c in digest.toList do
    let digit ← if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
    value := 16 * value + digit
  pure value

/-- Ownership travels with an admitted computation. This carrier is not an
external-authentication certificate; consumers must retain its complete context.
The equation prevents a result from being silently replaced inside this carrier. -/
structure AdmittedSpecOriginsV1 where
  provenance : Source.Provenance
  sourceName : String
  sourceSha256 : String
  ownerId : Int
  owner : Json
  bytes : ByteArray
  result : SpecOriginsV1
  resultEquation : result = specOriginsV1 owner bytes

theorem admittedSpecOriginsV1_forget (origin : AdmittedSpecOriginsV1) :
    origin.result.legacy = keyClauses (docText origin.owner) :=
  congrArg SpecOriginsV1.legacy origin.resultEquation

/-- Native source admission is reused. The selected snapshot is SHA-checked;
a unique declaration and its source identity must agree. This certifies neither
the external compiler nor transformed canonical-postcondition correspondence. -/
def admittedSpecOriginsV1? (fixture : Json) (sourceName : String)
    (bytes : ByteArray) (ownerId : Int) : Option AdmittedSpecOriginsV1 := do
  let unit ← (Source.readCompilationUnit fixture).toOption
  guard (!unit.provenance.legacyFixture)
  let source ← if unit.provenance.sources.isEmpty then do
      guard (sourceName == unit.provenance.source)
      let src ← J.str? unit.primary "src"
      let span ← (YulJson.sourceSpan src).toOption
      pure (span.file, unit.provenance.sourceSha256)
    else do
      let entry ← unit.provenance.sources.find? (·.name == sourceName)
      pure (Int.ofNat entry.sourceId, entry.sourceSha256)
  let expected ← digestNatV1? source.2
  guard (Hashes.sha256Nat (bytes.data.toList.map UInt8.toNat) == expected)
  let owners := unit.asts.flatMap fun ast => nodesWithIdV1 (ast.compress.length + 1) ast ownerId
  let [owner] := owners | none
  let span ← (J.str? owner "src").bind (YulJson.sourceSpan · |>.toOption)
  guard (span.file == source.1 && span.start + span.length ≤ bytes.size)
  pure ⟨unit.provenance, sourceName, source.2, ownerId, owner, bytes, specOriginsV1 owner bytes, rfl⟩

/-- Exact ordinal/range data lookup never falls back to an equal clause's text.
This Boolean is not an authenticity or canonical-postcondition certificate. -/
def SpecOriginsV1.accepts (result : SpecOriginsV1) (ordinal : Nat)
    (span : YulJson.SourceSpan) : Bool :=
  (result.origins.bind (·[ordinal]?)).any fun origin =>
    origin.ordinal == ordinal && decide (origin.span = span)

end Solidity.Frontend
