import Solidity.TacletAnnotations

/-!
# Token-level parser for `solidityProgramRules.key`

The text side of the conformance loop (`lake exe solkeycheck`): a
string-level scanner that extracts, per taclet, the read-operation
tokens (`find<[..]>`, `read<[..]>`, `selectSt<[..]>`,
`defaultValue<[..]>`, `valAt(..)`) and the `\has*Sort` varconds, and
`conforms`, which cross-checks the scan against
`TacletAnnotations.tacletReadAnns`.

This is deliberately not a KeY grammar: it pins read tokens and
varconds, nothing more. Two fail-loudly guards keep the token approach
honest: any `<[` whose head symbol is not one of the known read symbols
is reported (`UNKNOWN TOKEN`), and any read-bearing taclet without a
table row is reported (`UNANNOTATED READS`) — so a *new* kind of sorted
read cannot slip through silently.
-/

namespace Solidity
namespace KeyTacletParser

open TacletAnnotations

structure ParsedRead where
  /-- Head symbol: `find`, `read`, `selectSt`, `defaultValue`, `valAt`. -/
  token : String
  /-- Sort between `<[` and `]>`; `""` for `valAt`. -/
  sortTok : String
  /-- Whitespace-stripped balanced-paren argument text; `""` when the
  symbol has no immediate argument list (`defaultValue<[..]>`). -/
  arg : String
  deriving Repr, DecidableEq

structure ParsedTaclet where
  name : String
  varconds : List String
  reads : List ParsedRead
  /-- `ident<[sort` occurrences with an unrecognized head symbol. -/
  unknown : List String
  deriving Repr

/-! ## Comment stripping -/

private def stripCommentsGo : Nat -> List Char -> List Char -> List Char
  | 0, _, acc => acc.reverse
  | _, [], acc => acc.reverse
  | fuel + 1, '/' :: '/' :: rest, acc =>
      stripCommentsGo fuel (rest.dropWhile (· != '\n')) acc
  | fuel + 1, '/' :: '*' :: rest, acc => dropBlock fuel rest acc
  | fuel + 1, c :: rest, acc => stripCommentsGo fuel rest (c :: acc)
where
  dropBlock : Nat -> List Char -> List Char -> List Char
    | 0, _, acc => acc.reverse
    | _, [], acc => acc.reverse
    | fuel + 1, '*' :: '/' :: rest, acc => stripCommentsGo fuel rest acc
    | fuel + 1, _ :: rest, acc => dropBlock fuel rest acc

def stripComments (s : String) : String :=
  String.mk (stripCommentsGo (s.length + 1) s.toList [])

/-! ## Taclet grouping -/

private def braceBalance (l : String) : Int :=
  l.foldl (fun acc c =>
    if c = '{' then acc + 1 else if c = '}' then acc - 1 else acc) 0

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c = '_'

/-- A line of the form `ident {` (any indentation): a taclet header.
Block openers like `\rules {` start with a backslash and are not
matched. -/
private def headerName? (l : String) : Option String :=
  let t := l.trim
  if t.endsWith "{" then
    let n := (t.dropRight 1).trim
    match n.toList with
    | [] => none
    | c :: cs =>
        if !c.isDigit && (c :: cs).all isIdentChar then some n else none
  else none

private structure GroupState where
  taclets : List (String × String) := []
  current : Option (String × String × Int) := none

private def groupLines (ls : List String) : List (String × String) :=
  let final := ls.foldl (init := ({} : GroupState)) (fun st l =>
    match st.current with
    | none =>
        match headerName? l with
        | some n => { st with current := some (n, "", braceBalance l) }
        | none => st
    | some (n, body, depth) =>
        let depth := depth + braceBalance l
        if depth ≤ 0 then
          { taclets := (n, body) :: st.taclets, current := none }
        else
          { st with current := some (n, body ++ l ++ "\n", depth) })
  final.taclets.reverse

/-! ## Read-token scanning -/

private def stripWs (s : String) : String :=
  String.mk (s.toList.filter (fun c => !c.isWhitespace))

/-- Capture the text of a balanced-paren argument list; `cs` starts
just after the opening `(`. Returns the inner text and the remainder
after the matching `)`. -/
private def captureParenGo :
    Nat -> Int -> List Char -> List Char -> List Char × List Char
  | 0, _, cs, acc => (acc.reverse, cs)
  | _, _, [], acc => (acc.reverse, [])
  | fuel + 1, depth, c :: rest, acc =>
      if c = ')' then
        if depth = 0 then (acc.reverse, rest)
        else captureParenGo fuel (depth - 1) rest (c :: acc)
      else if c = '(' then captureParenGo fuel (depth + 1) rest (c :: acc)
      else captureParenGo fuel depth rest (c :: acc)

private def captureParen (fuel : Nat) (depth : Int) (cs : List Char) :
    List Char × List Char :=
  captureParenGo fuel depth cs []

private def knownReadTokens : List String :=
  ["find", "read", "selectSt", "defaultValue"]

/-- Scan a taclet body for read tokens. `identBuf` holds the (reversed)
identifier immediately before the scan position. -/
private def scanReadsGo :
    Nat -> List Char -> List Char -> List ParsedRead -> List String ->
      List ParsedRead × List String
  | 0, _, _, acc, unk => (acc.reverse, unk.reverse)
  | _, [], _, acc, unk => (acc.reverse, unk.reverse)
  | fuel + 1, '<' :: '[' :: rest, identBuf, acc, unk =>
      let tok := String.mk identBuf.reverse
      let sortChars := rest.takeWhile (· != ']')
      let afterSort := (rest.dropWhile (· != ']')).drop 2  -- "]>"
      let sortTok := String.mk sortChars
      if knownReadTokens.contains tok then
        match afterSort with
        | '(' :: argRest =>
            let (inner, rem) := captureParen (argRest.length + 1) 0 argRest
            scanReadsGo fuel rem []
              (⟨tok, sortTok, stripWs (String.mk inner)⟩ :: acc) unk
        | _ =>
            scanReadsGo fuel afterSort [] (⟨tok, sortTok, ""⟩ :: acc) unk
      else
        scanReadsGo fuel afterSort [] acc ((tok ++ "<[" ++ sortTok) :: unk)
  | fuel + 1, c :: rest, identBuf, acc, unk =>
      if c = '(' && String.mk identBuf.reverse = "valAt" then
        let (inner, rem) := captureParen (rest.length + 1) 0 rest
        scanReadsGo fuel rem []
          (⟨"valAt", "", stripWs (String.mk inner)⟩ :: acc) unk
      else if isIdentChar c then
        scanReadsGo fuel rest (c :: identBuf) acc unk
      else
        scanReadsGo fuel rest [] acc unk

def scanReads (body : String) : List ParsedRead × List String :=
  scanReadsGo (body.length + 1) body.toList [] [] []

def varcondNames : List String :=
  ["hasSort", "hasFieldSort", "hasElementSort", "hasMemoryFieldSort",
    "hasMemoryElementSort"]

def scanVarconds (body : String) : List String :=
  varcondNames.filter fun vc =>
    (body.splitOn ("\\" ++ vc ++ "(")).length > 1

def parseKeyFile (src : String) : List ParsedTaclet :=
  (groupLines ((stripComments src).splitOn "\n")).map fun (n, body) =>
    let (reads, unknown) := scanReads body
    { name := n, varconds := scanVarconds body, reads, unknown }

/-! ## Abstraction to the annotation vocabulary -/

/-- The whole `\has*Sort` family. A generic sort token is resolved against
the varconds the taclet actually carries, not against the token's name:
`alphaPrim` is a *bound* (`\generic alphaPrim \extends Prim`) and since
solkey `0f9b99ad55` it is used under the memory varconds too
(`memoryFieldDeletePrimitive`: `defaultValue<[alphaPrim]>` under
`\hasMemoryFieldSort(a, \sort(alphaPrim))`). -/
private def sortVarconds : List (String × SortVarcond) :=
  [("hasSort", .hasSort), ("hasFieldSort", .hasFieldSort),
    ("hasElementSort", .hasElementSort),
    ("hasMemoryFieldSort", .hasMemoryFieldSort),
    ("hasMemoryElementSort", .hasMemoryElementSort)]

private def resolveVarcond (t : ParsedTaclet)
    (table : List (String × SortVarcond)) : Except String SortVarcond :=
  match table.filter (fun p => t.varconds.contains p.1) with
  | [(_, vc)] => .ok vc
  | [] => .error s!"VARCOND DRIFT: {t.name}: generic sort token without \
      a matching \\has*Sort varcond"
  | _ => .error s!"VARCOND DRIFT: {t.name}: ambiguous \\has*Sort \
      varconds for a generic sort token"

private def readDomain (r : ParsedRead) : ReadDomain :=
  match r.token with
  | "read" => .memory
  | "defaultValue" => .memory
  | "selectSt" => if r.arg.startsWith "net" then .net else .storage
  | _ => .storage

private def readSite (domain : ReadDomain) (r : ParsedRead) : ReadSite :=
  if r.token = "defaultValue" then .dflt
  else if domain matches .net then .net
  else if r.arg.endsWith "size" || r.arg.endsWith "size)" then .length
  else .value

/-- Abstract one scanned read to the `TacletAnnotations` vocabulary. A
fixed sort token is looked up in the lattice (`KeySort.ofName`); a token
that names no declared sort is an error, and a fixed sort the
faithfulness proofs do not cover fails `sortFaithful_all` rather than
being silently accepted. -/
def abstractRead (t : ParsedTaclet) (r : ParsedRead) :
    Except String TacletRead := do
  let domain := readDomain r
  let site := readSite domain r
  let sort : ReadSort <-
    match r.sortTok with
    | "" => .ok (.fixed .stValue)
    | "alphaPrim" | "alpha" | "alphaMem" | "alphaId" | "alphaSt" =>
        .generic <$> resolveVarcond t sortVarconds
    | other =>
        match KeySort.ofName other with
        | some s => .ok (.fixed s)
        | none => .error s!"UNKNOWN SORT: {t.name}: {r.token}<[{other}]>"
  return ⟨domain, site, sort⟩

/-! ## Conformance -/

def SortVarcond.render : SortVarcond -> String
  | .hasSort => "hasSort"
  | .hasFieldSort => "hasFieldSort"
  | .hasElementSort => "hasElementSort"
  | .hasMemoryFieldSort => "hasMemoryFieldSort"
  | .hasMemoryElementSort => "hasMemoryElementSort"

def TacletRead.render (r : TacletRead) : String :=
  let domain := match r.domain with
    | .storage => "storage" | .memory => "memory" | .net => "net"
  let site := match r.site with
    | .value => "value" | .length => "length" | .net => "net"
    | .dflt => "default"
  let sort := match r.sort with
    | .fixed s => s!"fixed {s.name}"
    | .generic vc => s!"generic via {SortVarcond.render vc}"
  s!"{domain}/{site}/{sort}"

private def renderReads (rs : List TacletRead) : String :=
  if rs.isEmpty then "(none)"
  else String.intercalate ", " (rs.map TacletRead.render)

/-- Multiset equality of read lists (file order is irrelevant). -/
private def readsMatch (a b : List TacletRead) : Bool :=
  a.length == b.length && a.all fun r => a.count r == b.count r

/-- Cross-check the annotation table against the parsed file. Returns
human-readable mismatch reports; `[]` means the table and the taclet
text agree. -/
def conforms (anns : List TacletReadAnn) (parsed : List ParsedTaclet) :
    List String :=
  let tableErrors := anns.flatMap fun ann =>
    match parsed.find? (fun t => t.name == ann.keyName) with
    | none => [s!"MISSING TACLET: {ann.keyName}: in the annotation \
        table but not in the .key file"]
    | some t =>
        match t.reads.mapM (abstractRead t) with
        | .error e => [e]
        | .ok abstracted =>
            if readsMatch abstracted ann.reads then []
            else [s!"READ DRIFT: {ann.keyName}: file has \
                [{renderReads abstracted}], table has \
                [{renderReads ann.reads}]"]
  let unknownErrors := parsed.flatMap fun t =>
    t.unknown.map fun u => s!"UNKNOWN TOKEN: {t.name}: {u}<[..]>"
  let uncovered := parsed.flatMap fun t =>
    if t.reads.isEmpty || anns.any (fun ann => ann.keyName == t.name)
    then []
    else [s!"UNANNOTATED READS: {t.name}: taclet reads \
        {t.reads.length} value(s) but has no annotation-table row"]
  tableErrors ++ unknownErrors ++ uncovered

/-! ## Snippet tests

Miniature taclet texts pinning the scanner's behavior, including the
pre-fix `storageRootWriteCopySource` (must produce a `READ DRIFT`
against the current table) and a commented-out read (must be
ignored).  The scanner sees only the reads, so the write's spelling is
immaterial to it and the snippet tracks upstream for readers rather than
for the test. -/

private def currentRootCopySnippet : String :=
"\\rules {
    storageRootWriteCopySource {
        \\schemaVar \\formula post;

        \\find(\\modality{#mod}{c# s#gp = s#sp; #c}\\endmodality(post))
        \\replacewith({storage := save(storage, gp, find<[StValue]>(storage, sp))}
            \\modality{#mod}{c# #c}\\endmodality(post))
        \\heuristics(simplify_prog)
    };
}"

private def preFixRootCopySnippet : String :=
"\\rules {
    storageRootWriteCopySource {
        // a commented find<[Struct]>(storage, sp) must be ignored
        \\find(\\modality{#mod}{c# s#gp = s#sp; #c}\\endmodality(post))
        \\replacewith({storage := save(storage, gp, find<[int]>(storage, sp))}
            \\modality{#mod}{c# #c}\\endmodality(post))
    };
}"

private def readSelectSnippet : String :=
"\\rules {
    storageRootReadSelect {
        \\find(\\modality{#mod}{c# s#v =s#sp; #c}\\endmodality(post))
        \\varcond(\\hasSort(sp, \\sort(alphaPrim)))
        \\replacewith({v := find<[alphaPrim]>(storage, sp)}
            \\modality{#mod}{c# #c}\\endmodality(post))
    };
}"

private def boundsSnippet : String :=
"\\rules {
    storageIndexReadArrayBindLocalRoot {
        \\replacewith(0 <= i & i < find<[int]>(storage, consr(sp, size))
                & {lp := consr(sp, at(i))} post)
    };
}"

private def rootCopyAnnOnly : List TacletReadAnn :=
  tacletReadAnns.filter (·.keyName == "storageRootWriteCopySource")

example :
    conforms rootCopyAnnOnly (parseKeyFile currentRootCopySnippet)
      = [] := by
  native_decide

-- The pre-fix taclet text (hard-coded `find<[int]>`) drifts from the
-- current table row — the checker catches the `12e72a1b4b` bug class.
example :
    conforms rootCopyAnnOnly (parseKeyFile preFixRootCopySnippet)
      ≠ [] := by
  native_decide

-- The commented-out `find<[Struct]>` is invisible: the parsed reads of
-- the pre-fix snippet are exactly one int-sorted storage value read.
example :
    ((parseKeyFile preFixRootCopySnippet).map (·.reads)) =
      [[⟨"find", "int", "storage,sp"⟩]] := by
  native_decide

example :
    conforms
      (tacletReadAnns.filter (·.keyName == "storageRootReadSelect"))
      (parseKeyFile readSelectSnippet) = [] := by
  native_decide

-- A `.. size` read classifies as a length site.
example :
    conforms
      (tacletReadAnns.filter
        (·.keyName == "storageIndexReadArrayBindLocalRoot"))
      (parseKeyFile boundsSnippet) = [] := by
  native_decide

-- A read-bearing taclet with no table row is reported.
example :
    conforms [] (parseKeyFile boundsSnippet) ≠ [] := by
  native_decide

end KeyTacletParser
end Solidity
