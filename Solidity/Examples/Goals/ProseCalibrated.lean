import Solidity.Goals.ProseCalibrated

namespace Solidity.Goals
/--
info: open Solidity.Goals.proseCalibratedRatioRuleSound ← Solidity.Docs.prose_calibrated_ratio_rule_sound plan pb2-prose-ratio-rule
-/
#guard_msgs in
#roadmap_goal proseCalibratedRatioRuleSound
end Solidity.Goals

namespace Solidity.Examples.Goals.ProseCalibrated
open Solidity.Goals.ProseCalibrated
open Solidity.Goals.ProseRatio (Category)

private def half : Rational := ⟨1, 2, by decide⟩
private def w : Allowance := ⟨half, half⟩
#guard w.lines 1 = 1
#guard w.ratio.num * 1 / w.ratio.den + w.margin.num / w.margin.den = 0
#guard w.fits 1 1
#guard !w.fits 2 1
#guard (Allowance.mk ⟨2,4,by decide⟩ ⟨3,6,by decide⟩).fits 1 1
#guard (Allowance.mk ⟨2,4,by decide⟩ ⟨3,6,by decide⟩).lines 1 = w.lines 1
#guard w.fits 0 0
#guard !w.fits 1 0
#guard (Allowance.mk half ⟨3,2,by decide⟩).fits 1 0
#guard !(Allowance.mk half ⟨3,2,by decide⟩).fits 2 0
#guard (calibrate 12 0 [(2,4),(5,0)]).ratio.num = 0
#guard (calibrate 12 0 [(2,4),(5,0)]).lines 100 = 5
#guard (calibrate 0 7 [(2,4),(5,0)]).lines 100 = 5
#guard (calibrate 0 7 [(2,4),(5,0)]).ratio.num = 0
#guard (lookup [] (["unseen"], .docs)).fits 0 900
#guard !(lookup [] (["unseen"], .docs)).fits 1 900

private def scope : Scope where
  registeredImport := fun p i j => p == ["Solidity","A","Root.lean"] && i == 0 && j == 0
  verified := []
  provenance := "frozen external binding required"
  selection := "frozen history; never the candidate"

private def file (p : List String) (ls : List Solidity.Goals.ProseRatio.Line) : File :=
  ⟨p,"output",["generator"], "generator-blob", false,ls⟩
private def sourceA := file ["Solidity","A","a.lean"] [[.code "def x := 0"]]
private def sourceB := file ["Solidity","B","b.lean"] [[.code "def y := 0"]]
private def doc := file ["docs","guide","x.md"] [[],[]]
private def policy : Policy := ⟨scope, [((["docs","guide"], .docs), ⟨⟨1,1,by decide⟩,.zero⟩)]⟩
#guard !accepts policy [doc,sourceA]
#guard accepts policy [doc,sourceA,sourceB]
#guard denominator scope [doc,sourceA,sourceB] ["Solidity","A"] = 1
#guard denominator scope [doc,sourceA] ["Solidity","A"] = 1
#guard denominator scope [doc,sourceA,sourceB] ["docs","guide"] = 2
#guard !accepts ⟨scope,[]⟩ [doc]
#guard accepts ⟨scope,[]⟩ []
#guard !decision policy none
#guard numerator scope [file ["docs","audits","x.md"] [[],[]]] ["docs","audits"] .docs = 2
#guard accepts ⟨scope,[]⟩ [file ["docs","audits","x.md"] [[],[]]]

private def mixed := file ["Solidity","A","a.lean"]
  [[.docstring "doc", .comment "comment", .processId "H1", .processId "H1"]]
#guard codeFile scope mixed = 0
#guard proseFile scope mixed .comment = 1
#guard proseFile scope mixed .docstring = 1
#guard proseFile scope mixed .processId = 2
#guard proseFile scope mixed .docs = 0
#guard proseFile scope { mixed with path := ["Solidity","A","Root.lean"] } .processId = 2
#guard proseFile scope (file ["Solidity","A","Root.lean"] [[.processId "G1", .processId "H1", .processId "G2"]]) .processId = 2
#guard proseFile scope { mixed with path := ["Solidity","A","Other.lean"] } .processId = 2
#guard codeFile scope (file ["Solidity","A","x.lean"] [[.code " \t"], [.comment "c"], [.processId "H1"]]) = 0
private def boundaryFile (k : Category) (n : Nat) : File :=
  if k == .docs then file ["docs","guide","boundary"] (List.replicate n [])
  else file ["Solidity","A","boundary.lean"] (List.replicate n
    [match k with | .comment => .comment "c" | .docstring => .docstring "d"
                  | .processId => .processId "H1" | .docs => .comment "unused"])
private def metricPolicy (k : Category) : Policy :=
  let a := if k == .docs then ["docs","guide"] else ["Solidity","A"]
  ⟨scope, Category.all.map fun j => ((a,j), ⟨.zero, Rational.ofNat (if j == k then 1 else 100)⟩)⟩
#guard Category.all.all (fun k => accepts (metricPolicy k) [boundaryFile k 1] &&
  !accepts (metricPolicy k) [boundaryFile k 2])
#guard !accepts ⟨scope,[]⟩ [mixed]
#guard !accepts ⟨scope,[]⟩ [mixed, file ["Solidity","A","padding.lean"] [[.code " "], [.comment "c"]]]

private def frozen : Policy := ⟨scope,[((["Solidity","A"],.comment),w)]⟩
private def raised : Entries := [((["Solidity","A"],.comment),⟨⟨9,1,by decide⟩,⟨8,1,by decide⟩⟩)]
#guard (lookup (frozen.shrink raised).entries (["Solidity","A"],.comment)).lines 1 = 1
#guard (lookup (frozen.shrink [((["Solidity","A"],.comment),⟨half,⟨9,1,by decide⟩⟩)]).entries
  (["Solidity","A"],.comment)).lines 1 = 1
#guard (frozen.shrink raised).scope.provenance = frozen.scope.provenance
#guard (frozen.shrink raised).scope.selection = frozen.scope.selection
#guard (frozen.shrink raised).entries.map (·.1) = frozen.entries.map (·.1)
#guard (lookup (frozen.shrink [((["Solidity","A"],.comment),⟨⟨9,1,by decide⟩,half⟩)]).entries
  (["Solidity","A"],.comment)).lines 1 = 1
-- Candidate bytes/headers/hash-like strings have no policy replacement input.
private def replacementTree := [boundaryFile .comment 2]
#guard !accepts frozen replacementTree
#guard accepts ⟨scope,raised⟩ replacementTree
#guard !accepts (frozen.shrink raised) replacementTree
#guard !accepts frozen (replacementTree ++ [file ["outside","rewritten-policy-hash"] []])

private def entry : GeneratedEntry :=
  ⟨mixed.path,mixed.outputBlob,mixed.generatorPath,mixed.generatorBlob,"external reproduction required"⟩
private def verifiedScope : Scope := { scope with verified := [entry] }
#guard !verified scope { mixed with generationHeader := true }
#guard verified verifiedScope mixed
#guard codeFile verifiedScope sourceA = 0
#guard Category.all.all (fun k => proseFile verifiedScope mixed k == 0)
#guard !verified verifiedScope { mixed with path := ["Solidity","B","other"] }
#guard !verified verifiedScope { mixed with outputBlob := "edited" }
#guard !verified verifiedScope { mixed with generatorBlob := "edited" }
#guard !verified verifiedScope { mixed with generatorPath := ["other-generator"] }
#guard !accepts ⟨scope,[]⟩ [{ mixed with generationHeader := true }]
#guard accepts ⟨verifiedScope,[]⟩ [mixed]
#guard !accepts ⟨verifiedScope,[]⟩ [{ mixed with outputBlob := "edited" }]
#guard !accepts ⟨verifiedScope,[]⟩ [{ mixed with generatorBlob := "edited" }]
#guard accepts ⟨verifiedScope,[]⟩ [mixed] == accepts ⟨verifiedScope,[]⟩ []
#guard accepts ⟨verifiedScope,[]⟩ [doc,mixed] == accepts ⟨verifiedScope,[]⟩ [doc]
-- These synthetic classification controls certify neither the Python lexer,
-- registry importer nor actual generator reproduction. Identities stay fixed
-- for padding; blob edits above intentionally lapse verification.
end Solidity.Examples.Goals.ProseCalibrated
