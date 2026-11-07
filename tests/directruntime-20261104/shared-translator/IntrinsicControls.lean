import Solidity.Frontend.ExecutableAst.Shared.Translate
import Solidity.Frontend.ExecutableAst.Shared.Intrinsic
import Solidity.Frontend.Import

/-! Typed builder/callback controls, executed during development.
These check the existing lowering callback, modality, premise transport and
refusal gates. They are not AST-to-solc source-equivalence theorems. -/
open Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared

private def emptyDecl : FunDecl := { params := [], rets := [], body := [] }
private def exampleContract (d : FunDecl) : Contract := { vars := [], funs := [("f", d)] }
private def markerPre (C : Contract) (Γ : NCtx) : Fml C Γ.ctx := .not .tt
private def failedLowering : BodyLoopLowerer := fun _ _ _ => ElabM.lift (.error "lowering sentinel")
private def emptyC : Contract := exampleContract emptyDecl

#check BodyLoopLowerer
#check PlainEntryPre
#check assertionObligation
#check obligation

-- The production loop-lowering helper is passed, not copied or reimplemented.
#guard match assertionObligation lowerBodyLoops markerPre emptyC "f" true with
  | .ok (.imp (.not .tt) (.imp (.wellFormed _) (.modal .box _ _ .tt))) => true
  | _ => false
#guard match assertionObligation lowerBodyLoops markerPre emptyC "f" false with
  | .ok (.imp (.not .tt) (.imp (.wellFormed _) (.modal .diamond _ _ .tt))) => true
  | _ => false
#guard match assertionObligation failedLowering markerPre emptyC "f" true with
  | .error "lowering sentinel" => true | _ => false
#guard match assertionObligation failedLowering markerPre emptyC "missing" true with
  | .error "missing function" => true | _ => false

private def scalarC : Contract := exampleContract
  { emptyDecl with params := [("x", .prim .uint)] }
#guard match assertionObligation lowerBodyLoops markerPre scalarC "f" false with
  | .ok (.all _ .uint (.imp (.not .tt) (.imp (.wellFormed _) (.modal .diamond _ _ .tt)))) => true
  | _ => false

-- No reference parameter can silently acquire box binders in diamond mode.
private def referenceC : Contract := exampleContract
  { emptyDecl with params := [("xs", .array (.prim .uint))], paramLocs := [("xs", .memory)] }
#guard match assertionObligation lowerBodyLoops markerPre referenceC "f" false with
  | .error "plain reference obligation" => true | _ => false
#guard match assertionObligation lowerBodyLoops markerPre referenceC "f" true with
  | .error "plain reference obligation" => true | _ => false
private def returnC : Contract := exampleContract
  { emptyDecl with rets := [("result", .prim .uint)] }
#guard match assertionObligation failedLowering markerPre returnC "f" true with
  | .error "lowering sentinel" => true | _ => false

-- The specified branch calls the existing spec builder and never plain lowering.
#guard match obligation failedLowering markerPre emptyC "f" true false with
  | .ok _ => true | _ => false
#guard match obligation failedLowering markerPre emptyC "f" false false with
  | .error "lowering sentinel" => true | _ => false

-- Known producer/shared normalization gap: raw signed complement decodes,
-- while intrinsic unary complement accepts uint only. This is not support.
private def signedComplement : Lean.Json := Lean.Json.mkObj [
  ("nodeType", "UnaryOperation"), ("operator", "~"), ("prefix", .bool true),
  ("typeDescriptions", Lean.Json.mkObj [("typeString", "int256")]),
  ("subExpression", Lean.Json.mkObj [("nodeType", "Identifier"), ("name", "x"),
    ("typeDescriptions", Lean.Json.mkObj [("typeString", "int256")])])]
#guard match checkedExpression signedComplement with
  | .ok (.unop .bnot (.name "x")) => true | _ => false
private def signedComplementC : Contract := exampleContract
  { emptyDecl with params := [("x", .prim .int)], body :=
    [.assert (.binop .eqB (.unop .bnot (.name "x")) (.num 0))] }
#guard match assertionObligation lowerBodyLoops markerPre signedComplementC "f" false with
  | .error "operator ~ does not take int" => true | _ => false

-- Lexical preparation must retain invalid same-scope duplicates as refusals.
private def duplicateC : Contract := exampleContract
  { emptyDecl with body := [.decl (.named "uint") "x" (some (.num 1)),
      .decl (.named "uint") "x" (some (.num 2))] }
#guard match assertionObligation lowerBodyLoops markerPre duplicateC "f" false with
  | .error "x is already declared, or names a state variable" => true | _ => false
private def paramCollisionC : Contract := exampleContract
  { emptyDecl with params := [("x", .prim .uint)], body := [.decl (.named "uint") "x" none] }
#guard match assertionObligation lowerBodyLoops markerPre paramCollisionC "f" false with
  | .error "x is already declared, or names a state variable" => true | _ => false
private def unusedCaptureParamC : Contract := exampleContract
  { emptyDecl with params := [("se1", .prim .uint)], body := [.decl (.named "uint") "x" none] }
#guard match assertionObligation lowerBodyLoops markerPre unusedCaptureParamC "f" false with
  | .ok _ => true | _ => false
private def reservedStateC : Contract :=
  { vars := [("se1", .prim .uint)], funs := [("f", { emptyDecl with body := [.decl (.named "uint") "x" none] })] }
#guard match assertionObligation lowerBodyLoops markerPre reservedStateC "f" false with
  | .ok _ => true | _ => false
-- A UInt quantifier must not capture the freshly renamed Boolean local.
private def quantifiedCaptureC : Contract := exampleContract
  { emptyDecl with body := [.decl (.named "bool") "x" (some (.bool true)),
      .whileLoop { qinv := [.all .uint "se1" (.expr (.name "x"))] } (.bool false) []] }
#guard match assertionObligation lowerBodyLoops markerPre quantifiedCaptureC "f" true with
  | .ok _ => true | _ => false
