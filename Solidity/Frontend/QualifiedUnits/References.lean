import Solidity.Frontend.QualifiedUnits.Checked

/-! Structural reference coverage over existing intrinsic syntax. -/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source

/-- Identifier/member expression syntax as an existing path. -/
def expressionPath : Syn .expr → Option IdPath
  | .ident name => some ⟨name, []⟩
  | .member receiver name => (expressionPath receiver).map fun p => ⟨p.head, p.tail ++ [name]⟩
  | _ => none

/-- Explicit paths, identifiers and member prefixes. Runtime fields of
non-path receivers remain with G13; their ordinary subterms are traversed. -/
def references : {c : Cat} → Syn c → List IdPath
  | _, .nil => []
  | _, .cons a0 a1 => (references a0) ++ (references a1)
  | _, .none => []
  | _, .some a0 => (references a0)
  | _, .unit a0 => (references a0)
  | _, .pragma _ => []
  | _, .importPath _ _ => []
  | _, .importSymbols a0 a1 _ => (references a0) ++ (references a1)
  | _, .importStar _ _ => []
  | _, .importAlias _ _ => []
  | _, .contract _ _ a2 a3 a4 => (references a2) ++ (references a3) ++ (references a4)
  | _, .interface _ a1 a2 => (references a1) ++ (references a2)
  | _, .library _ a1 => (references a1)
  | _, .topPart a0 => (references a0)
  | _, .inherit a0 a1 => [a0] ++ (references a1)
  | _, .constructor a0 a1 _ _ a4 => (references a0) ++ (references a1) ++ (references a4)
  | _, .function _ a1 _ _ a4 _ a6 a7 a8 => a6.getD [] ++ (references a1) ++ (references a4) ++ (references a7) ++ (references a8)
  | _, .modifier _ a1 _ a3 a4 => a3.getD [] ++ (references a1) ++ (references a4)
  | _, .fallback a0 _ _ a3 _ a5 a6 => a5.getD [] ++ (references a0) ++ (references a3) ++ (references a6)
  | _, .fbNoParams => []
  | _, .fbParams a0 a1 a2 => (references a0) ++ (references a1) ++ (references a2)
  | _, .receive _ _ a2 _ a4 a5 => a4.getD [] ++ (references a2) ++ (references a5)
  | _, .struct _ a1 a2 => (references a1) ++ (references a2)
  | _, .structMember a0 _ => (references a0)
  | _, .enum _ _ _ => []
  | _, .udvt _ _ => []
  | _, .stateVar a0 _ _ a3 _ _ a6 => a3.getD [] ++ (references a0) ++ (references a6)
  | _, .constant a0 _ a2 => (references a0) ++ (references a2)
  | _, .event _ a1 _ => (references a1)
  | _, .eventParam a0 _ _ => (references a0)
  | _, .error _ a1 => (references a1)
  | _, .errorParam a0 _ => (references a0)
  | _, .usingPart a0 => (references a0)
  | _, .usingPath a0 a1 _ => [a0] ++ (references a1)
  | _, .usingAliases a0 a1 a2 _ => (references a0) ++ (references a1) ++ (references a2)
  | _, .usingAlias a0 _ => [a0]
  | _, .positional a0 => (references a0)
  | _, .named a0 => (references a0)
  | _, .namedArg _ a1 => (references a1)
  | _, .modInv a0 a1 => [a0] ++ (references a1)
  | _, .param a0 _ _ => (references a0)
  | _, .elem _ => []
  | _, .fnType a0 _ _ a3 => (references a0) ++ (references a3)
  | _, .mapping a0 _ a2 _ => MapKey.paths a0 ++ (references a2)
  | _, .userType a0 => [a0]
  | _, .array a0 a1 => (references a0) ++ (references a1)
  | _, .varDecl a0 _ _ => (references a0)
  | _, .index a0 a1 => (references a0) ++ (references a1)
  | _, .slice a0 a1 a2 => (references a0) ++ (references a1) ++ (references a2)
  | _, .member a0 a1 => (expressionPath (.member a0 a1)).toList ++ (references a0)
  | _, .callOptions a0 a1 a2 => (references a0) ++ (references a1) ++ (references a2)
  | _, .call a0 a1 => (references a0) ++ (references a1)
  | _, .payableConv a0 => (references a0)
  | _, .metaType a0 => (references a0)
  | _, .unaryPrefix _ a1 => (references a1)
  | _, .unarySuffix _ a1 => (references a1)
  | _, .exp a0 a1 => (references a0) ++ (references a1)
  | _, .mulDivMod _ a1 a2 => (references a1) ++ (references a2)
  | _, .addSub _ a1 a2 => (references a1) ++ (references a2)
  | _, .shift _ a1 a2 => (references a1) ++ (references a2)
  | _, .bitAnd a0 a1 => (references a0) ++ (references a1)
  | _, .bitXor a0 a1 => (references a0) ++ (references a1)
  | _, .bitOr a0 a1 => (references a0) ++ (references a1)
  | _, .order _ a1 a2 => (references a1) ++ (references a2)
  | _, .equality _ a1 a2 => (references a1) ++ (references a2)
  | _, .and a0 a1 => (references a0) ++ (references a1)
  | _, .or a0 a1 => (references a0) ++ (references a1)
  | _, .cond a0 a1 a2 => (references a0) ++ (references a1) ++ (references a2)
  | _, .assign _ a1 a2 => (references a1) ++ (references a2)
  | _, .new a0 => (references a0)
  | _, .tuple a0 a1 => (references a0) ++ (references a1)
  | _, .inlineArray a0 a1 => (references a0) ++ (references a1)
  | _, .ident a0 => [⟨a0, []⟩]
  | _, .lit _ => []
  | _, .litUnit _ _ => []
  | _, .elemType _ _ => []
  | _, .declVar a0 a1 => (references a0) ++ (references a1)
  | _, .declTuple _ a1 a2 a3 => (references a1) ++ (references a2) ++ (references a3)
  | _, .exprStmt a0 => (references a0)
  | _, .blockStmt a0 => (references a0)
  | _, .simpleStmt a0 => (references a0)
  | _, .ifStmt a0 a1 a2 => (references a0) ++ (references a1) ++ (references a2)
  | _, .forStmt a0 a1 a2 a3 => (references a0) ++ (references a1) ++ (references a2) ++ (references a3)
  | _, .whileStmt a0 a1 => (references a0) ++ (references a1)
  | _, .doWhile a0 a1 => (references a0) ++ (references a1)
  | _, .continueStmt => []
  | _, .breakStmt => []
  | _, .tryStmt a0 a1 a2 a3 a4 => (references a0) ++ (references a1) ++ (references a2) ++ (references a3) ++ (references a4)
  | _, .catchPlain a0 => (references a0)
  | _, .catchSig _ a1 a2 a3 => (references a1) ++ (references a2) ++ (references a3)
  | _, .returnStmt a0 => (references a0)
  | _, .emit a0 a1 => (references a0) ++ (references a1)
  | _, .revert a0 a1 => (references a0) ++ (references a1)
  | _, .assembly _ _ a2 => (references a2)
  | _, .block a0 => (references a0)
  | _, .stmtItem a0 => (references a0)
  | _, .uncheckedItem a0 => (references a0)
  | _, .yulBlock a0 => (references a0)
  | _, .yulLet _ _ a2 => (references a2)
  | _, .yulAssign _ _ a2 => (references a2)
  | _, .yulExprStmt a0 => (references a0)
  | _, .yulIf a0 a1 => (references a0) ++ (references a1)
  | _, .yulFor a0 a1 a2 a3 => (references a0) ++ (references a1) ++ (references a2) ++ (references a3)
  | _, .yulSwitch a0 a1 a2 => (references a0) ++ (references a1) ++ (references a2)
  | _, .yulCase _ a1 => (references a1)
  | _, .yulLeave => []
  | _, .yulBreak => []
  | _, .yulContinue => []
  | _, .yulFun _ _ _ a3 => (references a3)
  | _, .yulPath _ _ => []
  | _, .yulCall _ a1 => (references a1)
  | _, .yulLit _ => []

end Solidity.Frontend.QualifiedUnits
