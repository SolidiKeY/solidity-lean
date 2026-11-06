import Solidity.Source.Ctor
import Solidity.Frontend.StatementGrammarH28.G0List

/-! Gate G0 twins of the profile observation `Syn.rejections`
(`Source/Ctor.lean`), which the fixture controls evaluate by `decide +kernel`:
`Syn.nodes`, `Syn.excl`, `Syn.placeholders` and `isLiteralBase` match on the
indexed family. Their twins read syntax only through `Syn.casesOn` with
category-generalising motives and structural recursion;
`match` remains only on the parameter-free `Option`, `List`, `Prod`, `Lit`,
`YulLit`, `ShiftOp`, `AssignOp` and `Denom`. The twins are linked to their
Source counterparts (`…_eq`; the views `identAt`/`litAt` and the Yul views
only through them), and `g0Rejections_eq` links the whole.

`g0IsRethrow` is the twin of Source's `isRethrow` (an indexed `match` with
string-literal patterns, for which Lean 4.24 generates no equation lemmas).
It inspects the tree in the matcher's own preorder, so `g0IsRethrow_eq` is
proved by case analysis in that order: a mismatched constructor reduces both
sides, and a failed string or number test is discharged by unfolding the
matcher (`delta`) and rewriting its `dite` with the negated test. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

private def optValueResult : Cat → Type
  | .opt c => Option (Syn c)
  | _ => PUnit

private def optValueAt {category : Cat} (tree : Syn category) : optValueResult category := by
  apply Syn.casesOn (motive := fun category _ => optValueResult category) tree
  case none => intro category; exact Option.none
  case some => intro category x; exact Option.some x
  all_goals intros; exact PUnit.unit

/-- The value of an optional syntax tree. -/
def g0OptValue {c : Cat} (o : Syn (.opt c)) : Option (Syn c) := optValueAt o

private def identAt {category : Cat} (tree : Syn category) : Option String := by
  apply Syn.casesOn (motive := fun _ _ => Option String) tree
  case ident => intro name; exact Option.some name
  all_goals intros; exact Option.none

private def litAt {category : Cat} (tree : Syn category) : Option Lit := by
  apply Syn.casesOn (motive := fun _ _ => Option Lit) tree
  case lit => intro l; exact Option.some l
  all_goals intros; exact Option.none

private def listViewResult : Cat → Type
  | .list c => Option (Syn c × Syn (.list c))
  | _ => PUnit

private def listViewAt {category : Cat} (tree : Syn category) : listViewResult category := by
  apply Syn.casesOn (motive := fun category _ => listViewResult category) tree
  case nil => intro category; exact Option.none
  case cons => intro category x xs; exact Option.some (x, xs)
  all_goals intros; exact PUnit.unit

def g0ListView {c : Cat} (xs : Syn (.list c)) : Option (Syn c × Syn (.list c)) := listViewAt xs

private def yulExprStmtAt {category : Cat} (tree : Syn category) : Option (Syn .yulExpr) := by
  apply Syn.casesOn (motive := fun _ _ => Option (Syn .yulExpr)) tree
  case yulExprStmt => intro e; exact Option.some e
  all_goals intros; exact Option.none

private def yulCallAt {category : Cat} (tree : Syn category) :
    Option (String × Syn (.list .yulExpr)) := by
  apply Syn.casesOn (motive := fun _ _ => Option (String × Syn (.list .yulExpr))) tree
  case yulCall => intro fn args; exact Option.some (fn, args)
  all_goals intros; exact Option.none

private def yulPathAt {category : Cat} (tree : Syn category) : Option (String × List String) := by
  apply Syn.casesOn (motive := fun _ _ => Option (String × List String)) tree
  case yulPath => intro head tail; exact Option.some (head, tail)
  all_goals intros; exact Option.none

private def yulLitAt {category : Cat} (tree : Syn category) : Option YulLit := by
  apply Syn.casesOn (motive := fun _ _ => Option YulLit) tree
  case yulLit => intro l; exact Option.some l
  all_goals intros; exact Option.none

/-- `isRethrow` through the eliminator views, inspecting the tree in the
same preorder as the Source matcher. -/
def g0IsRethrow (b : Syn (.list .yulStmt)) : Bool :=
  match g0ListView b with
  | Option.none => false
  | Option.some (x, rest) =>
  match yulExprStmtAt x with
  | Option.none => false
  | Option.some e =>
  match yulCallAt e with
  | Option.none => false
  | Option.some (fn, args) =>
  if fn = "revert" then
  match g0ListView args with
  | Option.none => false
  | Option.some (a1, r1) =>
  match yulCallAt a1 with
  | Option.none => false
  | Option.some (g, gargs) =>
  if g = "add" then
  match g0ListView gargs with
  | Option.none => false
  | Option.some (p, r3) =>
  match yulPathAt p with
  | Option.some (d, []) =>
    match g0ListView r3 with
    | Option.none => false
    | Option.some (l, r4) =>
    match yulLitAt l with
    | Option.some (.dec n) =>
      if n = 32 then
      match g0ListView r4 with
      | Option.some _ => false
      | Option.none =>
      match g0ListView r1 with
      | Option.none => false
      | Option.some (a2, r2) =>
      match yulCallAt a2 with
      | Option.none => false
      | Option.some (m, margs) =>
      if m = "mload" then
      match g0ListView margs with
      | Option.none => false
      | Option.some (q, r5) =>
      match yulPathAt q with
      | Option.some (d', []) =>
        match g0ListView r5, g0ListView r2, g0ListView rest with
        | Option.none, Option.none, Option.none => d == d'
        | _, _, _ => false
      | _ => false
      else false
      else false
    | _ => false
  | _ => false
  else false
  else false

local macro "rethrow_neg" h:ident : tactic => `(tactic|
  (delta isRethrow isRethrow.match_1
   simp only [g0IsRethrow, g0ListView, listViewAt, yulExprStmtAt, yulCallAt, yulPathAt,
     yulLitAt, dif_neg $h:ident, if_neg $h:ident] <;> rfl))

theorem g0IsRethrow_eq (b : Syn (.list .yulStmt)) : g0IsRethrow b = isRethrow b := by
  cases b
  · rfl
  rename_i x rest
  cases x <;> try rfl
  rename_i e
  cases e <;> try rfl
  rename_i fn args
  by_cases h1 : fn = "revert"
  case neg => rethrow_neg h1
  subst h1
  cases args <;> try rfl
  rename_i a1 r1
  cases a1 <;> try rfl
  rename_i g gargs
  by_cases h2 : g = "add"
  case neg => rethrow_neg h2
  subst h2
  cases gargs <;> try rfl
  rename_i p r3
  cases p <;> try rfl
  rename_i d tl
  cases tl <;> try rfl
  cases r3 <;> try rfl
  rename_i l r4
  cases l <;> try rfl
  rename_i lit
  cases lit <;> try rfl
  rename_i n
  by_cases h3 : n = 32
  case neg => rethrow_neg h3
  subst h3
  cases r4 <;> try rfl
  cases r1 <;> try rfl
  rename_i a2 r2
  cases a2 <;> try rfl
  rename_i m margs
  by_cases h4 : m = "mload"
  case neg => rethrow_neg h4
  subst h4
  cases margs <;> try rfl
  rename_i q r5
  cases q <;> try rfl
  rename_i d' tl'
  cases tl' <;> try rfl
  cases r5 <;> try rfl
  cases r2 <;> try rfl
  cases rest <;> try rfl
  done

/-- `isLiteralBase` through the literal view. -/
def g0IsLiteralBase (b : Syn .expr) : Bool :=
  match litAt b with
  | Option.some (.num _) => true
  | _ => false

private def placeholdersAt {category : Cat} (tree : Syn category) : Nat := by
  apply Syn.casesOn (motive := fun _ _ => Nat) tree
  case nil => intros; exact 0
  case cons =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case none => intros; exact 0
  case some =>
    intros; rename_i s0
    exact placeholdersAt s0
  case unit =>
    intros; rename_i s0
    exact placeholdersAt s0
  case pragma => intros; exact 0
  case importPath => intros; exact 0
  case importSymbols =>
    intros; rename_i s0 s1 _
    exact placeholdersAt s0 + placeholdersAt s1
  case importStar => intros; exact 0
  case importAlias => intros; exact 0
  case contract =>
    intros; rename_i _ _ s2 s3 s4
    exact placeholdersAt s2 + placeholdersAt s3 + placeholdersAt s4
  case interface =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case library =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case topPart =>
    intros; rename_i s0
    exact placeholdersAt s0
  case inherit =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case constructor =>
    intros; rename_i s0 s1 _ _ s4
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s4
  case function =>
    intros; rename_i _ s1 _ _ s4 _ _ s7 s8
    exact placeholdersAt s1 + placeholdersAt s4 + placeholdersAt s7 + placeholdersAt s8
  case modifier =>
    intros; rename_i _ s1 _ _ s4
    exact placeholdersAt s1 + placeholdersAt s4
  case fallback =>
    intros; rename_i s0 _ _ s3 _ _ s6
    exact placeholdersAt s0 + placeholdersAt s3 + placeholdersAt s6
  case fbNoParams => intros; exact 0
  case fbParams =>
    intros; rename_i s0 s1 s2
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2
  case receive =>
    intros; rename_i _ _ s2 _ _ s5
    exact placeholdersAt s2 + placeholdersAt s5
  case struct =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case structMember =>
    intros; rename_i s0 _
    exact placeholdersAt s0
  case enum => intros; exact 0
  case udvt => intros; exact 0
  case stateVar =>
    intros; rename_i s0 _ _ _ _ _ s6
    exact placeholdersAt s0 + placeholdersAt s6
  case constant =>
    intros; rename_i s0 _ s2
    exact placeholdersAt s0 + placeholdersAt s2
  case event =>
    intros; rename_i _ s1 _
    exact placeholdersAt s1
  case eventParam =>
    intros; rename_i s0 _ _
    exact placeholdersAt s0
  case error =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case errorParam =>
    intros; rename_i s0 _
    exact placeholdersAt s0
  case usingPart =>
    intros; rename_i s0
    exact placeholdersAt s0
  case usingPath =>
    intros; rename_i _ s1 _
    exact placeholdersAt s1
  case usingAliases =>
    intros; rename_i s0 s1 s2 _
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2
  case usingAlias => intros; exact 0
  case positional =>
    intros; rename_i s0
    exact placeholdersAt s0
  case named =>
    intros; rename_i s0
    exact placeholdersAt s0
  case namedArg =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case modInv =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case param =>
    intros; rename_i s0 _ _
    exact placeholdersAt s0
  case elem => intros; exact 0
  case fnType =>
    intros; rename_i s0 _ _ s3
    exact placeholdersAt s0 + placeholdersAt s3
  case mapping =>
    intros; rename_i _ _ s2 _
    exact placeholdersAt s2
  case userType => intros; exact 0
  case array =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case varDecl =>
    intros; rename_i s0 _ _
    exact placeholdersAt s0
  case index =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case slice =>
    intros; rename_i s0 s1 s2
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2
  case member =>
    intros; rename_i s0 _
    exact placeholdersAt s0
  case callOptions =>
    intros; rename_i s0 s1 s2
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2
  case call =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case payableConv =>
    intros; rename_i s0
    exact placeholdersAt s0
  case metaType =>
    intros; rename_i s0
    exact placeholdersAt s0
  case unaryPrefix =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case unarySuffix =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case exp =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case mulDivMod =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case addSub =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case shift =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case bitAnd =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case bitXor =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case bitOr =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case order =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case equality =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case and =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case or =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case cond =>
    intros; rename_i s0 s1 s2
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2
  case assign =>
    intros; rename_i _ s1 s2
    exact placeholdersAt s1 + placeholdersAt s2
  case new =>
    intros; rename_i s0
    exact placeholdersAt s0
  case tuple =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case inlineArray =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case ident => intros; exact 0
  case lit => intros; exact 0
  case litUnit => intros; exact 0
  case elemType => intros; exact 0
  case declVar =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case declTuple =>
    intros; rename_i _ s1 s2 s3
    exact placeholdersAt s1 + placeholdersAt s2 + placeholdersAt s3
  case exprStmt =>
    intros; rename_i s0
    exact if identAt s0 == some "_" then 1 else placeholdersAt s0
  case blockStmt =>
    intros; rename_i s0
    exact placeholdersAt s0
  case simpleStmt =>
    intros; rename_i s0
    exact placeholdersAt s0
  case ifStmt =>
    intros; rename_i s0 s1 s2
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2
  case forStmt =>
    intros; rename_i s0 s1 s2 s3
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2 + placeholdersAt s3
  case whileStmt =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case doWhile =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case continueStmt => intros; exact 0
  case breakStmt => intros; exact 0
  case tryStmt =>
    intros; rename_i s0 s1 s2 s3 s4
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2 + placeholdersAt s3 + placeholdersAt s4
  case catchPlain =>
    intros; rename_i s0
    exact placeholdersAt s0
  case catchSig =>
    intros; rename_i _ s1 s2 s3
    exact placeholdersAt s1 + placeholdersAt s2 + placeholdersAt s3
  case returnStmt =>
    intros; rename_i s0
    exact placeholdersAt s0
  case emit =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case revert =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case assembly =>
    intros; rename_i _ _ s2
    exact placeholdersAt s2
  case block =>
    intros; rename_i s0
    exact placeholdersAt s0
  case stmtItem =>
    intros; rename_i s0
    exact placeholdersAt s0
  case uncheckedItem =>
    intros; rename_i s0
    exact placeholdersAt s0
  case yulBlock =>
    intros; rename_i s0
    exact placeholdersAt s0
  case yulLet =>
    intros; rename_i _ _ s2
    exact placeholdersAt s2
  case yulAssign =>
    intros; rename_i _ _ s2
    exact placeholdersAt s2
  case yulExprStmt =>
    intros; rename_i s0
    exact placeholdersAt s0
  case yulIf =>
    intros; rename_i s0 s1
    exact placeholdersAt s0 + placeholdersAt s1
  case yulFor =>
    intros; rename_i s0 s1 s2 s3
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2 + placeholdersAt s3
  case yulSwitch =>
    intros; rename_i s0 s1 s2
    exact placeholdersAt s0 + placeholdersAt s1 + placeholdersAt s2
  case yulCase =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case yulLeave => intros; exact 0
  case yulBreak => intros; exact 0
  case yulContinue => intros; exact 0
  case yulFun =>
    intros; rename_i _ _ _ s3
    exact placeholdersAt s3
  case yulPath => intros; exact 0
  case yulCall =>
    intros; rename_i _ s1
    exact placeholdersAt s1
  case yulLit => intros; exact 0
termination_by structural tree

/-- `Syn.placeholders` by the eliminator. -/
def g0Placeholders {c : Cat} (s : Syn c) : Nat := placeholdersAt s

private def nodesAt {category : Cat} (tree : Syn category) : List Node := by
  apply Syn.casesOn (motive := fun _ _ => List Node) tree
  case nil => intros; exact ⟨Ctor.nil, Option.none⟩ :: []
  case cons =>
    intros; rename_i s0 s1
    exact ⟨Ctor.cons, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case none => intros; exact ⟨Ctor.none, Option.none⟩ :: []
  case some =>
    intros; rename_i s0
    exact ⟨Ctor.some, Option.none⟩ :: (nodesAt s0)
  case unit =>
    intros; rename_i s0
    exact ⟨Ctor.unit, Option.none⟩ :: (nodesAt s0)
  case pragma =>
    intros; rename_i f0
    exact ⟨Ctor.pragma, (if f0 == ["experimental", "solidity"] then Option.some .removedGenericSolidity
      else Option.none)⟩ :: []
  case importPath =>
    intros; rename_i _ _
    exact ⟨Ctor.importPath, Option.none⟩ :: []
  case importSymbols =>
    intros; rename_i s0 s1 _
    exact ⟨Ctor.importSymbols, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case importStar =>
    intros; rename_i _ _
    exact ⟨Ctor.importStar, Option.none⟩ :: []
  case importAlias =>
    intros; rename_i _ _
    exact ⟨Ctor.importAlias, Option.none⟩ :: []
  case contract =>
    intros; rename_i f0 f1 s2 s3 s4
    exact ⟨Ctor.contract, (match g0OptValue s2 with
      | Option.some b => if g0IsLiteralBase b then Option.none else Option.some .storageLayout
      | Option.none => Option.none)⟩ :: (nodesAt s2 ++ nodesAt s3 ++ nodesAt s4)
  case interface =>
    intros; rename_i _ s1 s2
    exact ⟨Ctor.interface, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2)
  case library =>
    intros; rename_i _ s1
    exact ⟨Ctor.library, Option.none⟩ :: (nodesAt s1)
  case topPart =>
    intros; rename_i s0
    exact ⟨Ctor.topPart, Option.none⟩ :: (nodesAt s0)
  case inherit =>
    intros; rename_i _ s1
    exact ⟨Ctor.inherit, Option.none⟩ :: (nodesAt s1)
  case constructor =>
    intros; rename_i s0 s1 _ _ s4
    exact ⟨Ctor.constructor, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s4)
  case function =>
    intros; rename_i _ s1 _ _ s4 _ _ s7 s8
    exact ⟨Ctor.function, Option.none⟩ :: (nodesAt s1 ++ nodesAt s4 ++ nodesAt s7 ++ nodesAt s8)
  case modifier =>
    intros; rename_i f0 s1 f2 f3 s4
    exact ⟨Ctor.modifier, (match g0OptValue s4 with
      | Option.some b => if placeholdersAt b == 0 then Option.some .invalidModifierBody else Option.none
      | Option.none => Option.none)⟩ :: (nodesAt s1 ++ nodesAt s4)
  case fallback =>
    intros; rename_i s0 _ _ s3 _ _ s6
    exact ⟨Ctor.fallback, Option.none⟩ :: (nodesAt s0 ++ nodesAt s3 ++ nodesAt s6)
  case fbNoParams => intros; exact ⟨Ctor.fbNoParams, Option.none⟩ :: []
  case fbParams =>
    intros; rename_i s0 s1 s2
    exact ⟨Ctor.fbParams, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2)
  case receive =>
    intros; rename_i _ _ s2 _ _ s5
    exact ⟨Ctor.receive, Option.none⟩ :: (nodesAt s2 ++ nodesAt s5)
  case struct =>
    intros; rename_i _ s1 s2
    exact ⟨Ctor.struct, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2)
  case structMember =>
    intros; rename_i s0 _
    exact ⟨Ctor.structMember, Option.none⟩ :: (nodesAt s0)
  case enum =>
    intros; rename_i _ _ _
    exact ⟨Ctor.enum, Option.none⟩ :: []
  case udvt =>
    intros; rename_i _ _
    exact ⟨Ctor.udvt, Option.none⟩ :: []
  case stateVar =>
    intros; rename_i s0 _ _ _ _ _ s6
    exact ⟨Ctor.stateVar, Option.none⟩ :: (nodesAt s0 ++ nodesAt s6)
  case constant =>
    intros; rename_i s0 _ s2
    exact ⟨Ctor.constant, Option.none⟩ :: (nodesAt s0 ++ nodesAt s2)
  case event =>
    intros; rename_i _ s1 _
    exact ⟨Ctor.event, Option.none⟩ :: (nodesAt s1)
  case eventParam =>
    intros; rename_i s0 _ _
    exact ⟨Ctor.eventParam, Option.none⟩ :: (nodesAt s0)
  case error =>
    intros; rename_i _ s1
    exact ⟨Ctor.error, Option.none⟩ :: (nodesAt s1)
  case errorParam =>
    intros; rename_i s0 _
    exact ⟨Ctor.errorParam, Option.none⟩ :: (nodesAt s0)
  case usingPart =>
    intros; rename_i s0
    exact ⟨Ctor.usingPart, Option.none⟩ :: (nodesAt s0)
  case usingPath =>
    intros; rename_i _ s1 _
    exact ⟨Ctor.usingPath, Option.none⟩ :: (nodesAt s1)
  case usingAliases =>
    intros; rename_i s0 s1 s2 _
    exact ⟨Ctor.usingAliases, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2)
  case usingAlias =>
    intros; rename_i _ _
    exact ⟨Ctor.usingAlias, Option.none⟩ :: []
  case positional =>
    intros; rename_i s0
    exact ⟨Ctor.positional, Option.none⟩ :: (nodesAt s0)
  case named =>
    intros; rename_i s0
    exact ⟨Ctor.named, Option.none⟩ :: (nodesAt s0)
  case namedArg =>
    intros; rename_i _ s1
    exact ⟨Ctor.namedArg, Option.none⟩ :: (nodesAt s1)
  case modInv =>
    intros; rename_i _ s1
    exact ⟨Ctor.modInv, Option.none⟩ :: (nodesAt s1)
  case param =>
    intros; rename_i s0 _ _
    exact ⟨Ctor.param, Option.none⟩ :: (nodesAt s0)
  case elem =>
    intros; rename_i _
    exact ⟨Ctor.elem, Option.none⟩ :: []
  case fnType =>
    intros; rename_i s0 _ _ s3
    exact ⟨Ctor.fnType, Option.none⟩ :: (nodesAt s0 ++ nodesAt s3)
  case mapping =>
    intros; rename_i _ _ s2 _
    exact ⟨Ctor.mapping, Option.none⟩ :: (nodesAt s2)
  case userType =>
    intros; rename_i _
    exact ⟨Ctor.userType, Option.none⟩ :: []
  case array =>
    intros; rename_i s0 s1
    exact ⟨Ctor.array, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case varDecl =>
    intros; rename_i s0 _ _
    exact ⟨Ctor.varDecl, Option.none⟩ :: (nodesAt s0)
  case index =>
    intros; rename_i s0 s1
    exact ⟨Ctor.index, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case slice =>
    intros; rename_i s0 s1 s2
    exact ⟨Ctor.slice, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2)
  case member =>
    intros; rename_i s0 _
    exact ⟨Ctor.member, Option.none⟩ :: (nodesAt s0)
  case callOptions =>
    intros; rename_i s0 s1 s2
    exact ⟨Ctor.callOptions, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2)
  case call =>
    intros; rename_i s0 s1
    exact ⟨Ctor.call, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case payableConv =>
    intros; rename_i s0
    exact ⟨Ctor.payableConv, Option.none⟩ :: (nodesAt s0)
  case metaType =>
    intros; rename_i s0
    exact ⟨Ctor.metaType, Option.none⟩ :: (nodesAt s0)
  case unaryPrefix =>
    intros; rename_i _ s1
    exact ⟨Ctor.unaryPrefix, Option.none⟩ :: (nodesAt s1)
  case unarySuffix =>
    intros; rename_i _ s1
    exact ⟨Ctor.unarySuffix, Option.none⟩ :: (nodesAt s1)
  case exp =>
    intros; rename_i s0 s1
    exact ⟨Ctor.exp, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case mulDivMod =>
    intros; rename_i _ s1 s2
    exact ⟨Ctor.mulDivMod, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2)
  case addSub =>
    intros; rename_i _ s1 s2
    exact ⟨Ctor.addSub, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2)
  case shift =>
    intros; rename_i f0 s1 s2
    exact ⟨Ctor.shift, (match f0 with | .shr => Option.some .unsignedRightShift | _ => Option.none)⟩ :: (nodesAt s1 ++ nodesAt s2)
  case bitAnd =>
    intros; rename_i s0 s1
    exact ⟨Ctor.bitAnd, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case bitXor =>
    intros; rename_i s0 s1
    exact ⟨Ctor.bitXor, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case bitOr =>
    intros; rename_i s0 s1
    exact ⟨Ctor.bitOr, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case order =>
    intros; rename_i _ s1 s2
    exact ⟨Ctor.order, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2)
  case equality =>
    intros; rename_i _ s1 s2
    exact ⟨Ctor.equality, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2)
  case and =>
    intros; rename_i s0 s1
    exact ⟨Ctor.and, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case or =>
    intros; rename_i s0 s1
    exact ⟨Ctor.or, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case cond =>
    intros; rename_i s0 s1 s2
    exact ⟨Ctor.cond, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2)
  case assign =>
    intros; rename_i f0 s1 s2
    exact ⟨Ctor.assign, (match f0 with | .shr => Option.some .unsignedRightShift | _ => Option.none)⟩ :: (nodesAt s1 ++ nodesAt s2)
  case new =>
    intros; rename_i s0
    exact ⟨Ctor.new, Option.none⟩ :: (nodesAt s0)
  case tuple =>
    intros; rename_i s0 s1
    exact ⟨Ctor.tuple, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case inlineArray =>
    intros; rename_i s0 s1
    exact ⟨Ctor.inlineArray, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case ident =>
    intros; rename_i _
    exact ⟨Ctor.ident, Option.none⟩ :: []
  case lit =>
    intros; rename_i _
    exact ⟨Ctor.lit, Option.none⟩ :: []
  case litUnit =>
    intros; rename_i f0 f1
    exact ⟨Ctor.litUnit, (match f1 with | .years => Option.some .removedUnits | _ => Option.none)⟩ :: []
  case elemType =>
    intros; rename_i _ _
    exact ⟨Ctor.elemType, Option.none⟩ :: []
  case declVar =>
    intros; rename_i s0 s1
    exact ⟨Ctor.declVar, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case declTuple =>
    intros; rename_i _ s1 s2 s3
    exact ⟨Ctor.declTuple, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2 ++ nodesAt s3)
  case exprStmt =>
    intros; rename_i s0
    exact ⟨Ctor.exprStmt, Option.none⟩ :: (nodesAt s0)
  case blockStmt =>
    intros; rename_i s0
    exact ⟨Ctor.blockStmt, Option.none⟩ :: (nodesAt s0)
  case simpleStmt =>
    intros; rename_i s0
    exact ⟨Ctor.simpleStmt, Option.none⟩ :: (nodesAt s0)
  case ifStmt =>
    intros; rename_i s0 s1 s2
    exact ⟨Ctor.ifStmt, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2)
  case forStmt =>
    intros; rename_i s0 s1 s2 s3
    exact ⟨Ctor.forStmt, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2 ++ nodesAt s3)
  case whileStmt =>
    intros; rename_i s0 s1
    exact ⟨Ctor.whileStmt, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case doWhile =>
    intros; rename_i s0 s1
    exact ⟨Ctor.doWhile, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case continueStmt => intros; exact ⟨Ctor.continueStmt, Option.none⟩ :: []
  case breakStmt => intros; exact ⟨Ctor.breakStmt, Option.none⟩ :: []
  case tryStmt =>
    intros; rename_i s0 s1 s2 s3 s4
    exact ⟨Ctor.tryStmt, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2 ++ nodesAt s3 ++ nodesAt s4)
  case catchPlain =>
    intros; rename_i s0
    exact ⟨Ctor.catchPlain, Option.none⟩ :: (nodesAt s0)
  case catchSig =>
    intros; rename_i _ s1 s2 s3
    exact ⟨Ctor.catchSig, Option.none⟩ :: (nodesAt s1 ++ nodesAt s2 ++ nodesAt s3)
  case returnStmt =>
    intros; rename_i s0
    exact ⟨Ctor.returnStmt, Option.none⟩ :: (nodesAt s0)
  case emit =>
    intros; rename_i s0 s1
    exact ⟨Ctor.emit, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case revert =>
    intros; rename_i s0 s1
    exact ⟨Ctor.revert, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case assembly =>
    intros; rename_i f0 f1 s2
    exact ⟨Ctor.assembly, if g0IsRethrow s2 then Option.none else Option.some .inlineAssembly⟩ :: (nodesAt s2)
  case block =>
    intros; rename_i s0
    exact ⟨Ctor.block, Option.none⟩ :: (nodesAt s0)
  case stmtItem =>
    intros; rename_i s0
    exact ⟨Ctor.stmtItem, Option.none⟩ :: (nodesAt s0)
  case uncheckedItem =>
    intros; rename_i s0
    exact ⟨Ctor.uncheckedItem, (if placeholdersAt s0 == 0 then Option.none else Option.some .invalidModifierBody)⟩ :: (nodesAt s0)
  case yulBlock =>
    intros; rename_i s0
    exact ⟨Ctor.yulBlock, Option.none⟩ :: (nodesAt s0)
  case yulLet =>
    intros; rename_i _ _ s2
    exact ⟨Ctor.yulLet, Option.none⟩ :: (nodesAt s2)
  case yulAssign =>
    intros; rename_i _ _ s2
    exact ⟨Ctor.yulAssign, Option.none⟩ :: (nodesAt s2)
  case yulExprStmt =>
    intros; rename_i s0
    exact ⟨Ctor.yulExprStmt, Option.none⟩ :: (nodesAt s0)
  case yulIf =>
    intros; rename_i s0 s1
    exact ⟨Ctor.yulIf, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1)
  case yulFor =>
    intros; rename_i s0 s1 s2 s3
    exact ⟨Ctor.yulFor, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2 ++ nodesAt s3)
  case yulSwitch =>
    intros; rename_i s0 s1 s2
    exact ⟨Ctor.yulSwitch, Option.none⟩ :: (nodesAt s0 ++ nodesAt s1 ++ nodesAt s2)
  case yulCase =>
    intros; rename_i _ s1
    exact ⟨Ctor.yulCase, Option.none⟩ :: (nodesAt s1)
  case yulLeave => intros; exact ⟨Ctor.yulLeave, Option.none⟩ :: []
  case yulBreak => intros; exact ⟨Ctor.yulBreak, Option.none⟩ :: []
  case yulContinue => intros; exact ⟨Ctor.yulContinue, Option.none⟩ :: []
  case yulFun =>
    intros; rename_i _ _ _ s3
    exact ⟨Ctor.yulFun, Option.none⟩ :: (nodesAt s3)
  case yulPath =>
    intros; rename_i _ _
    exact ⟨Ctor.yulPath, Option.none⟩ :: []
  case yulCall =>
    intros; rename_i _ s1
    exact ⟨Ctor.yulCall, Option.none⟩ :: (nodesAt s1)
  case yulLit =>
    intros; rename_i _
    exact ⟨Ctor.yulLit, Option.none⟩ :: []
termination_by structural tree

/-- `Syn.nodes` with each node's exclusion, by the eliminator. -/
def g0Nodes {c : Cat} (s : Syn c) : List Node := nodesAt s

/-- `Syn.rejections` by the eliminator. -/
def g0Rejections {c : Cat} (s : Syn c) : List Excl := (g0Nodes s).filterMap Node.excl

theorem g0OptValue_none {c : Cat} : g0OptValue (Syn.none (c := c)) = Option.none := rfl

theorem g0OptValue_some {c : Cat} (x : Syn c) : g0OptValue (Syn.some x) = Option.some x := rfl

theorem g0IsLiteralBase_eq (b : Syn .expr) : g0IsLiteralBase b = isLiteralBase b := by
  cases b
  all_goals try rfl
  rename_i l
  cases l <;> rfl

theorem g0Placeholders_eq {c : Cat} (s : Syn c) : g0Placeholders s = s.placeholders := by
  suffices h : s.placeholders = placeholdersAt s from h.symm
  induction s
  case exprStmt e ih =>
    cases e
    case ident n =>
      by_cases hn : n = "_"
      · subst hn
        rfl
      · have hb : (Option.some n == Option.some "_") = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun h => hn (Option.some.inj h)
        have rhs : placeholdersAt (Syn.exprStmt (.ident n)) = 0 := by
          change (if Option.some n == Option.some "_" then 1 else 0) = 0
          rw [hb]
          rfl
        rw [rhs]
        simp only [Syn.ident.injEq, hn, imp_self, Syn.placeholders]
    all_goals exact ih
  all_goals first | rfl | (simp only [Syn.placeholders, *] <;> rfl)

private theorem excl_contract (abstract : Bool) (name : String) (layout : Syn (.opt .expr))
    (bases : Syn (.list .inherit)) (parts : Syn (.list (.part false))) :
    (Syn.contract abstract name layout bases parts).excl =
      (match g0OptValue layout with
        | Option.some b => if g0IsLiteralBase b then Option.none else Option.some .storageLayout
        | Option.none => Option.none) := by
  cases layout with
  | none => rfl
  | some b =>
    show _ = if g0IsLiteralBase b then Option.none else Option.some Excl.storageLayout
    rw [g0IsLiteralBase_eq]
    rfl

private theorem excl_modifier (name : String) (params : Syn (.opt (.list .param)))
    (virtual : Bool) (override : Option (List IdPath)) (body : Syn (.opt (.block .body))) :
    (Syn.modifier name params virtual override body).excl =
      (match g0OptValue body with
        | Option.some b => if g0Placeholders b == 0 then Option.some .invalidModifierBody
            else Option.none
        | Option.none => Option.none) := by
  cases body with
  | none => rfl
  | some b =>
    show _ = if g0Placeholders b == 0 then Option.some Excl.invalidModifierBody else Option.none
    rw [g0Placeholders_eq]
    rfl

private theorem excl_unchecked {l : Bool} (b : Syn (.block ⟨l, true⟩)) :
    (Syn.uncheckedItem b).excl =
      if g0Placeholders b == 0 then Option.none else Option.some .invalidModifierBody := by
  rw [g0Placeholders_eq]
  rfl

private theorem excl_assembly {k : SCtx} (evm : Bool) (flags : List String)
    (body : Syn (.list .yulStmt)) :
    (Syn.assembly (k := k) evm flags body).excl =
      if g0IsRethrow body then Option.none else Option.some .inlineAssembly := by
  rw [g0IsRethrow_eq]
  rfl

/-- The link of the node twin, exclusions included. -/
theorem g0Nodes_eq {c : Cat} (s : Syn c) : g0Nodes s = s.nodes := by
  suffices h : s.nodes = nodesAt s from h.symm
  induction s
  case shift op a b iha ihb =>
    cases op <;> (simp only [Syn.nodes, *]; rfl)
  case assign op a b iha ihb =>
    cases op <;> (simp only [Syn.nodes, *]; rfl)
  case litUnit n u =>
    cases u <;> rfl
  all_goals (simp only [Syn.nodes, Syn.node, excl_contract, excl_modifier,
    excl_unchecked, excl_assembly, *] <;> rfl)

/-- The link of the profile observation. -/
theorem g0Rejections_eq {c : Cat} (s : Syn c) : g0Rejections s = s.rejections := by
  simp only [g0Rejections, Syn.rejections, g0Nodes_eq]

#print axioms g0IsRethrow_eq
#print axioms g0IsLiteralBase_eq
#print axioms g0Placeholders_eq
#print axioms g0Nodes_eq
#print axioms g0Rejections_eq
end Solidity.Frontend.StatementGrammarH28
