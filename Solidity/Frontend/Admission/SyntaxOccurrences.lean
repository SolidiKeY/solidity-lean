import Solidity.Source.Ctor

/-! Typed syntax occurrence inventory. Categories/payloads are retained;
no executable syntax/state representation or feature policy is replaced. -/
namespace Solidity.Frontend.Admission
open Solidity.Source

abbrev SyntaxOccurrence := (c : Cat) × Syn c

/-- Proper descendants in preorder, all Syn-typed children, no fuel or truncation. -/
def syntaxDescendants {c : Cat} (s : Syn c) : List SyntaxOccurrence :=
  Syn.casesOn (motive := fun _ _ => List SyntaxOccurrence) s
    ([]) -- nil
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- cons
    ([]) -- none
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- some
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- unit
    (fun _ => []) -- pragma
    (fun _ _ => []) -- importPath
    (fun s0 s1 _ => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- importSymbols
    (fun _ _ => []) -- importStar
    (fun _ _ => []) -- importAlias
    (fun _ _ s2 s3 s4 => (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) -- contract
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- interface
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- library
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- topPart
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- inherit
    (fun s0 s1 _ _ s4 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) -- constructor
    (fun _ s1 _ _ s4 _ _ s7 s8 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4) ++ (⟨_, s7⟩ :: syntaxDescendants s7) ++ (⟨_, s8⟩ :: syntaxDescendants s8)) -- function
    (fun _ s1 _ _ s4 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) -- modifier
    (fun s0 _ _ s3 _ _ s6 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s6⟩ :: syntaxDescendants s6)) -- fallback
    ([]) -- fbNoParams
    (fun s0 s1 s2 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- fbParams
    (fun _ _ s2 _ _ s5 => (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s5⟩ :: syntaxDescendants s5)) -- receive
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- struct
    (fun s0 _ => (⟨_, s0⟩ :: syntaxDescendants s0)) -- structMember
    (fun _ _ _ => []) -- enum
    (fun _ _ => []) -- udvt
    (fun s0 _ _ _ _ _ s6 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s6⟩ :: syntaxDescendants s6)) -- stateVar
    (fun s0 _ s2 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- constant
    (fun _ s1 _ => (⟨_, s1⟩ :: syntaxDescendants s1)) -- event
    (fun s0 _ _ => (⟨_, s0⟩ :: syntaxDescendants s0)) -- eventParam
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- error
    (fun s0 _ => (⟨_, s0⟩ :: syntaxDescendants s0)) -- errorParam
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- usingPart
    (fun _ s1 _ => (⟨_, s1⟩ :: syntaxDescendants s1)) -- usingPath
    (fun s0 s1 s2 _ => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- usingAliases
    (fun _ _ => []) -- usingAlias
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- positional
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- named
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- namedArg
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- modInv
    (fun s0 _ _ => (⟨_, s0⟩ :: syntaxDescendants s0)) -- param
    (fun _ => []) -- elem
    (fun s0 _ _ s3 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) -- fnType
    (fun _ _ s2 _ => (⟨_, s2⟩ :: syntaxDescendants s2)) -- mapping
    (fun _ => []) -- userType
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- array
    (fun s0 _ _ => (⟨_, s0⟩ :: syntaxDescendants s0)) -- varDecl
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- index
    (fun s0 s1 s2 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- slice
    (fun s0 _ => (⟨_, s0⟩ :: syntaxDescendants s0)) -- member
    (fun s0 s1 s2 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- callOptions
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- call
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- payableConv
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- metaType
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- unaryPrefix
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- unarySuffix
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- exp
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- mulDivMod
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- addSub
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- shift
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- bitAnd
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- bitXor
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- bitOr
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- order
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- equality
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- and
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- or
    (fun s0 s1 s2 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- cond
    (fun _ s1 s2 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- assign
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- new
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- tuple
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- inlineArray
    (fun _ => []) -- ident
    (fun _ => []) -- lit
    (fun _ _ => []) -- litUnit
    (fun _ _ => []) -- elemType
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- declVar
    (fun _ s1 s2 s3 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) -- declTuple
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- exprStmt
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- blockStmt
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- simpleStmt
    (fun s0 s1 s2 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- ifStmt
    (fun s0 s1 s2 s3 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) -- forStmt
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- whileStmt
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- doWhile
    ([]) -- continueStmt
    ([]) -- breakStmt
    (fun s0 s1 s2 s3 s4 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) -- tryStmt
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- catchPlain
    (fun _ s1 s2 s3 => (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) -- catchSig
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- returnStmt
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- emit
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- revert
    (fun _ _ s2 => (⟨_, s2⟩ :: syntaxDescendants s2)) -- assembly
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- block
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- stmtItem
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- uncheckedItem
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- yulBlock
    (fun _ _ s2 => (⟨_, s2⟩ :: syntaxDescendants s2)) -- yulLet
    (fun _ _ s2 => (⟨_, s2⟩ :: syntaxDescendants s2)) -- yulAssign
    (fun s0 => (⟨_, s0⟩ :: syntaxDescendants s0)) -- yulExprStmt
    (fun s0 s1 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) -- yulIf
    (fun s0 s1 s2 s3 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) -- yulFor
    (fun s0 s1 s2 => (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) -- yulSwitch
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- yulCase
    ([]) -- yulLeave
    ([]) -- yulBreak
    ([]) -- yulContinue
    (fun _ _ _ s3 => (⟨_, s3⟩ :: syntaxDescendants s3)) -- yulFun
    (fun _ _ => []) -- yulPath
    (fun _ s1 => (⟨_, s1⟩ :: syntaxDescendants s1)) -- yulCall
    (fun _ => []) -- yulLit
termination_by structural s

/-- Expose the root without unfolding the recursive descendants walk. -/
def syntaxOccurrences {c : Cat} (s : Syn c) : List SyntaxOccurrence :=
  ⟨c, s⟩ :: syntaxDescendants s

theorem syntaxOccurrences_root : ∀ (c : Cat) (s : Syn c),
    (⟨c, s⟩ : SyntaxOccurrence) ∈ syntaxOccurrences s := by
  intro c s
  exact List.mem_cons_self

/-- info: 'Solidity.Frontend.Admission.syntaxOccurrences_root' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms syntaxOccurrences_root

end Solidity.Frontend.Admission
