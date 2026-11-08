import Solidity.Frontend.Admission.SyntaxOccurrences

/-! Structural laws against the independent Source.Syn.Sub relation.
No execution-root, feature classification or frontend adequacy is asserted. -/
namespace Solidity.Frontend.Admission
open Solidity.Source

theorem syntaxDescendants_children : ∀ (c : Cat) (s : Syn c),
    syntaxDescendants s = s.children.flatMap (fun x => syntaxOccurrences x.2) := by
  intro c s
  cases s with
  | nil =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | cons s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | none =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | some s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | unit s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | pragma s0 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | importPath s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | importSymbols s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | importStar s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | importAlias s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | contract s0 s1 s2 s3 s4 =>
    change (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s4⟩ :: syntaxDescendants s4) = ((⟨_, s2⟩ :: syntaxDescendants s2) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ ((⟨_, s4⟩ :: syntaxDescendants s4) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | interface s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | library s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | topPart s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | inherit s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | constructor s0 s1 s2 s3 s4 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s4⟩ :: syntaxDescendants s4) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | function s0 s1 s2 s3 s4 s5 s6 s7 s8 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4) ++ (⟨_, s7⟩ :: syntaxDescendants s7) ++ (⟨_, s8⟩ :: syntaxDescendants s8) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s4⟩ :: syntaxDescendants s4) ++ ((⟨_, s7⟩ :: syntaxDescendants s7) ++ ((⟨_, s8⟩ :: syntaxDescendants s8) ++ []))))
    simp only [List.append_nil, List.append_assoc]
  | modifier s0 s1 s2 s3 s4 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s4⟩ :: syntaxDescendants s4) ++ []))
    simp only [List.append_nil]
  | fallback s0 s1 s2 s3 s4 s5 s6 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s6⟩ :: syntaxDescendants s6) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ ((⟨_, s6⟩ :: syntaxDescendants s6) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | fbNoParams =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | fbParams s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | receive s0 s1 s2 s3 s4 s5 =>
    change (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s5⟩ :: syntaxDescendants s5) = ((⟨_, s2⟩ :: syntaxDescendants s2) ++ ((⟨_, s5⟩ :: syntaxDescendants s5) ++ []))
    simp only [List.append_nil]
  | struct s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | structMember s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | enum s0 s1 s2 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | udvt s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | stateVar s0 s1 s2 s3 s4 s5 s6 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s6⟩ :: syntaxDescendants s6) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s6⟩ :: syntaxDescendants s6) ++ []))
    simp only [List.append_nil]
  | constant s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | event s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | eventParam s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | error s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | errorParam s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | usingPart s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | usingPath s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | usingAliases s0 s1 s2 s3 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | usingAlias s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | positional s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | named s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | namedArg s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | modInv s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | param s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | elem s0 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | fnType s0 s1 s2 s3 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s3⟩ :: syntaxDescendants s3) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ []))
    simp only [List.append_nil]
  | mapping s0 s1 s2 s3 =>
    change (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])
    simp only [List.append_nil]
  | userType s0 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | array s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | varDecl s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | index s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | slice s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | member s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | callOptions s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | call s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | payableConv s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | metaType s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | unaryPrefix s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | unarySuffix s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | exp s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | mulDivMod s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | addSub s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | shift s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | bitAnd s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | bitXor s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | bitOr s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | order s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | equality s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | and s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | or s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | cond s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | assign s0 s1 s2 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ []))
    simp only [List.append_nil]
  | new s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | tuple s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | inlineArray s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | ident s0 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | lit s0 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | litUnit s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | elemType s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | declVar s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | declTuple s0 s1 s2 s3 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | exprStmt s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | blockStmt s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | simpleStmt s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | ifStmt s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | forStmt s0 s1 s2 s3 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ []))))
    simp only [List.append_nil, List.append_assoc]
  | whileStmt s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | doWhile s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | continueStmt =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | breakStmt =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | tryStmt s0 s1 s2 s3 s4 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s4⟩ :: syntaxDescendants s4) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ ((⟨_, s4⟩ :: syntaxDescendants s4) ++ [])))))
    simp only [List.append_nil, List.append_assoc]
  | catchPlain s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | catchSig s0 s1 s2 s3 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | returnStmt s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | emit s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | revert s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | assembly s0 s1 s2 =>
    change (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])
    simp only [List.append_nil]
  | block s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | stmtItem s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | uncheckedItem s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | yulBlock s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | yulLet s0 s1 s2 =>
    change (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])
    simp only [List.append_nil]
  | yulAssign s0 s1 s2 =>
    change (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])
    simp only [List.append_nil]
  | yulExprStmt s0 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ [])
    simp only [List.append_nil]
  | yulIf s0 s1 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ []))
    simp only [List.append_nil]
  | yulFor s0 s1 s2 s3 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ ((⟨_, s3⟩ :: syntaxDescendants s3) ++ []))))
    simp only [List.append_nil, List.append_assoc]
  | yulSwitch s0 s1 s2 =>
    change (⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) = ((⟨_, s0⟩ :: syntaxDescendants s0) ++ ((⟨_, s1⟩ :: syntaxDescendants s1) ++ ((⟨_, s2⟩ :: syntaxDescendants s2) ++ [])))
    simp only [List.append_nil, List.append_assoc]
  | yulCase s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | yulLeave =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | yulBreak =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | yulContinue =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | yulFun s0 s1 s2 s3 =>
    change (⟨_, s3⟩ :: syntaxDescendants s3) = ((⟨_, s3⟩ :: syntaxDescendants s3) ++ [])
    simp only [List.append_nil]
  | yulPath s0 s1 =>
    change ([] : List SyntaxOccurrence) = []
    rfl
  | yulCall s0 s1 =>
    change (⟨_, s1⟩ :: syntaxDescendants s1) = ((⟨_, s1⟩ :: syntaxDescendants s1) ++ [])
    simp only [List.append_nil]
  | yulLit s0 =>
    change ([] : List SyntaxOccurrence) = []
    rfl

theorem syntaxOccurrences_sound : ∀ (c : Cat) (s : Syn c) (x : SyntaxOccurrence),
    x ∈ syntaxOccurrences s → Syn.Sub x ⟨c, s⟩ := by
  intro c s
  induction s with
  | nil =>
    intro x hx
    change x ∈ (⟨_, .nil⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | cons s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .cons s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | none =>
    intro x hx
    change x ∈ (⟨_, .none⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | some s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .some s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | unit s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .unit s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | pragma s0 =>
    intro x hx
    change x ∈ (⟨_, .pragma s0⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | importPath s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .importPath s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | importSymbols s0 s1 s2 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .importSymbols s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | importStar s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .importStar s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | importAlias s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .importAlias s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | contract s0 s1 s2 s3 s4 ih2 ih3 ih4 =>
    intro x hx
    change x ∈ (⟨_, .contract s0 s1 s2 s3 s4⟩ : SyntaxOccurrence) :: ((⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih2 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih3 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih4 x h2)
  | interface s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .interface s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | library s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .library s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | topPart s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .topPart s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | inherit s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .inherit s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | constructor s0 s1 s2 s3 s4 ih0 ih1 ih4 =>
    intro x hx
    change x ∈ (⟨_, .constructor s0 s1 s2 s3 s4⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih4 x h2)
  | function s0 s1 s2 s3 s4 s5 s6 s7 s8 ih1 ih4 ih7 ih8 =>
    intro x hx
    change x ∈ (⟨_, .function s0 s1 s2 s3 s4 s5 s6 s7 s8⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4) ++ (⟨_, s7⟩ :: syntaxDescendants s7) ++ (⟨_, s8⟩ :: syntaxDescendants s8)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (((h0 | h1) | h2) | h3)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih4 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih7 x h2)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) (ih8 x h3)
  | modifier s0 s1 s2 s3 s4 ih1 ih4 =>
    intro x hx
    change x ∈ (⟨_, .modifier s0 s1 s2 s3 s4⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih4 x h1)
  | fallback s0 s1 s2 s3 s4 s5 s6 ih0 ih3 ih6 =>
    intro x hx
    change x ∈ (⟨_, .fallback s0 s1 s2 s3 s4 s5 s6⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s6⟩ :: syntaxDescendants s6)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih3 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih6 x h2)
  | fbNoParams =>
    intro x hx
    change x ∈ (⟨_, .fbNoParams⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | fbParams s0 s1 s2 ih0 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .fbParams s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
  | receive s0 s1 s2 s3 s4 s5 ih2 ih5 =>
    intro x hx
    change x ∈ (⟨_, .receive s0 s1 s2 s3 s4 s5⟩ : SyntaxOccurrence) :: ((⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s5⟩ :: syntaxDescendants s5)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih2 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih5 x h1)
  | struct s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .struct s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | structMember s0 s1 ih0 =>
    intro x hx
    change x ∈ (⟨_, .structMember s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | enum s0 s1 s2 =>
    intro x hx
    change x ∈ (⟨_, .enum s0 s1 s2⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | udvt s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .udvt s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | stateVar s0 s1 s2 s3 s4 s5 s6 ih0 ih6 =>
    intro x hx
    change x ∈ (⟨_, .stateVar s0 s1 s2 s3 s4 s5 s6⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s6⟩ :: syntaxDescendants s6)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih6 x h1)
  | constant s0 s1 s2 ih0 ih2 =>
    intro x hx
    change x ∈ (⟨_, .constant s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | event s0 s1 s2 ih1 =>
    intro x hx
    change x ∈ (⟨_, .event s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | eventParam s0 s1 s2 ih0 =>
    intro x hx
    change x ∈ (⟨_, .eventParam s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | error s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .error s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | errorParam s0 s1 ih0 =>
    intro x hx
    change x ∈ (⟨_, .errorParam s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | usingPart s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .usingPart s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | usingPath s0 s1 s2 ih1 =>
    intro x hx
    change x ∈ (⟨_, .usingPath s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | usingAliases s0 s1 s2 s3 ih0 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .usingAliases s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
  | usingAlias s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .usingAlias s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | positional s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .positional s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | named s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .named s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | namedArg s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .namedArg s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | modInv s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .modInv s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | param s0 s1 s2 ih0 =>
    intro x hx
    change x ∈ (⟨_, .param s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | elem s0 =>
    intro x hx
    change x ∈ (⟨_, .elem s0⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | fnType s0 s1 s2 s3 ih0 ih3 =>
    intro x hx
    change x ∈ (⟨_, .fnType s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih3 x h1)
  | mapping s0 s1 s2 s3 ih2 =>
    intro x hx
    change x ∈ (⟨_, .mapping s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih2 x hc)
  | userType s0 =>
    intro x hx
    change x ∈ (⟨_, .userType s0⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | array s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .array s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | varDecl s0 s1 s2 ih0 =>
    intro x hx
    change x ∈ (⟨_, .varDecl s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | index s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .index s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | slice s0 s1 s2 ih0 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .slice s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
  | member s0 s1 ih0 =>
    intro x hx
    change x ∈ (⟨_, .member s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | callOptions s0 s1 s2 ih0 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .callOptions s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
  | call s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .call s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | payableConv s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .payableConv s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | metaType s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .metaType s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | unaryPrefix s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .unaryPrefix s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | unarySuffix s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .unarySuffix s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | exp s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .exp s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | mulDivMod s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .mulDivMod s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | addSub s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .addSub s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | shift s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .shift s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | bitAnd s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .bitAnd s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | bitXor s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .bitXor s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | bitOr s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .bitOr s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | order s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .order s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | equality s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .equality s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | and s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .and s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | or s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .or s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | cond s0 s1 s2 ih0 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .cond s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
  | assign s0 s1 s2 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .assign s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
  | new s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .new s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | tuple s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .tuple s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | inlineArray s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .inlineArray s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | ident s0 =>
    intro x hx
    change x ∈ (⟨_, .ident s0⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | lit s0 =>
    intro x hx
    change x ∈ (⟨_, .lit s0⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | litUnit s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .litUnit s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | elemType s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .elemType s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | declVar s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .declVar s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | declTuple s0 s1 s2 s3 ih1 ih2 ih3 =>
    intro x hx
    change x ∈ (⟨_, .declTuple s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih3 x h2)
  | exprStmt s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .exprStmt s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | blockStmt s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .blockStmt s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | simpleStmt s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .simpleStmt s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | ifStmt s0 s1 s2 ih0 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .ifStmt s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
  | forStmt s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
    intro x hx
    change x ∈ (⟨_, .forStmt s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (((h0 | h1) | h2) | h3)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) (ih3 x h3)
  | whileStmt s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .whileStmt s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | doWhile s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .doWhile s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | continueStmt =>
    intro x hx
    change x ∈ (⟨_, .continueStmt⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | breakStmt =>
    intro x hx
    change x ∈ (⟨_, .breakStmt⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | tryStmt s0 s1 s2 s3 s4 ih0 ih1 ih2 ih3 ih4 =>
    intro x hx
    change x ∈ (⟨_, .tryStmt s0 s1 s2 s3 s4⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3) ++ (⟨_, s4⟩ :: syntaxDescendants s4)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((((h0 | h1) | h2) | h3) | h4)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) (ih3 x h3)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))) (ih4 x h4)
  | catchPlain s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .catchPlain s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | catchSig s0 s1 s2 s3 ih1 ih2 ih3 =>
    intro x hx
    change x ∈ (⟨_, .catchSig s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih1 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih2 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih3 x h2)
  | returnStmt s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .returnStmt s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | emit s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .emit s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | revert s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .revert s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | assembly s0 s1 s2 ih2 =>
    intro x hx
    change x ∈ (⟨_, .assembly s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih2 x hc)
  | block s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .block s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | stmtItem s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .stmtItem s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | uncheckedItem s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .uncheckedItem s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | yulBlock s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .yulBlock s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | yulLet s0 s1 s2 ih2 =>
    intro x hx
    change x ∈ (⟨_, .yulLet s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih2 x hc)
  | yulAssign s0 s1 s2 ih2 =>
    intro x hx
    change x ∈ (⟨_, .yulAssign s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih2 x hc)
  | yulExprStmt s0 ih0 =>
    intro x hx
    change x ∈ (⟨_, .yulExprStmt s0⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih0 x hc)
  | yulIf s0 s1 ih0 ih1 =>
    intro x hx
    change x ∈ (⟨_, .yulIf s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (h0 | h1)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
  | yulFor s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
    intro x hx
    change x ∈ (⟨_, .yulFor s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2) ++ (⟨_, s3⟩ :: syntaxDescendants s3)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with (((h0 | h1) | h2) | h3)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) (ih3 x h3)
  | yulSwitch s0 s1 s2 ih0 ih1 ih2 =>
    intro x hx
    change x ∈ (⟨_, .yulSwitch s0 s1 s2⟩ : SyntaxOccurrence) :: ((⟨_, s0⟩ :: syntaxDescendants s0) ++ (⟨_, s1⟩ :: syntaxDescendants s1) ++ (⟨_, s2⟩ :: syntaxDescendants s2)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · simp only [List.mem_append] at hc
      rcases hc with ((h0 | h1) | h2)
      · exact .child (List.mem_cons_self) (ih0 x h0)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_self)) (ih1 x h1)
      · exact .child (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) (ih2 x h2)
  | yulCase s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .yulCase s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | yulLeave =>
    intro x hx
    change x ∈ (⟨_, .yulLeave⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | yulBreak =>
    intro x hx
    change x ∈ (⟨_, .yulBreak⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | yulContinue =>
    intro x hx
    change x ∈ (⟨_, .yulContinue⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | yulFun s0 s1 s2 s3 ih3 =>
    intro x hx
    change x ∈ (⟨_, .yulFun s0 s1 s2 s3⟩ : SyntaxOccurrence) :: ((⟨_, s3⟩ :: syntaxDescendants s3)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih3 x hc)
  | yulPath s0 s1 =>
    intro x hx
    change x ∈ (⟨_, .yulPath s0 s1⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)
  | yulCall s0 s1 ih1 =>
    intro x hx
    change x ∈ (⟨_, .yulCall s0 s1⟩ : SyntaxOccurrence) :: ((⟨_, s1⟩ :: syntaxDescendants s1)) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    ·
      exact .child (List.mem_cons_self) (ih1 x hc)
  | yulLit s0 =>
    intro x hx
    change x ∈ (⟨_, .yulLit s0⟩ : SyntaxOccurrence) :: ([]) at hx
    rcases List.mem_cons.mp hx with hr | hc
    · cases hr; exact .refl _
    · exact False.elim (List.not_mem_nil hc)

theorem syntaxOccurrences_complete (x y : SyntaxOccurrence) (h : Syn.Sub x y) :
    x ∈ syntaxOccurrences y.2 := by
  induction h with
  | refl => exact syntaxOccurrences_root _ _
  | @child y c s hy h ih =>
    change x ∈ _ :: syntaxDescendants s
    apply List.mem_cons_of_mem
    rw [syntaxDescendants_children]
    exact List.mem_flatMap.mpr ⟨y, hy, ih⟩

theorem syntaxOccurrences_iff {c : Cat} (s : Syn c) (x : SyntaxOccurrence) :
    x ∈ syntaxOccurrences s ↔ Syn.Sub x ⟨c, s⟩ :=
  ⟨syntaxOccurrences_sound c s x, syntaxOccurrences_complete x ⟨c, s⟩⟩

/-- info: 'Solidity.Frontend.Admission.syntaxDescendants_children' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxDescendants_children
/-- info: 'Solidity.Frontend.Admission.syntaxOccurrences_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxOccurrences_sound
/-- info: 'Solidity.Frontend.Admission.syntaxOccurrences_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxOccurrences_complete
/-- info: 'Solidity.Frontend.Admission.syntaxOccurrences_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxOccurrences_iff

/-! Generic whole-syntax metadata collection. Regression: headers are not
part of a declaration-only roster. Classifiers share the canonical visitor
rather than introducing per-feature traversal copies. -/
universe u

/-- Collect direct field values with their actual intrinsic sites. -/
def syntaxFieldUses {α : Type u} {c : Cat} (root : Syn c)
    (fields : ∀ {k : Cat}, Syn k → List α) : List (SyntaxOccurrence × α) :=
  (syntaxOccurrences root).flatMap fun site =>
    (fields site.2).map fun value => (site,value)

/-- Exact field accounting against the independent intrinsic subterm relation;
classifier validity/completeness and lexical positions remain separate. -/
theorem syntaxFieldUses_iff {α : Type u} {c : Cat} (root : Syn c)
    (fields : ∀ {k : Cat}, Syn k → List α) (site : SyntaxOccurrence) (value : α) :
    (site,value) ∈ syntaxFieldUses root fields ↔
      Syn.Sub site ⟨c,root⟩ ∧ value ∈ fields site.2 := by
  simp only [syntaxFieldUses, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨other,member,field,present,equality⟩
    have sites := congrArg Prod.fst equality
    have values := congrArg Prod.snd equality
    dsimp only at sites values
    cases sites
    cases values
    exact ⟨(syntaxOccurrences_iff root site).mp member,present⟩
  · rintro ⟨subterm,present⟩
    exact ⟨site,(syntaxOccurrences_iff root site).mpr subterm,value,present,rfl⟩

/-- info: 'Solidity.Frontend.Admission.syntaxFieldUses_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms syntaxFieldUses_iff
end Solidity.Frontend.Admission
