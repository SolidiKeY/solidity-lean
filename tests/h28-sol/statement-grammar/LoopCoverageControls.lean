import Solidity.Frontend.StatementGrammarH28.LoopCoverage

/-! Every BooleanLoops constructor, all loop arrangements and an unbounded
family, plus malformed-token and excluded-conditional negative controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def loopTower (u : Bool) : Nat → Syn (.stmt ⟨true, u⟩)
  | 0 => .blockStmt (.block .nil)
  | n + 1 => .whileStmt (.lit (.bool true)) (loopTower u n)

def loopTowerTokens : Nat → List Tok
  | 0 => braces []
  | n + 1 => [.kw .while_, .punct .lparen, .bool true, .punct .rparen] ++ loopTowerTokens n

theorem loop_tower_relation (u : Bool) (n : Nat) :
    BooleanLoops (loopTower u n) (loopTowerTokens n) n := by
  induction n with
  | zero => exact .block .nil
  | succ n ih => exact .whileLoop ih

theorem loop_tower_coverage (u : Bool) (n extra : Nat) (s : St) :
    stmt (extra + n + 6) ⟨true, u⟩ (locatedInput (loopTowerTokens n) s) =
      .ok (loopTower u n, s) := boolean_loops_coverage (loop_tower_relation u n) extra s

def mixedLoops : Syn (.stmt .body) :=
  .whileStmt (.lit (.bool false))
    (.doWhile (.forStmt .none .none .none
      (.blockStmt (.block (.cons (.stmtItem .breakStmt)
        (.cons (.stmtItem .continueStmt) (.cons (.stmtItem (.returnStmt .none)) .nil))))))
      (.lit (.bool true)))

def mixedLoopTokens : List Tok :=
  [.kw .while_, .punct .lparen, .bool false, .punct .rparen, .kw .do_,
   .kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++
    braces [.kw .break_, .punct .semi, .kw .continue_, .punct .semi, .kw .return_, .punct .semi] ++
    [.kw .while_, .punct .lparen, .bool true, .punct .rparen, .punct .semi]

theorem mixed_loops_relation : BooleanLoops mixedLoops mixedLoopTokens 3 :=
  .whileLoop (.doLoop (.forLoop (.block (.breakCons (.continueCons (.returnCons .nil))))))

theorem mixed_loops_coverage (n : Nat) (s : St) :
    stmt (n + 9) .body (locatedInput mixedLoopTokens s) = .ok (mixedLoops, s) :=
  boolean_loops_coverage mixed_loops_relation n s

theorem mixed_loops_yield (L : List Choice) :
    mixedLoops.yield L = some ([mixedLoopTokens], L) :=
  boolean_loops_yield mixed_loops_relation L

theorem mixed_loops_unique {x : Syn (.stmt .body)} {ts : List Tok} {d : Nat}
    (h : BooleanLoops x ts d) (hx : x.Derives mixedLoopTokens) : x = mixedLoops :=
  boolean_loops_yield_unique h mixed_loops_relation hx
    ((boolean_loops_derives_iff mixed_loops_relation mixedLoopTokens).mpr rfl)

theorem conditional_excluded (ts : List Tok) (d : Nat) :
    ¬ BooleanLoops (Syn.ifStmt (k := .body) (.lit (.bool true))
      (.blockStmt (.block .nil)) .none) ts d := by
  intro h
  cases h

theorem zero_fuel_refuses :
    stmt 0 .body (locatedInput mixedLoopTokens ⟨[], [], 0⟩) ≠ .ok (mixedLoops, ⟨[], [], 0⟩) := by
  intro h
  cases h

theorem missing_do_semi_refuses :
    (match stmt 12 .body (locatedInput [.kw .do_, .punct .lbrace, .punct .rbrace,
      .kw .while_, .punct .lparen, .bool false, .punct .rparen] ⟨[], [], 0⟩) with | .error _ => true | .ok _ => false) = true := by
  decide

#print axioms loop_tower_relation
#print axioms loop_tower_coverage
#print axioms mixed_loops_relation
#print axioms mixed_loops_coverage
#print axioms mixed_loops_yield
#print axioms mixed_loops_unique
#print axioms conditional_excluded
#print axioms zero_fuel_refuses
#print axioms missing_do_semi_refuses
end Solidity.Frontend.StatementGrammarH28
