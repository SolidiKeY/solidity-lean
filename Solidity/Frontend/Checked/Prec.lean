import Solidity.Source.Syntax

/-!
# Precedence, associativity and the dangling `else` (G10, G11)

A token sequence can be the yield (`Syn.yield`) of several trees: `a + b * c`
of `addSub` over `mulDivMod` and of `mulDivMod` over `addSub`.  `Syn.prec`
selects one: every node satisfies `Syn.precNode`, the precedence and
associativity of the pinned grammar's `expression` rule (alternatives listed
first bind tighter; `**`, `?:` and assignment associate to the right) and the
`if`/`else` rule (an `else` belongs to the nearest `if`).

Levels (`Syn.level`), loosest first: assignment 0, conditional 1, `||` 2,
`&&` 3, equality 4, order 5, `|` 6, `^` 7, `&` 8, shifts 9, `+ -` 10,
`* / %` 11, `**` 12, prefix operators 13, postfix `++ --` 14, index, slice,
member, call options and calls 15, primaries 16.

**Where the grammar and solc's parser disagree, the input is refused**
(`Syn.precNode` is false, so no accepted tree exists), recorded in
`docs/feature-work/frontend-parse.md`:

* a postfix `++`/`--` directly under a prefix operator (`-x++`): the grammar
  reads `(-x)++`, solc `-(x++)`;
* a postfix `++`/`--` as the base of an index, slice, member, call options
  or call (`x++.f`) or of another postfix `++`/`--`: the grammar accepts,
  solc's parser does not;
* an assignment as the false branch of a conditional (`a ? b : c = d`): the
  grammar reads `(a ? b : c) = d`, solc `a ? b : (c = d)`.

**Greedy readings** where the grammar is ambiguous and solc reads one way:
`new T[](n)` and `new a.b(…)` keep `[]` and `.b` in the type name (an index
or member never has a `new` base); `emit`/`revert` targets are paths
(identifiers and member accesses), as solc's parser reads them.
-/

namespace Solidity.Source

/-- The binding level of an expression's root (16 for non-expressions). -/
def Syn.level : {c : Cat} → Syn c → Nat
  | _, .assign .. => 0
  | _, .cond .. => 1
  | _, .or .. => 2
  | _, .and .. => 3
  | _, .equality .. => 4
  | _, .order .. => 5
  | _, .bitOr .. => 6
  | _, .bitXor .. => 7
  | _, .bitAnd .. => 8
  | _, .shift .. => 9
  | _, .addSub .. => 10
  | _, .mulDivMod .. => 11
  | _, .exp .. => 12
  | _, .unaryPrefix .. => 13
  | _, .unarySuffix .. => 14
  | _, .index .. | _, .slice .. | _, .member .. | _, .callOptions .. | _, .call .. => 15
  | _, _ => 16

def Syn.isNew : {c : Cat} → Syn c → Bool
  | _, .new _ => true
  | _, _ => false

/-- An identifier or a member access of a path. -/
def Syn.isPathExpr : {c : Cat} → Syn c → Bool
  | _, .ident _ => true
  | _, .member e _ => e.isPathExpr
  | _, _ => false

/-- A statement ending in an `if` without `else`. -/
def Syn.openIf : {c : Cat} → Syn c → Bool
  | _, .ifStmt _ _ .none => true
  | _, .ifStmt _ _ (.some s) => s.openIf
  | _, .forStmt _ _ _ b => b.openIf
  | _, .whileStmt _ b => b.openIf
  | _, _ => false

/-- A left-associative binary operator at level `p`. -/
def binOk {c c' : Cat} (p : Nat) (a : Syn c) (b : Syn c') : Bool := p ≤ a.level && p + 1 ≤ b.level

/-- The condition at one node. -/
def Syn.precNode : {c : Cat} → Syn c → Bool
  | _, .index e _ => 15 ≤ e.level && !e.isNew
  | _, .slice e _ _ => 15 ≤ e.level && !e.isNew
  | _, .member e _ => 15 ≤ e.level && !e.isNew
  | _, .callOptions e _ _ => 15 ≤ e.level
  | _, .call e _ => 15 ≤ e.level
  | _, .unarySuffix _ e => 15 ≤ e.level
  | _, .unaryPrefix _ e => 13 ≤ e.level && e.level != 14
  | _, .exp a b => 13 ≤ a.level && 12 ≤ b.level
  | _, .mulDivMod _ a b => binOk 11 a b
  | _, .addSub _ a b => binOk 10 a b
  | _, .shift _ a b => binOk 9 a b
  | _, .bitAnd a b => binOk 8 a b
  | _, .bitXor a b => binOk 7 a b
  | _, .bitOr a b => binOk 6 a b
  | _, .order _ a b => binOk 5 a b
  | _, .equality _ a b => binOk 4 a b
  | _, .and a b => binOk 3 a b
  | _, .or a b => binOk 2 a b
  | _, .cond c _ f => 2 ≤ c.level && 1 ≤ f.level
  | _, .assign _ a _ => 2 ≤ a.level
  | _, .ifStmt _ t (.some _) => !t.openIf
  | _, .emit e _ => e.isPathExpr
  | _, .revert e _ => e.isPathExpr
  | _, _ => true

-- Generated from `Syn.nodes` (`Solidity/Source/Ctor.lean`): every node.
/-- Every node of a tree satisfies `p`. -/
def Syn.all (p : {c : Cat} → Syn c → Bool) : {c : Cat} → Syn c → Bool
  | _, s@(.nil) => p s
  | _, s@(.cons s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.none) => p s
  | _, s@(.some s0) => p s && s0.all p
  | _, s@(.unit s0) => p s && s0.all p
  | _, s@(.pragma _) => p s
  | _, s@(.importPath _ _) => p s
  | _, s@(.importSymbols s0 s1 _) => p s && s0.all p && s1.all p
  | _, s@(.importStar _ _) => p s
  | _, s@(.importAlias _ _) => p s
  | _, s@(.contract _ _ s2 s3 s4) => p s && s2.all p && s3.all p && s4.all p
  | _, s@(.interface _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.library _ s1) => p s && s1.all p
  | _, s@(.topPart s0) => p s && s0.all p
  | _, s@(.inherit _ s1) => p s && s1.all p
  | _, s@(.constructor s0 s1 _ _ s4) => p s && s0.all p && s1.all p && s4.all p
  | _, s@(.function _ s1 _ _ s4 _ _ s7 s8) => p s && s1.all p && s4.all p && s7.all p && s8.all p
  | _, s@(.modifier _ s1 _ _ s4) => p s && s1.all p && s4.all p
  | _, s@(.fallback s0 _ _ s3 _ _ s6) => p s && s0.all p && s3.all p && s6.all p
  | _, s@(.fbNoParams) => p s
  | _, s@(.fbParams s0 s1 s2) => p s && s0.all p && s1.all p && s2.all p
  | _, s@(.receive _ _ s2 _ _ s5) => p s && s2.all p && s5.all p
  | _, s@(.struct _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.structMember s0 _) => p s && s0.all p
  | _, s@(.enum _ _ _) => p s
  | _, s@(.udvt _ _) => p s
  | _, s@(.stateVar s0 _ _ _ _ _ s6) => p s && s0.all p && s6.all p
  | _, s@(.constant s0 _ s2) => p s && s0.all p && s2.all p
  | _, s@(.event _ s1 _) => p s && s1.all p
  | _, s@(.eventParam s0 _ _) => p s && s0.all p
  | _, s@(.error _ s1) => p s && s1.all p
  | _, s@(.errorParam s0 _) => p s && s0.all p
  | _, s@(.usingPart s0) => p s && s0.all p
  | _, s@(.usingPath _ s1 _) => p s && s1.all p
  | _, s@(.usingAliases s0 s1 s2 _) => p s && s0.all p && s1.all p && s2.all p
  | _, s@(.usingAlias _ _) => p s
  | _, s@(.positional s0) => p s && s0.all p
  | _, s@(.named s0) => p s && s0.all p
  | _, s@(.namedArg _ s1) => p s && s1.all p
  | _, s@(.modInv _ s1) => p s && s1.all p
  | _, s@(.param s0 _ _) => p s && s0.all p
  | _, s@(.elem _) => p s
  | _, s@(.fnType s0 _ _ s3) => p s && s0.all p && s3.all p
  | _, s@(.mapping _ _ s2 _) => p s && s2.all p
  | _, s@(.userType _) => p s
  | _, s@(.array s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.varDecl s0 _ _) => p s && s0.all p
  | _, s@(.index s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.slice s0 s1 s2) => p s && s0.all p && s1.all p && s2.all p
  | _, s@(.member s0 _) => p s && s0.all p
  | _, s@(.callOptions s0 s1 s2) => p s && s0.all p && s1.all p && s2.all p
  | _, s@(.call s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.payableConv s0) => p s && s0.all p
  | _, s@(.metaType s0) => p s && s0.all p
  | _, s@(.unaryPrefix _ s1) => p s && s1.all p
  | _, s@(.unarySuffix _ s1) => p s && s1.all p
  | _, s@(.exp s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.mulDivMod _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.addSub _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.shift _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.bitAnd s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.bitXor s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.bitOr s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.order _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.equality _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.and s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.or s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.cond s0 s1 s2) => p s && s0.all p && s1.all p && s2.all p
  | _, s@(.assign _ s1 s2) => p s && s1.all p && s2.all p
  | _, s@(.new s0) => p s && s0.all p
  | _, s@(.tuple s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.inlineArray s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.ident _) => p s
  | _, s@(.lit _) => p s
  | _, s@(.litUnit _ _) => p s
  | _, s@(.elemType _ _) => p s
  | _, s@(.declVar s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.declTuple _ s1 s2 s3) => p s && s1.all p && s2.all p && s3.all p
  | _, s@(.exprStmt s0) => p s && s0.all p
  | _, s@(.blockStmt s0) => p s && s0.all p
  | _, s@(.simpleStmt s0) => p s && s0.all p
  | _, s@(.ifStmt s0 s1 s2) => p s && s0.all p && s1.all p && s2.all p
  | _, s@(.forStmt s0 s1 s2 s3) => p s && s0.all p && s1.all p && s2.all p && s3.all p
  | _, s@(.whileStmt s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.doWhile s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.continueStmt) => p s
  | _, s@(.breakStmt) => p s
  | _, s@(.tryStmt s0 s1 s2 s3 s4) => p s && s0.all p && s1.all p && s2.all p && s3.all p && s4.all p
  | _, s@(.catchPlain s0) => p s && s0.all p
  | _, s@(.catchSig _ s1 s2 s3) => p s && s1.all p && s2.all p && s3.all p
  | _, s@(.returnStmt s0) => p s && s0.all p
  | _, s@(.emit s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.revert s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.assembly _ _ s2) => p s && s2.all p
  | _, s@(.block s0) => p s && s0.all p
  | _, s@(.stmtItem s0) => p s && s0.all p
  | _, s@(.uncheckedItem s0) => p s && s0.all p
  | _, s@(.yulBlock s0) => p s && s0.all p
  | _, s@(.yulLet _ _ s2) => p s && s2.all p
  | _, s@(.yulAssign _ _ s2) => p s && s2.all p
  | _, s@(.yulExprStmt s0) => p s && s0.all p
  | _, s@(.yulIf s0 s1) => p s && s0.all p && s1.all p
  | _, s@(.yulFor s0 s1 s2 s3) => p s && s0.all p && s1.all p && s2.all p && s3.all p
  | _, s@(.yulSwitch s0 s1 s2) => p s && s0.all p && s1.all p && s2.all p
  | _, s@(.yulCase _ s1) => p s && s1.all p
  | _, s@(.yulLeave) => p s
  | _, s@(.yulBreak) => p s
  | _, s@(.yulContinue) => p s
  | _, s@(.yulFun _ _ _ s3) => p s && s3.all p
  | _, s@(.yulPath _ _) => p s
  | _, s@(.yulCall _ s1) => p s && s1.all p
  | _, s@(.yulLit _) => p s

/-- **The precedence predicate**: every node is read as the grammar (and
solc) reads it. -/
def Syn.prec {c : Cat} (t : Syn c) : Bool := t.precNode && t.all Syn.precNode

/-- The root of a precedence-selected tree satisfies the condition (`Syn.all`
checks it too; stated at the root so no case split over `Syn` is needed). -/
theorem Syn.prec_root {c : Cat} {t : Syn c} (h : t.prec = true) : t.precNode = true := by
  simp only [Syn.prec, Bool.and_eq_true] at h
  exact h.1

end Solidity.Source
