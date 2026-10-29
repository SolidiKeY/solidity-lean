import Solidity.Frontend.Checked.TypeExamples

/-!
# Expression controls (G10)

Precedence and associativity as theorems about `Syn.precNode`, which every
accepted expression satisfies at every node (`parseExpr_prec_root`); every
operator of the grammar parsed into its constructor; concrete trees for the
tricky forms; the constructor coverage of the expression constructors; and
refused inputs, ambiguous or malformed.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- **Every accepted expression satisfies the precedence condition at its
root** (and, by `Syn.prec`, at every node). -/
theorem parseExpr_prec_root {src : Bytes} {e : Syn .expr} (h : parseExpr src = .ok e) :
    e.precNode = true := by
  obtain ⟨_, _, _, hp⟩ := parseExpr_derives h
  exact Syn.prec_root hp

/-! ## Precedence and associativity -/

section
variable {a b c d : Syn .expr}

/-- Left associativity: the right operand of a left-associative operator is
never an operator of its level. -/
theorem addSub_left_assoc (o o' : AddOp) : (Syn.addSub o a (.addSub o' b c)).precNode = false := by
  show (decide (10 ≤ a.level) && decide (11 ≤ 10)) = false
  simp
theorem mul_left_assoc (o o' : MulOp) :
    (Syn.mulDivMod o a (.mulDivMod o' b c)).precNode = false := by
  show (decide (11 ≤ a.level) && decide (12 ≤ 11)) = false
  simp
theorem or_left_assoc : (Syn.or a (.or b c)).precNode = false := by
  show (decide (2 ≤ a.level) && decide (3 ≤ 2)) = false
  simp

/-- Right associativity of `**`, `?:` and assignment: the left operand is
never of the same level. -/
theorem exp_right_assoc : (Syn.exp (.exp a b) c).precNode = false := rfl
theorem assign_right_assoc (o o' : AssignOp) :
    (Syn.assign o (.assign o' a b) c).precNode = false := rfl
theorem cond_right_assoc {e : Syn .expr} : (Syn.cond (.cond a b c) d e).precNode = false := rfl

/-- Binding: `*` binds tighter than `+` on both sides, `&` than `^` than `|`
than order, order than equality, `&&` than `||`. -/
theorem mul_over_add (o : MulOp) (o' : AddOp) :
    (Syn.mulDivMod o (.addSub o' a b) c).precNode = false ∧
    (Syn.mulDivMod o a (.addSub o' b c)).precNode = false := by
  refine ⟨rfl, ?_⟩
  show (decide (11 ≤ a.level) && decide (12 ≤ 10)) = false
  simp
theorem bit_levels (o : OrderOp) (q : EqOp) (sh : ShiftOp) (ad : AddOp) :
    (Syn.bitAnd (.bitXor a b) c).precNode = false ∧ (Syn.bitXor (.bitOr a b) c).precNode = false ∧
    (Syn.order o (.equality q a b) c).precNode = false ∧
    (Syn.and (.or a b) c).precNode = false ∧ (Syn.shift sh (.bitAnd a b) c).precNode = false ∧
    (Syn.addSub ad (.shift sh a b) c).precNode = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Every binary level, both directions**: a binary node at level `p`
satisfies the condition exactly when its left operand is at level `p` or
above and its right operand above `p` (`**`: left above, right at or above). -/
theorem binary_levels (o : OrderOp) (q : EqOp) (sh : ShiftOp) (ad : AddOp) (mu : MulOp) :
    ((Syn.or a b).precNode = true ↔ 2 ≤ a.level ∧ 3 ≤ b.level) ∧
    ((Syn.and a b).precNode = true ↔ 3 ≤ a.level ∧ 4 ≤ b.level) ∧
    ((Syn.equality q a b).precNode = true ↔ 4 ≤ a.level ∧ 5 ≤ b.level) ∧
    ((Syn.order o a b).precNode = true ↔ 5 ≤ a.level ∧ 6 ≤ b.level) ∧
    ((Syn.bitOr a b).precNode = true ↔ 6 ≤ a.level ∧ 7 ≤ b.level) ∧
    ((Syn.bitXor a b).precNode = true ↔ 7 ≤ a.level ∧ 8 ≤ b.level) ∧
    ((Syn.bitAnd a b).precNode = true ↔ 8 ≤ a.level ∧ 9 ≤ b.level) ∧
    ((Syn.shift sh a b).precNode = true ↔ 9 ≤ a.level ∧ 10 ≤ b.level) ∧
    ((Syn.addSub ad a b).precNode = true ↔ 10 ≤ a.level ∧ 11 ≤ b.level) ∧
    ((Syn.mulDivMod mu a b).precNode = true ↔ 11 ≤ a.level ∧ 12 ≤ b.level) ∧
    ((Syn.exp a b).precNode = true ↔ 13 ≤ a.level ∧ 12 ≤ b.level) := by
  have bin : ∀ (p : Nat) (x y : Syn .expr), binOk p x y = true ↔ p ≤ x.level ∧ p + 1 ≤ y.level :=
    fun p x y => by simp only [binOk, Bool.and_eq_true, decide_eq_true_eq]
  have ex : (decide (13 ≤ a.level) && decide (12 ≤ b.level)) = true ↔ 13 ≤ a.level ∧ 12 ≤ b.level := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨bin 2 a b, bin 3 a b, bin 4 a b, bin 5 a b, bin 6 a b, bin 7 a b, bin 8 a b, bin 9 a b,
    bin 10 a b, bin 11 a b, ex⟩
theorem bitOr_over_order : (Syn.bitOr a (.order .lt b c)).precNode = false := by
  show (decide (6 ≤ a.level) && decide (7 ≤ 5)) = false
  simp

/-- A binary node at level `p` has operands at level `p` and above (left)
and above `p` (right). -/
theorem addSub_levels (o : AddOp) (h : (Syn.addSub o a b).precNode = true) :
    10 ≤ a.level ∧ 11 ≤ b.level := by
  have h' : (decide (10 ≤ a.level) && decide (11 ≤ b.level)) = true := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'

/-- Prefix operators bind tighter than `**` (the operand is never an
exponentiation); a postfix `++`/`--` directly under a prefix operator is
refused (the grammar and solc disagree). -/
theorem prefix_over_exp (o : PrefixOp) : (Syn.unaryPrefix o (.exp a b)).precNode = false := rfl
theorem prefix_suffix_refused (o : PrefixOp) (o' : SuffixOp) :
    (Syn.unaryPrefix o (.unarySuffix o' a)).precNode = false := rfl
theorem cond_false_assign_refused (o : AssignOp) :
    (Syn.cond a b (.assign o c d)).precNode = false := by
  show (decide (2 ≤ a.level) && decide (1 ≤ 0)) = false
  simp
theorem postfix_base (n : String) (o : SuffixOp) :
    (Syn.member (.unarySuffix o a) n).precNode = false ∧
    (Syn.member (.addSub .add a b) n).precNode = false := ⟨rfl, rfl⟩
end

/-! ## Every operator -/

/-- Each assignment operator with its spelling, written out. -/
def assignSpellings : List (AssignOp × String) :=
  [(.assign, "="), (.bitOr, "|="), (.bitXor, "^="), (.bitAnd, "&="), (.shl, "<<="),
    (.sar, ">>="), (.shr, ">>>="), (.add, "+="), (.sub, "-="), (.mul, "*="), (.div, "/="),
    (.mod, "%=")]
def prefixSpellings : List (PrefixOp × String) :=
  [(.inc, "++"), (.dec, "--"), (.not, "!"), (.bitNot, "~"), (.delete, "delete"), (.neg, "-")]

theorem assignSpellings_complete (o : AssignOp) : o ∈ assignSpellings.map Prod.fst := by
  cases o <;> decide
theorem prefixSpellings_complete (o : PrefixOp) : o ∈ prefixSpellings.map Prod.fst := by
  cases o <;> decide

/-- The binary operators of the grammar, spelled out, with their
constructors. -/
def binOps : List (String × (Syn .expr → Syn .expr → Syn .expr)) :=
  [("||", .or), ("&&", .and), ("==", .equality .eq), ("!=", .equality .ne),
    ("<", .order .lt), (">", .order .gt), ("<=", .order .le), (">=", .order .ge),
    ("|", .bitOr), ("^", .bitXor), ("&", .bitAnd), ("<<", .shift .shl),
    (">>", .shift .sar), (">>>", .shift .shr), ("+", .addSub .add), ("-", .addSub .sub),
    ("*", .mulDivMod .mul), ("/", .mulDivMod .div), ("%", .mulDivMod .mod), ("**", .exp)]

def va : Syn .expr := .ident "a"
def vb : Syn .expr := .ident "b"

/-- **Every binary, assignment and prefix operator** parses into its
constructor. -/
theorem every_operator :
    binOps.all (fun (p, mk) => parsesTo expr ("a " ++ p ++ " b") (mk va vb)) = true ∧
    assignSpellings.all (fun (o, sp) => parsesTo expr ("a " ++ sp ++ " b") (.assign o va vb)) = true ∧
    prefixSpellings.all (fun (o, sp) => parsesTo expr (sp ++ " a") (.unaryPrefix o va)) = true ∧
    parsesTo expr "a++" (.unarySuffix .inc va) = true ∧
    parsesTo expr "a--" (.unarySuffix .dec va) = true := by
  decide +kernel

/-! ## Trees -/

def n (k : Nat) : Syn .expr := .lit (.num (.dec k 0 0))

theorem tree_precedence :
    parsesTo expr "a + b * 2" (.addSub .add va (.mulDivMod .mul vb (n 2))) &&
    parsesTo expr "a - b - 2" (.addSub .sub (.addSub .sub va vb) (n 2)) &&
    parsesTo expr "a ** b ** 2" (.exp va (.exp vb (n 2))) &&
    parsesTo expr "-a ** 2" (.exp (.unaryPrefix .neg va) (n 2)) &&
    parsesTo expr "a = b = 2" (.assign .assign va (.assign .assign vb (n 2))) &&
    parsesTo expr "a ? b : 1 ? 2 : 3" (.cond va vb (.cond (n 1) (n 2) (n 3))) &&
    parsesTo expr "a = b ? 1 : 2" (.assign .assign va (.cond vb (n 1) (n 2))) &&
    parsesTo expr "a || b && 1 == 2 < 3" (.or va (.and vb (.equality .eq (n 1) (.order .lt (n 2) (n 3))))) &&
    parsesTo expr "a & b ^ 1 | 2" (.bitOr (.bitXor (.bitAnd va vb) (n 1)) (n 2)) &&
    parsesTo expr "a << b + 1" (.shift .shl va (.addSub .add vb (n 1))) &&
    parsesTo expr "!a.b()" (.unaryPrefix .not (.call (.member va "b") (.positional .nil))) &&
    parsesTo expr "a++ + ++b" (.addSub .add (.unarySuffix .inc va) (.unaryPrefix .inc vb)) &&
    parsesTo expr "delete a[1]" (.unaryPrefix .delete (.index va (.some (n 1))))
      = true := by decide +kernel

theorem tree_forms :
    parsesTo expr "(a, , b)" (.tuple (.some va) (.cons .none (.cons (.some vb) .nil))) &&
    parsesTo expr "(a)" (.tuple (.some va) .nil) &&
    parsesTo expr "()" (.tuple .none .nil) &&
    parsesTo expr "[a, b]" (.inlineArray va (.cons vb .nil)) &&
    parsesTo expr "a[1:]" (.slice va (.some (n 1)) .none) &&
    parsesTo expr "a[:b]" (.slice va .none (.some vb)) &&
    parsesTo expr "a[]" (.index va .none) &&
    parsesTo expr "f(a, b)" (.call (.ident "f") (.positional (.cons va (.cons vb .nil)))) &&
    parsesTo expr "f({x: a, y: b})" (.call (.ident "f")
      (.named (.cons (.namedArg "x" va) (.cons (.namedArg "y" vb) .nil)))) &&
    parsesTo expr "c.f{value: 1, gas: 2}(a)" (.call (.callOptions (.member (.ident "c") "f")
      (.namedArg "value" (n 1)) (.cons (.namedArg "gas" (n 2)) .nil)) (.positional (.cons va .nil))) &&
    parsesTo expr "new uint[](3)" (.call (.new (.array (.elem (.int false 256 (by decide))) .none))
      (.positional (.cons (n 3) .nil))) &&
    parsesTo expr "new a.B" (.new (.userType ⟨"a", ["B"]⟩)) &&
    parsesTo expr "type(C).max" (.member (.metaType (.userType ⟨"C", []⟩)) "max") &&
    parsesTo expr "payable(a)" (.payableConv (.positional (.cons va .nil))) &&
    parsesTo expr "address(this).balance" (.member (.call (.elemType .address (by decide))
      (.positional (.cons (.ident "this") .nil))) "balance") &&
    parsesTo expr "x.address" (.member (.ident "x") "address") &&
    parsesTo expr "1 ether" (.litUnit (.dec 1 0 0) .ether) &&
    parsesTo expr "\"a\" \"b\"" (.lit (.str (ascii "ab"))) &&
    parsesTo expr "a += b -= 1" (.assign .add va (.assign .sub vb (n 1)))
      = true := by decide +kernel

/-! ## Refused -/

def exprErr (s : String) : Option String :=
  match parseExpr (ascii s) with
  | .error e => some e.msg
  | .ok _ => none

/-- Ambiguous between the grammar and solc, refused; malformed, refused. -/
theorem expr_refused :
    exprErr "-a++" = some "refused by Syn.prec (precedence, dangling else or a solc node condition)" ∧
    exprErr "a ? b : c = d" = some "refused by Syn.prec (precedence, dangling else or a solc node condition)" ∧
    exprErr "a++.f" = some "refused by Syn.prec (precedence, dangling else or a solc node condition)" ∧
    exprErr "a++ ++" = some "refused by Syn.prec (precedence, dangling else or a solc node condition)" ∧
    exprErr "(a" = some "expected ')'" ∧
    exprErr "f(a,)" = some "expected an expression" ∧
    exprErr "a +" = some "expected an expression" ∧
    exprErr "[]" = some "expected an expression" ∧
    exprErr "x{}" = some "unexpected token" ∧
    exprErr "a b" = some "unexpected token" ∧
    exprErr "address payable(a)" = some "unexpected token" ∧
    exprErr "type(address payable)" = some "expected a type expression" ∧
    exprErr "type(mapping(uint => uint))" = some "expected a type expression" := by
  decide +kernel

/-- Parenthesized, the refused forms are accepted. -/
theorem expr_parenthesized :
    (exprErr "-(a++)").isNone && (exprErr "a ? b : (c = d)").isNone &&
    (exprErr "(a++).f").isNone = true := by decide +kernel

/-! ## Coverage -/

/-- The expression constructors (G10). -/
def exprCtors : List Ctor :=
  [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix,
    .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order,
    .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit,
    .elemType, .positional, .named, .namedArg]

def exprCorpus : List String :=
  ["a[1] + b[1:2]", "c.d ** e{x: 1}(f)", "g({y: 2}) << h & i", "h ^ i | j < k == l",
    "m && n || o", "z = p ? payable(q) : type(T).max", "new uint[](1)", "[1, 2][0]",
    "(3, 4)", "5 gwei", "uint8(-x)", "x--", "a * b % c", "\"s\""]

def exprCtorsOf (s : String) : List Ctor :=
  match parseExpr (ascii s) with
  | .ok e => e.nodes.map Node.ctor
  | .error _ => []

/-- **Acceptance coverage (G10)**: every expression constructor occurs in an
accepted expression. -/
theorem exprCtors_covered :
    exprCtors.all (fun c => exprCorpus.any fun s => (exprCtorsOf s).contains c) = true := by
  decide +kernel

/-- The expression corpus is in the profile. -/
theorem exprCorpus_in_profile :
    exprCorpus.all (fun s => match parseExpr (ascii s) with
      | .ok e => e.rejections.isEmpty | .error _ => false) = true := by decide +kernel

/-- **Out of the profile, refused precisely**: `>>>`, `>>>=` and `years`
parse (they are syntax) and are rejected with their manifest feature. -/
theorem expr_out_of_profile :
    ["a >>> b", "a >>>= b", "1 years"].map (fun s => match parseExpr (ascii s) with
      | .ok e => e.rejections.map Excl.id | .error _ => []) =
      [["unsignedRightShift"], ["unsignedRightShift"], ["removedUnits"]] ∧
    (match parseInProfile (ascii "contract C { function f() public { x = a >>> 1; } }") with
      | .error e => some e.msg | .ok _ => none) = some "outside the profile: unsignedRightShift" := by
  decide +kernel

end Solidity.Frontend.Checked

/-- info: 'Solidity.Frontend.Checked.parseExpr_prec_root' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.parseExpr_prec_root
/-- info: 'Solidity.Frontend.Checked.every_operator' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.every_operator

