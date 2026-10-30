import Solidity.Source.WellFormed

/-!
# Compile-time constants (G13)

Two relations S01 lacks ("What S01 does not do", Constants):

**Compile-time initializers.**  solc requires the initializer of a
`constant` to be *pure* (`TypeChecker`: "Initial value for constant variable
has to be compile-time constant", error 8349): built from literals, other
constants, operators, `? :`, type conversions and the pure builtins
(`keccak256`, `sha256`, `ripemd160`, `ecrecover`, `addmod`, `mulmod`,
`erc7201`, which `docs/solidity-scope.md` admits as compile-time foldable).  A
local, a state variable, `msg`/`block`, a call of a declared function or an
assignment is not.  `PureS Γ .expr e` is that judgment (over every category
so that argument lists and tuple slots are covered by the same family);
`ConstInitsPure r` requires it of every constant of a resolved unit.

**Named constants as values.**  S01's `arrayLen` folds literal lengths
only.  `TEval`/`NamedConst` are solc's `ConstantEvaluator` (0.8.x): a
literal-only expression folds exactly by S01's `Syn.const`; a named integer
constant has its declared type and its initializer's value converted to it;
an operation with a typed operand takes solc's result type, folds exactly
and converts, so `uint256 constant A = 7;` gives `A / 2 = 3`, and
`uint8 constant C = 255;` gives `C + 1` no value (out of range).
`ArrayLenOK` reads array lengths through it.  **Cycles**: `NamedConst` is a
least fixpoint, so a cyclic definition has no value, and `ConstsAcyclic`
refuses it outright, as solc does, even when no length reads it.
-/

namespace Solidity.Source

/-! ## Pure expressions -/

/-- The builtins whose calls are pure (solc's `FunctionType::isPure`), among
those S01 types. -/
def Builtin.pure : Builtin → Bool
  | .keccak256 | .sha256 | .ripemd160 | .ecrecover | .addmod | .mulmod | .erc7201 => true
  | _ => false

/-- A call head whose call is pure on pure arguments: an elementary type, a
contract or enum (a conversion) or a pure builtin. -/
def pureHead (Γ : Ctx) : Syn .expr → Bool
  | .elemType _ _ => true
  | .ident n =>
    (Γ.convTarget n).isSome ||
      match Γ.resolve n with
      | Option.some (.builtin b) => b.pure
      | _ => false
  | _ => false

/-- A unary operator that keeps purity (not `++`, `--`, `delete`). -/
def PrefixOp.pure : PrefixOp → Bool
  | .neg | .not | .bitNot => true
  | _ => false

/-- **Purity**, over every category: expressions, their argument lists,
tuple slots and call arguments. -/
inductive PureS (Γ : Ctx) : (c : Cat) → Syn c → Prop where
  | nil {c : Cat} : PureS Γ (.list c) .nil
  | cons {c : Cat} {x : Syn c} {xs : Syn (.list c)} : PureS Γ c x → PureS Γ (.list c) xs →
      PureS Γ (.list c) (.cons x xs)
  | some {c : Cat} {x : Syn c} : PureS Γ c x → PureS Γ (.opt c) (.some x)
  | positional {es : Syn (.list .expr)} : PureS Γ (.list .expr) es → PureS Γ .callArgs (.positional es)
  | lit (l : Lit) : PureS Γ .expr (.lit l)
  | litUnit (n : NumLit) (u : Denom) : PureS Γ .expr (.litUnit n u)
  /-- A name denoting a constant. -/
  | named {x : String} {d : Decl} : Γ.resolve x = Option.some (.decls [d]) → d.isConst = true →
      PureS Γ .expr (.ident x)
  | tuple {o : Syn (.opt .expr)} {s : Syn (.list (.opt .expr))} : PureS Γ (.opt .expr) o →
      PureS Γ (.list (.opt .expr)) s → PureS Γ .expr (.tuple o s)
  | unary {op : PrefixOp} {x : Syn .expr} : op.pure = true → PureS Γ .expr x →
      PureS Γ .expr (.unaryPrefix op x)
  | binary {e a b : Syn .expr} {k : BinKind} : e.binOp? = Option.some (k, a, b) → PureS Γ .expr a →
      PureS Γ .expr b → PureS Γ .expr e
  | cond {c a b : Syn .expr} : PureS Γ .expr c → PureS Γ .expr a → PureS Γ .expr b →
      PureS Γ .expr (.cond c a b)
  | call {f : Syn .expr} {a : Syn .callArgs} : pureHead Γ f = true → PureS Γ .callArgs a →
      PureS Γ .expr (.call f a)
  | payable {a : Syn .callArgs} : PureS Γ .callArgs a → PureS Γ .expr (.payableConv a)

/-- An expression is a compile-time constant expression. -/
def Pure (Γ : Ctx) (e : Syn .expr) : Prop := PureS Γ .expr e

/-- **Every constant's initializer is compile-time** (solc error 8349). -/
def ConstInitsPure (r : Resolution) : Prop :=
  ∀ d ∈ r.unit.decls, d.isConst = true → ∀ e, d.init? = Option.some e →
    Pure (Ctx.forInit r.env d.scope) e

/-! ## Values of named constants -/

/-- A compile-time value with its type: an integer type, or `none` for a
literal's rational type. -/
abbrev TVal := Option IntTy × Q

/-- solc's `ConstantEvaluator::convertType` to an integer type: `none` out of
range, else the value truncated toward zero. -/
def Q.toIntTy? (q : Q) (t : IntTy) : Option Q :=
  if t.lo * (q.den : Int) ≤ q.num ∧ q.num ≤ t.hi * (q.den : Int) then Option.some (Q.ofInt (q.num.tdiv q.den))
  else Option.none

/-- The literal of an integral value. -/
def Q.lit? (q : Q) : Option (Syn .expr) :=
  if q.isInt then
    if 0 ≤ q.toInt then Option.some (.lit (.num (.dec q.toInt.toNat 0 0)))
    else Option.some (.unaryPrefix .neg (.lit (.num (.dec (-q.toInt).toNat 0 0))))
  else Option.none

/-- The binary operators `Syn.const` folds. -/
inductive ConstOp where
  | add | sub | mul | div | mod | exp | shl | sar | bitAnd | bitOr | bitXor
  deriving DecidableEq, Repr

/-- The expression of an operator on two operands. -/
def ConstOp.mk : ConstOp → Syn .expr → Syn .expr → Syn .expr
  | .add, a, b => .addSub .add a b
  | .sub, a, b => .addSub .sub a b
  | .mul, a, b => .mulDivMod .mul a b
  | .div, a, b => .mulDivMod .div a b
  | .mod, a, b => .mulDivMod .mod a b
  | .exp, a, b => .exp a b
  | .shl, a, b => .shift .shl a b
  | .sar, a, b => .shift .sar a b
  | .bitAnd, a, b => .bitAnd a b
  | .bitOr, a, b => .bitOr a b
  | .bitXor, a, b => .bitXor a b

/-- The operator and operands of a binary expression `Syn.const` folds. -/
def Syn.constBin? : Syn .expr → Option (ConstOp × Syn .expr × Syn .expr)
  | .addSub .add a b => Option.some (.add, a, b)
  | .addSub .sub a b => Option.some (.sub, a, b)
  | .mulDivMod .mul a b => Option.some (.mul, a, b)
  | .mulDivMod .div a b => Option.some (.div, a, b)
  | .mulDivMod .mod a b => Option.some (.mod, a, b)
  | .exp a b => Option.some (.exp, a, b)
  | .shift .shl a b => Option.some (.shl, a, b)
  | .shift .sar a b => Option.some (.sar, a, b)
  | .bitAnd a b => Option.some (.bitAnd, a, b)
  | .bitOr a b => Option.some (.bitOr, a, b)
  | .bitXor a b => Option.some (.bitXor, a, b)
  | _ => Option.none

/-- The type of an operation with at least one typed operand
(`binaryOperatorResult` on integer types): the wider of two integer types
when one converts to the other, an integer type and a constant that fits
it; for `**` and shifts, the left operand's type. -/
def ConstOp.resultTy : ConstOp → TVal → TVal → Option IntTy
  | .exp, (Option.some t, _), _ | .shl, (Option.some t, _), _ | .sar, (Option.some t, _), _ =>
    Option.some t
  | .exp, _, _ | .shl, _, _ | .sar, _, _ => Option.none
  | _, (Option.some t₁, _), (Option.some t₂, _) =>
    if t₁.implicit t₂ then Option.some t₂ else if t₂.implicit t₁ then Option.some t₁ else Option.none
  | _, (Option.some t, _), (Option.none, q) => if q.FitsInt t then Option.some t else Option.none
  | _, (Option.none, q), (Option.some t, _) => if q.FitsInt t then Option.some t else Option.none
  | _, (Option.none, _), (Option.none, _) => Option.none

mutual

/-- **Compile-time evaluation** of a constant expression in a scope, solc's
`ConstantEvaluator`: a literal-only expression folds exactly (S01's
`Syn.const`); a named integer constant has its declared type; an operation
with a typed operand takes the result type, folds exactly, then converts
(`Q.toIntTy?`: out of range is no value, a fraction is truncated). -/
inductive TEval (E : Env) : Option String → Syn .expr → TVal → Prop where
  | rational {scope : Option String} {e : Syn .expr} {q : Q} : e.const = Option.some q →
      TEval E scope e (Option.none, q)
  | named {scope : Option String} {x : String} {t : IntTy} {q : Q} : NamedConst E scope x t q →
      TEval E scope (.ident x) (Option.some t, q)
  | paren {scope : Option String} {e : Syn .expr} {t : IntTy} {q : Q} : TEval E scope e (Option.some t, q) →
      TEval E scope (.tuple (.some e) .nil) (Option.some t, q)
  | unary {scope : Option String} {x : Syn .expr} {op : PrefixOp} {t : IntTy} {q r r' : Q} {l : Syn .expr} :
      (op = .neg ∨ op = .bitNot) → TEval E scope x (Option.some t, q) → q.lit? = Option.some l →
      (Syn.unaryPrefix op l).const = Option.some r → r.toIntTy? t = Option.some r' →
      TEval E scope (.unaryPrefix op x) (Option.some t, r')
  | binary {scope : Option String} {e a b : Syn .expr} {k : ConstOp} {va vb : TVal} {t : IntTy}
      {la lb : Syn .expr} {r r' : Q} :
      e.constBin? = Option.some (k, a, b) → TEval E scope a va → TEval E scope b vb →
      (va.1.isSome || vb.1.isSome) = true → k.resultTy va vb = Option.some t →
      va.2.lit? = Option.some la → vb.2.lit? = Option.some lb → (k.mk la lb).const = Option.some r →
      r.toIntTy? t = Option.some r' → TEval E scope e (Option.some t, r')

/-- **The value of a named integer constant**: its initializer's value,
converted to its declared type.  A least fixpoint: a cyclic definition has
no value. -/
inductive NamedConst (E : Env) : Option String → String → IntTy → Q → Prop where
  | mk {scope : Option String} {x : String} {d : Decl} {e : Syn .expr} {t : IntTy} {v : TVal} {q : Q} :
      E.lookup scope x = [d] → d.isConst = true → d.init? = Option.some e →
      d.varTy E = Option.some (.int t) → TEval E d.scope e v → v.2.toIntTy? t = Option.some q →
      NamedConst E scope x t q

end

/-- The value of a constant expression, named constants included. -/
def ConstVal (E : Env) (scope : Option String) (e : Syn .expr) (q : Q) : Prop :=
  ∃ t, TEval E scope e (t, q)

/-- **An array length**: absent (dynamic), or a constant expression, named
constants included, with a positive integral value (solc: "Invalid array
length" otherwise). -/
inductive ArrayLenOK (E : Env) (scope : Option String) : Syn (.opt .expr) → Option Nat → Prop where
  | dynamic : ArrayLenOK E scope .none Option.none
  | static {e : Syn .expr} {q : Q} : ConstVal E scope e q → q.isInt = true → 0 < q.toInt →
      ArrayLenOK E scope (.some e) (Option.some q.toInt.toNat)

/-! ## Acyclic constants -/

/-- The constants a constant's initializer names, as `(scope, name)` nodes. -/
def Env.constDeps (E : Env) (n : Option String × String) : List (Option String × String) :=
  match E.lookup n.1 n.2 with
  | [d] =>
    if d.isConst then
      match d.init? with
      | Option.some e => e.paths.filterMap fun p =>
          match E.lookupPath d.scope p with
          | [d'] => if d'.isConst then Option.some (d'.scope, d'.name) else Option.none
          | _ => Option.none
      | Option.none => []
    else []
  | _ => []

/-- One step or more of `constDeps`. -/
inductive DepPath (E : Env) : Option String × String → Option String × String → Prop where
  | step {a b : Option String × String} : b ∈ E.constDeps a → DepPath E a b
  | trans {a b c : Option String × String} : b ∈ E.constDeps a → DepPath E b c → DepPath E a c

/-- **No cyclic constant** (solc: "The value of the constant … has a cyclic
dependency via …"): no constant depends on itself. -/
def ConstsAcyclic (E : Env) : Prop :=
  ∀ d ∈ E.decls, d.isConst = true → ¬ DepPath E (d.scope, d.name) (d.scope, d.name)

end Solidity.Source
