import Solidity.Source.WellFormed


namespace Solidity.Source


def Builtin.pure : Builtin → Bool
  | .keccak256 | .sha256 | .ripemd160 | .ecrecover | .addmod | .mulmod | .erc7201 => true
  | _ => false

def pureHead (Γ : Ctx) : Syn .expr → Bool
  | .elemType _ _ => true
  | .ident n =>
    (Γ.convTarget n).isSome ||
      match Γ.resolve n with
      | Option.some (.builtin b) => b.pure
      | _ => false
  | _ => false

def PrefixOp.pure : PrefixOp → Bool
  | .neg | .not | .bitNot => true
  | _ => false

inductive PureS (Γ : Ctx) : (c : Cat) → Syn c → Prop where
  | nil {c : Cat} : PureS Γ (.list c) .nil
  | cons {c : Cat} {x : Syn c} {xs : Syn (.list c)} : PureS Γ c x → PureS Γ (.list c) xs →
      PureS Γ (.list c) (.cons x xs)
  | some {c : Cat} {x : Syn c} : PureS Γ c x → PureS Γ (.opt c) (.some x)
  | positional {es : Syn (.list .expr)} : PureS Γ (.list .expr) es → PureS Γ .callArgs (.positional es)
  | lit (l : Lit) : PureS Γ .expr (.lit l)
  | litUnit (n : NumLit) (u : Denom) : PureS Γ .expr (.litUnit n u)
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

def Pure (Γ : Ctx) (e : Syn .expr) : Prop := PureS Γ .expr e

def ConstInitsPure (r : Resolution) : Prop :=
  ∀ d ∈ r.unit.decls, d.isConst = true → ∀ e, d.init? = Option.some e →
    Pure (Ctx.forInit r.env d.scope) e


abbrev TVal := Option IntTy × Q

def Q.toIntTy? (q : Q) (t : IntTy) : Option Q :=
  if t.lo * (q.den : Int) ≤ q.num ∧ q.num ≤ t.hi * (q.den : Int) then Option.some (Q.ofInt (q.num.tdiv q.den))
  else Option.none

def Q.lit? (q : Q) : Option (Syn .expr) :=
  if q.isInt then
    if 0 ≤ q.toInt then Option.some (.lit (.num (.dec q.toInt.toNat 0 0)))
    else Option.some (.unaryPrefix .neg (.lit (.num (.dec (-q.toInt).toNat 0 0))))
  else Option.none

inductive ConstOp where
  | add | sub | mul | div | mod | exp | shl | sar | bitAnd | bitOr | bitXor
  deriving DecidableEq, Repr

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

inductive NamedConst (E : Env) : Option String → String → IntTy → Q → Prop where
  | mk {scope : Option String} {x : String} {d : Decl} {e : Syn .expr} {t : IntTy} {v : TVal} {q : Q} :
      E.lookup scope x = [d] → d.isConst = true → d.init? = Option.some e →
      d.varTy E = Option.some (.int t) → TEval E d.scope e v → v.2.toIntTy? t = Option.some q →
      NamedConst E scope x t q

end

def ConstVal (E : Env) (scope : Option String) (e : Syn .expr) (q : Q) : Prop :=
  ∃ t, TEval E scope e (t, q)

inductive ArrayLenOK (E : Env) (scope : Option String) : Syn (.opt .expr) → Option Nat → Prop where
  | dynamic : ArrayLenOK E scope .none Option.none
  | static {e : Syn .expr} {q : Q} : ConstVal E scope e q → q.isInt = true → 0 < q.toInt →
      ArrayLenOK E scope (.some e) (Option.some q.toInt.toNat)


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

inductive DepPath (E : Env) : Option String × String → Option String × String → Prop where
  | step {a b : Option String × String} : b ∈ E.constDeps a → DepPath E a b
  | trans {a b c : Option String × String} : b ∈ E.constDeps a → DepPath E b c → DepPath E a c

def ConstsAcyclic (E : Env) : Prop :=
  ∀ d ∈ E.decls, d.isConst = true → ¬ DepPath E (d.scope, d.name) (d.scope, d.name)

end Solidity.Source
