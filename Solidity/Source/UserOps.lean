import Solidity.Source.Typing

/-!
# User-defined value types: operators, `wrap`, `unwrap` (G13)

S01 types no operation on a user-defined value type (`type T is V;`):
`STy.isNumeric (.udvt _)` is false, and `T.wrap`/`T.unwrap` have no rule.
This module states them as relations over a unit's syntax.

**Operators** (solc 0.8.19+).  A file-level `using {f as op, …} for T
global;` binds the operator `op` on `T` to the free function `f`
(`Syn.usingOps`; solc admits operator bindings only in a global, file-level
directive).  A binary operation `a op b` with both operands of type `T`
calls the bound function of two parameters `(T, T)`; unary `-`/`~` call one
of one parameter `(T)`.  The result is the function's single return type:
`T` for arithmetic and bitwise operators, `bool` for comparisons (solc
requires exactly these signatures, and `pure`).  `opBindings` lists the
binding functions of an operator, type and arity whose signature has that
shape; an operation is typed only when exactly one exists (solc refuses a
duplicate binding).  `UsingOpsOK` refuses a unit with any ill-formed binding
(wrong signature, not `pure`, not global, not at file level), as solc does,
so `opBindings`' filter never hides one in an accepted unit.

**Conversions.**  `T.wrap(x)` takes the underlying type (any argument that
converts implicitly to it) to `T`; `T.unwrap(x)` takes `T` to the
underlying type.
-/

namespace Solidity.Source

/-- The `{f as op}` pairs of a `using` directive. -/
def Syn.opAliases : {c : Cat} → Syn c → List (IdPath × UserOp)
  | _, .cons x xs => x.opAliases ++ xs.opAliases
  | _, .usingAlias fn (Option.some op) => [(fn, op)]
  | _, _ => []

/-- The operator bindings of a unit: global, file-level `using {f as op}
for T global;` directives. -/
def Syn.usingOps : {c : Cat} → Syn c → List (IdPath × UserOp × Syn .typeName)
  | _, .unit xs => xs.usingOps
  | _, .cons x xs => x.usingOps ++ xs.usingOps
  | _, .topPart p => p.usingOps
  | _, .usingPart u => u.usingOps
  | _, .usingAliases a as (.some t) true => (a.opAliases ++ as.opAliases).map fun (f, op) => (f, op, t)
  | _, _ => []

/-- Comparison operators return `bool`. -/
def UserOp.isCompare : UserOp → Bool
  | .eq | .ne | .lt | .gt | .le | .ge => true
  | _ => false

/-- Operators that may be unary: `-` and `~`. -/
def UserOp.unaryOK : UserOp → Bool
  | .sub | .bitNot => true
  | _ => false

/-- The user operator of a binary expression. -/
def Syn.userBinOp? : Syn .expr → Option (UserOp × Syn .expr × Syn .expr)
  | .addSub .add a b => Option.some (.add, a, b)
  | .addSub .sub a b => Option.some (.sub, a, b)
  | .mulDivMod .mul a b => Option.some (.mul, a, b)
  | .mulDivMod .div a b => Option.some (.div, a, b)
  | .mulDivMod .mod a b => Option.some (.mod, a, b)
  | .bitAnd a b => Option.some (.bitAnd, a, b)
  | .bitOr a b => Option.some (.bitOr, a, b)
  | .bitXor a b => Option.some (.bitXor, a, b)
  | .equality .eq a b => Option.some (.eq, a, b)
  | .equality .ne a b => Option.some (.ne, a, b)
  | .order .lt a b => Option.some (.lt, a, b)
  | .order .gt a b => Option.some (.gt, a, b)
  | .order .le a b => Option.some (.le, a, b)
  | .order .ge a b => Option.some (.ge, a, b)
  | _ => Option.none

/-- The user operator of a unary expression. -/
def Syn.userUnOp? : Syn .expr → Option (UserOp × Syn .expr)
  | .unaryPrefix .neg x => Option.some (.sub, x)
  | .unaryPrefix .bitNot x => Option.some (.bitNot, x)
  | _ => Option.none

/-- The signature a binding of `op` on `T` with `n` operands must have. -/
def UserOp.sigOK (op : UserOp) (T : DeclName) (n : Nat) (ps rs : List STy) : Bool :=
  STy.sameList ps (List.replicate n (.udvt T)) &&
    STy.sameList rs [if op.isCompare then .bool else .udvt T]

/-- The functions bound to `op` on `T` with `n` operands and the required
signature. -/
def opBindings (E : Env) (u : Syn .unit) (T : DeclName) (op : UserOp) (n : Nat) : List Decl :=
  u.usingOps.flatMap fun (f, op', t) =>
    if op' = op ∧ (match t.ty E Option.none .memory with
        | Option.some (.udvt T') => T' == T
        | _ => false) = true then
      (E.lookupPath Option.none f).filter fun d =>
        d.kind == .function && d.top &&
          match d.fnSig E with
          | Option.some (ps, rs) => op.sigOK T n ps rs
          | Option.none => false
    else []

/-- The underlying type of a user-defined value type declaration. -/
def Decl.underlying? (d : Decl) : Option Elem :=
  match d.kind, d.top, d.node with
  | .udvt, _, .udvt _ el => Option.some el
  | _, _, _ => Option.none

/-- **Typing of user-defined value type operations** in unit `u`. -/
inductive UdvtTyped (Γ : Ctx) (u : Syn .unit) : Syn .expr → STy → Prop where
  /-- `a op b` on two operands of type `T`: the unique bound function's result. -/
  | binOp {e a b : Syn .expr} {op : UserOp} {T : DeclName} {d : Decl} {ps : List STy} {τ : STy} :
      e.userBinOp? = Option.some (op, a, b) → HasType Γ a (.udvt T) → HasType Γ b (.udvt T) →
      opBindings Γ.env u T op 2 = [d] → d.fnSig Γ.env = Option.some (ps, [τ]) → UdvtTyped Γ u e τ
  /-- `-x`, `~x` on an operand of type `T`. -/
  | unOp {e x : Syn .expr} {op : UserOp} {T : DeclName} {d : Decl} {ps : List STy} {τ : STy} :
      e.userUnOp? = Option.some (op, x) → op.unaryOK = true → HasType Γ x (.udvt T) →
      opBindings Γ.env u T op 1 = [d] → d.fnSig Γ.env = Option.some (ps, [τ]) → UdvtTyped Γ u e τ
  /-- `T.wrap(x)`: the underlying type, implicitly converted, to `T`. -/
  | wrap {T : String} {x : Syn .expr} {d : Decl} {el : Elem} {σ : STy} :
      Γ.resolve T = Option.some (.decls [d]) → d.underlying? = Option.some el → HasType Γ x σ →
      σ.implicit Γ.isBase (el.ty .memory) = true →
      UdvtTyped Γ u (.call (.member (.ident T) "wrap") (.positional (.cons x .nil))) (.udvt ⟨d.scope, d.name⟩)
  /-- `T.unwrap(x)`: `T` to the underlying type. -/
  | unwrap {T : String} {x : Syn .expr} {d : Decl} {el : Elem} :
      Γ.resolve T = Option.some (.decls [d]) → d.underlying? = Option.some el →
      HasType Γ x (.udvt ⟨d.scope, d.name⟩) →
      UdvtTyped Γ u (.call (.member (.ident T) "unwrap") (.positional (.cons x .nil))) (el.ty .memory)

/-! ## Well-formed operator bindings -/

/-- Every operator binding of a unit: `(f, op, T, global, file level)`, from
`using` directives at file level and in contracts and libraries. -/
def Syn.opUsesAt (top : Bool) : {c : Cat} → Syn c → List (IdPath × UserOp × Option (Syn .typeName) × Bool × Bool)
  | _, .unit xs => xs.opUsesAt true
  | _, .cons x xs => x.opUsesAt top ++ xs.opUsesAt top
  | _, .topPart p => p.opUsesAt true
  | _, .contract _ _ _ _ body => body.opUsesAt false
  | _, .library _ body => body.opUsesAt false
  | _, .usingPart u => u.opUsesAt top
  | _, .usingAliases a as (.some t) g => (a.opAliases ++ as.opAliases).map fun (f, op) => (f, op, Option.some t, g, top)
  | _, .usingAliases a as .none g => (a.opAliases ++ as.opAliases).map fun (f, op) => (f, op, Option.none, g, top)
  | _, _ => []

/-- Whether a function declaration is `pure`. -/
def Decl.isPure (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ m _ _ _ _ _ => m == Option.some .pure
  | _, _, _ => false

/-- One operator binding is well formed (solc's `TypeChecker` on `using`
directives with operators): in a global, file-level directive for a
user-defined value type `T`, naming a free `pure` function of signature
`(T, T) → T` (`bool` for comparisons), or `(T) → T` for unary `-`/`~`. -/
def opUseOK (E : Env) : IdPath × UserOp × Option (Syn .typeName) × Bool × Bool → Bool
  | (f, op, Option.some t, true, true) =>
    match t.ty E Option.none .memory with
    | Option.some (.udvt T) =>
      match E.lookupPath Option.none f with
      | [d] =>
        d.kind == .function && d.top && d.isPure &&
          match d.fnSig E with
          | Option.some (ps, rs) => op.sigOK T 2 ps rs || (op.unaryOK && op.sigOK T 1 ps rs)
          | Option.none => false
      | _ => false
    | _ => false
  | _ => false

/-- **Every operator binding of the unit is well formed**; otherwise solc
refuses the unit ("Wrong parameters in operator definition", "User-defined
operators can only be defined in a global 'using for' directive", …). -/
def UsingOpsOK (E : Env) (u : Syn .unit) : Prop := ∀ use ∈ u.opUsesAt true, opUseOK E use = true

end Solidity.Source
