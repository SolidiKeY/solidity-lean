import Solidity.Source.Typing


namespace Solidity.Source

def Syn.opAliases : {c : Cat} → Syn c → List (IdPath × UserOp)
  | _, .cons x xs => x.opAliases ++ xs.opAliases
  | _, .usingAlias fn (Option.some op) => [(fn, op)]
  | _, _ => []

def Syn.usingOps : {c : Cat} → Syn c → List (IdPath × UserOp × Syn .typeName)
  | _, .unit xs => xs.usingOps
  | _, .cons x xs => x.usingOps ++ xs.usingOps
  | _, .topPart p => p.usingOps
  | _, .usingPart u => u.usingOps
  | _, .usingAliases a as (.some t) true => (a.opAliases ++ as.opAliases).map fun (f, op) => (f, op, t)
  | _, _ => []

def UserOp.isCompare : UserOp → Bool
  | .eq | .ne | .lt | .gt | .le | .ge => true
  | _ => false

def UserOp.unaryOK : UserOp → Bool
  | .sub | .bitNot => true
  | _ => false

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

def Syn.userUnOp? : Syn .expr → Option (UserOp × Syn .expr)
  | .unaryPrefix .neg x => Option.some (.sub, x)
  | .unaryPrefix .bitNot x => Option.some (.bitNot, x)
  | _ => Option.none

def UserOp.sigOK (op : UserOp) (T : DeclName) (n : Nat) (ps rs : List STy) : Bool :=
  STy.sameList ps (List.replicate n (.udvt T)) &&
    STy.sameList rs [if op.isCompare then .bool else .udvt T]

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

def Decl.underlying? (d : Decl) : Option Elem :=
  match d.kind, d.top, d.node with
  | .udvt, _, .udvt _ el => Option.some el
  | _, _, _ => Option.none

inductive UdvtTyped (Γ : Ctx) (u : Syn .unit) : Syn .expr → STy → Prop where
  | binOp {e a b : Syn .expr} {op : UserOp} {T : DeclName} {d : Decl} {ps : List STy} {τ : STy} :
      e.userBinOp? = Option.some (op, a, b) → HasType Γ a (.udvt T) → HasType Γ b (.udvt T) →
      opBindings Γ.env u T op 2 = [d] → d.fnSig Γ.env = Option.some (ps, [τ]) → UdvtTyped Γ u e τ
  | unOp {e x : Syn .expr} {op : UserOp} {T : DeclName} {d : Decl} {ps : List STy} {τ : STy} :
      e.userUnOp? = Option.some (op, x) → op.unaryOK = true → HasType Γ x (.udvt T) →
      opBindings Γ.env u T op 1 = [d] → d.fnSig Γ.env = Option.some (ps, [τ]) → UdvtTyped Γ u e τ
  | wrap {T : String} {x : Syn .expr} {d : Decl} {el : Elem} {σ : STy} :
      Γ.resolve T = Option.some (.decls [d]) → d.underlying? = Option.some el → HasType Γ x σ →
      σ.implicit Γ.isBase Γ.mapFree (el.ty .memory) = true →
      UdvtTyped Γ u (.call (.member (.ident T) "wrap") (.positional (.cons x .nil))) (.udvt ⟨d.scope, d.name⟩)
  | unwrap {T : String} {x : Syn .expr} {d : Decl} {el : Elem} :
      Γ.resolve T = Option.some (.decls [d]) → d.underlying? = Option.some el →
      HasType Γ x (.udvt ⟨d.scope, d.name⟩) →
      UdvtTyped Γ u (.call (.member (.ident T) "unwrap") (.positional (.cons x .nil))) (el.ty .memory)


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

def Decl.isPure (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ m _ _ _ _ _ => m == Option.some .pure
  | _, _, _ => false

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

def UsingOpsOK (E : Env) (u : Syn .unit) : Prop := ∀ use ∈ u.opUsesAt true, opUseOK E use = true

end Solidity.Source
