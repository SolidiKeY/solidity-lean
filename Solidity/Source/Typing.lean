import Solidity.Source.Types
import Solidity.Source.Resolve

/-!
# Static typing (S01)

The typing judgments of Solidity 0.8.38 over S00's syntax, with name
resolution (`Solidity/Source/Resolve.lean`), compile-time constants
(`Solidity/Source/Const.lean`) and conversions (`Solidity/Source/Types.lean`):

- `Syn.tys`: the elaboration of type names (and parameter lists) to `STy`,
  user types resolved in scope, array lengths folded as constants;
- `Ctx`: the typing context: the environment, the enclosing contract, the
  locals (innermost first) and the return types of the enclosing function;
- `HasType Γ e τ` (with `HasTypes` for argument lists and `HasSlots` for
  tuple slots): expression typing; a constant expression has its exact
  rational type (`HasType.const`) and meets a typed context only through a
  conversion;
- `StmtOK`/`ItemsOK`: statement and block typing, threading the locals a
  declaration adds.

**Fixed point (second round).** `-e` is typed at `ufixed` too (solc's type
checker accepts it; it panics at run time unless `e` is 0); shifts and `**`
on fixed-point operands have no rule (solc reaches an internal assertion, so
no such program compiles); a fixed-point and an integer operand meet at the
fixed-point type only when the integer range fits (`FixTy.intImplicit`).

**Coverage.** `exprCoverage` classifies every expression constructor of
S00: typed here, with a derivation in `Solidity/Source/TypingExamples.lean`,
or deferred to a named later stage with the reason.
-/

namespace Solidity.Source

/-! ## Elaborating type names -/

/-- The last component of a path (qualified names resolve by their last
component in scope; library- and contract-qualified lookup is the same
lookup in the qualifier's scope). -/
def IdPath.last (p : IdPath) : String := p.tail.getLast?.getD p.head

/-- The type a user-defined type name denotes in a location. -/
def Env.userTy (E : Env) (scope : Option String) (loc : DataLoc) (p : IdPath) : Option STy :=
  match E.lookup scope p.last with
  | [d] =>
    match d.kind with
    | .struct => Option.some (.struct loc ⟨d.scope, d.name⟩)
    | .enum => Option.some (.enum ⟨d.scope, d.name⟩)
    | .udvt => Option.some (.udvt ⟨d.scope, d.name⟩)
    | .contract | .interface => Option.some (.contract ⟨d.scope, d.name⟩)
    | _ => Option.none
  | _ => Option.none

/-- The type of a mapping key. -/
def Env.keyTy (E : Env) (scope : Option String) : MapKey → Option STy
  | .elem e _ => Option.some (e.ty .memory)
  | .path p => E.userTy scope .memory p

/-- An array length: a constant non-negative integer. -/
def arrayLen : Syn (.opt .expr) → Option (Option Nat)
  | .none => Option.some Option.none
  | .some e =>
    match e.const with
    | Option.some q => if q.isInt ∧ 0 < q.toInt then Option.some (Option.some q.toInt.toNat) else Option.none
    | Option.none => Option.none

/-- **Type elaboration**: the types a type name or a parameter list
denotes, in a default location (a parameter's own location overrides it;
mapping values are in storage). -/
def Syn.tys (E : Env) (scope : Option String) (loc : DataLoc) : {c : Cat} → Syn c → Option (List STy)
  | _, .elem e => Option.some [e.ty loc]
  | _, .userType p => (E.userTy scope loc p).map ([·])
  | _, .array t len =>
    match t.tys E scope loc, arrayLen len with
    | Option.some [τ], Option.some n => Option.some [.array loc τ n]
    | _, _ => Option.none
  | _, .mapping k _ v _ =>
    match E.keyTy scope k, v.tys E scope .storage with
    | Option.some τk, Option.some [τv] => Option.some [.mapping τk τv]
    | _, _ => Option.none
  | _, .fnType ps vis mutability rs =>
    match ps.tys E scope .memory, rs.tys E scope .memory with
    | Option.some a, Option.some r => Option.some [.fn (vis == Option.some .external) a r mutability]
    | _, _ => Option.none
  | _, .param t l _ => t.tys E scope (l.getD loc)
  | _, .eventParam t _ _ => t.tys E scope .memory
  | _, .errorParam t _ => t.tys E scope .memory
  | _, .varDecl t l _ => t.tys E scope (l.getD loc)
  | _, .nil => Option.some []
  | _, .cons x xs =>
    match x.tys E scope loc, xs.tys E scope loc with
    | Option.some a, Option.some b => Option.some (a ++ b)
    | _, _ => Option.none
  | _, _ => Option.none

/-- The single type of a type name. -/
def Syn.ty (E : Env) (scope : Option String) (loc : DataLoc) (t : Syn .typeName) : Option STy :=
  match t.tys E scope loc with
  | Option.some [τ] => Option.some τ
  | _ => Option.none

/-- The declared type of a state variable (in storage) or constant. -/
def Decl.varTy (E : Env) (d : Decl) : Option STy :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar t _ _ _ _ _ _ => t.ty E d.scope .storage
  | .constant, _, .constant t _ _ => t.ty E d.scope .memory
  | _, _, _ => Option.none

/-- Whether a state variable may be assigned (not `constant`/`immutable`). -/
def Decl.mutable (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar _ _ Option.none _ _ _ _ => true
  | _, _, _ => false

/-- The parameter and return types of a function declaration. -/
def Decl.fnSig (E : Env) (d : Decl) : Option (List STy × List STy) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ ps _ _ _ _ _ rs _ =>
    match ps.tys E d.scope .memory, rs.tys E d.scope .memory with
    | Option.some a, Option.some r => Option.some (a, r)
    | _, _ => Option.none
  | _, _, _ => Option.none

/-- The parameter types of an event or error declaration. -/
def Decl.paramTys (E : Env) (d : Decl) : Option (List STy) :=
  match d.kind, d.top, d.node with
  | .event, _, .event _ ps _ => ps.tys E d.scope .memory
  | .error, _, .error _ ps => ps.tys E d.scope .memory
  | _, _, _ => Option.none

/-! ## Builtins -/

/-- `bytes32`, `bytes20`. -/
def STy.bytes32 : STy := .fixedBytes 32 (by decide)
def STy.bytes20 : STy := .fixedBytes 20 (by decide)

/-- The type of an admitted magic member. -/
def Builtin.memberTy : Builtin → String → Option STy
  | .msg, "sender" => Option.some (.address false)
  | .msg, "value" => Option.some (.int IntTy.u256)
  | .block, "timestamp" => Option.some (.int IntTy.u256)
  | _, _ => Option.none

/-- Whether a type is a string, by value or literal. -/
def STy.isStringy : STy → Bool
  | .string _ | .stringLit _ => true
  | _ => false

/-- The result type of a call of an admitted builtin function on arguments
of the given types. -/
def Builtin.callTy (isBase : DeclName → DeclName → Bool) : Builtin → List STy → Option STy
  | .require, [c] | .assert, [c] => if c matches .bool then Option.some (.tuple []) else Option.none
  | .require, [c, m] =>
    if (c matches .bool) && m.isStringy then Option.some (.tuple []) else Option.none
  | .revert, [] => Option.some (.tuple [])
  | .revert, [m] => if m.isStringy then Option.some (.tuple []) else Option.none
  | .keccak256, [b] => if b.implicit isBase (.bytes .memory) then Option.some .bytes32 else Option.none
  | .sha256, [b] => if b.implicit isBase (.bytes .memory) then Option.some .bytes32 else Option.none
  | .ripemd160, [b] => if b.implicit isBase (.bytes .memory) then Option.some .bytes20 else Option.none
  | .addmod, [x, y, k] | .mulmod, [x, y, k] =>
    if [x, y, k].all (·.implicit isBase (.int IntTy.u256)) then Option.some (.int IntTy.u256)
    else Option.none
  | .ecrecover, [h, v, r, s] =>
    if h.implicit isBase .bytes32 && v.implicit isBase (.int IntTy.u8) &&
      r.implicit isBase .bytes32 && s.implicit isBase .bytes32 then Option.some (.address false)
    else Option.none
  | _, _ => Option.none

/-! ## Contexts -/

/-- A typing context. -/
structure Ctx where
  env : Env
  scope : Option String
  /-- Locals and parameters, innermost first. -/
  locals : List (String × STy)
  /-- The return types of the enclosing function. -/
  rets : List STy := []

namespace Ctx

/-- The inheritance relation: `d'` is `d` or one of its bases. -/
def isBase (Γ : Ctx) (d d' : DeclName) : Bool :=
  d == d' || (d.scope == Option.none && d'.scope == Option.none &&
    ((Γ.env.linearize d.name).getD []).contains d'.name)

/-- What a name denotes here. -/
def resolve (Γ : Ctx) (x : String) : Option Denot :=
  Γ.env.resolve (Γ.locals.map Prod.fst) Γ.scope x

/-- The type of a variable: a local, a state variable or constant, or
`this`. -/
def varTy (Γ : Ctx) (x : String) : Option STy :=
  match Γ.resolve x with
  | Option.some (.loc i) => (Γ.locals[i]?).map Prod.snd
  | Option.some (.decls [d]) => d.varTy Γ.env
  | Option.some (.builtin .this) => Γ.scope.map fun c => .contract ⟨Option.none, c⟩
  | _ => Option.none

/-- Whether a name is an assignable variable: a local, or a state variable
neither `constant` nor `immutable`. -/
def assignable (Γ : Ctx) (x : String) : Bool :=
  match Γ.resolve x with
  | Option.some (.loc _) => true
  | Option.some (.decls [d]) => d.mutable
  | _ => false

/-- The function declarations a name denotes. -/
def functions (Γ : Ctx) (x : String) : List Decl :=
  match Γ.resolve x with
  | Option.some (.decls ds) => ds.filter (·.kind == .function)
  | _ => []

/-- The contract or enum a conversion's callee names. -/
def convTarget (Γ : Ctx) (x : String) : Option STy :=
  match Γ.resolve x with
  | Option.some (.decls [d]) =>
    match d.kind with
    | .contract | .interface => Option.some (.contract ⟨d.scope, d.name⟩)
    | .enum => Option.some (.enum ⟨d.scope, d.name⟩)
    | _ => Option.none
  | _ => Option.none

/-- The event or error declarations a name denotes. -/
def declsOf (Γ : Ctx) (k : DeclKind) (x : String) : List Decl :=
  match Γ.resolve x with
  | Option.some (.decls ds) => ds.filter (·.kind == k)
  | _ => []

/-- The context with one more local. -/
def push (Γ : Ctx) (x : String) (τ : STy) : Ctx := { Γ with locals := (x, τ) :: Γ.locals }

end Ctx

/-! ## Operand rules -/

/-- The type two operands meet at: one converts implicitly to the other. -/
def STy.common? (isBase : DeclName → DeclName → Bool) (a b : STy) : Option STy :=
  if a.implicit isBase b then Option.some b
  else if b.implicit isBase a then Option.some a else Option.none

/-- Numbers: integers and fixed-point values (`+ - * / %`, order). -/
def STy.isNumeric : STy → Bool
  | .int _ | .fixed _ => true
  | _ => false

/-- Integers (bitwise operations). -/
def STy.isInt : STy → Bool
  | .int _ => true
  | _ => false

/-- An unsigned integer, or a non-negative integral constant: a shift
amount or an exponent. -/
def STy.isAmount : STy → Bool
  | .int t => !t.signed
  | .rational q => q.isInt && decide (0 ≤ q.toInt)
  | _ => false

/-- Ordered types besides numbers: `bytesN`, addresses, enums. -/
def STy.isOrdered : STy → Bool
  | .int _ | .fixed _ | .fixedBytes _ _ | .address _ | .enum _ => true
  | _ => false

/-- Types with `==`: the value types except function types of internal
visibility (`fn false`). -/
def STy.hasEq : STy → Bool
  | .int _ | .fixed _ | .fixedBytes _ _ | .address _ | .enum _ | .bool | .contract _ => true
  | .fn ext _ _ _ => ext
  | _ => false

/-- An index: an unsigned integer, or a constant that fits `uint256`. -/
def STy.isIndex : STy → Bool
  | .int t => !t.signed
  | .rational q => decide (q.FitsInt IntTy.u256)
  | _ => false

/-- The operator family of a binary expression and its operands. -/
inductive BinKind where
  /-- `+ - * / %`. -/
  | arith
  /-- `& | ^`. -/
  | bit
  | shift
  | exp
  | order
  | eq
  /-- `&&`, `||`. -/
  | logic
  deriving DecidableEq, Repr

/-- The family and operands of a binary operation. -/
def Syn.binOp? : Syn .expr → Option (BinKind × Syn .expr × Syn .expr)
  | .mulDivMod _ a b | .addSub _ a b => Option.some (.arith, a, b)
  | .bitAnd a b | .bitOr a b | .bitXor a b => Option.some (.bit, a, b)
  | .shift _ a b => Option.some (.shift, a, b)
  | .exp a b => Option.some (.exp, a, b)
  | .order _ a b => Option.some (.order, a, b)
  | .equality _ a b => Option.some (.eq, a, b)
  | .and a b | .or a b => Option.some (.logic, a, b)
  | _ => Option.none

/-- The family of a compound assignment operator. -/
def AssignOp.kind? : AssignOp → Option BinKind
  | .assign => Option.none
  | .bitOr | .bitXor | .bitAnd => Option.some .bit
  | .shl | .sar | .shr => Option.some .shift
  | .add | .sub | .mul | .div | .mod => Option.some .arith

/-- The base of an indexed or member lvalue: a variable or a nested
access. -/
def Syn.isLValueBase (Γ : Ctx) : Syn .expr → Bool
  | .ident x => (Γ.varTy x).isSome
  | .index _ (.some _) | .member _ _ => true
  | _ => false

/-- Whether an expression denotes storage or a variable that can be
assigned: an assignable name, or an index or member of a variable (S02
decides which reference it denotes). -/
def Syn.isLValue (Γ : Ctx) : Syn .expr → Bool
  | .ident x => Γ.assignable x
  | .index a (.some _) => a.isLValueBase Γ
  | .member a _ => a.isLValueBase Γ
  | .tuple (.some a) .nil => a.isLValueBase Γ
  | _ => false

/-! ## Expression typing -/

mutual

/-- **Expression typing.** -/
inductive HasType (Γ : Ctx) : Syn .expr → STy → Prop where
  /-- A constant expression has its exact value as its type. -/
  | const {e : Syn .expr} {q : Q} : e.const = Option.some q → HasType Γ e (.rational q)
  | bool (b : Bool) : HasType Γ (.lit (.bool b)) .bool
  | str (bs : List UInt8) : HasType Γ (.lit (.str bs)) (.stringLit bs)
  | hexStr (bs : List UInt8) : HasType Γ (.lit (.hexStr bs)) (.stringLit bs)
  | unicodeStr (bs : List UInt8) : HasType Γ (.lit (.unicodeStr bs)) (.stringLit bs)
  | var {x : String} {τ : STy} : Γ.varTy x = Option.some τ → HasType Γ (.ident x) τ
  | paren {e : Syn .expr} {τ : STy} : HasType Γ e τ → HasType Γ (.tuple (.some e) .nil) τ
  /-- `(a, b, …)` with every slot present. -/
  | tuple {e : Syn .expr} {s : Syn (.list (.opt .expr))} {τ : STy} {τs : List STy} :
      HasType Γ e τ → HasSlots Γ s τs → τs ≠ [] → HasType Γ (.tuple (.some e) s) (.tuple (τ :: τs))
  /-- `-e` on a signed integer. -/
  | neg {e : Syn .expr} {t : IntTy} : HasType Γ e (.int t) → t.signed = true →
      HasType Γ (.unaryPrefix .neg e) (.int t)
  /-- `-e` on any fixed-point type, `ufixed` included (second round). -/
  | negFixed {e : Syn .expr} {f : FixTy} : HasType Γ e (.fixed f) →
      HasType Γ (.unaryPrefix .neg e) (.fixed f)
  | not {e : Syn .expr} : HasType Γ e .bool → HasType Γ (.unaryPrefix .not e) .bool
  | bitNot {e : Syn .expr} {t : IntTy} : HasType Γ e (.int t) → HasType Γ (.unaryPrefix .bitNot e) (.int t)
  /-- `++e`, `--e`, `e++`, `e--` on an assignable number (fixed point: `±1`). -/
  | incDec {e : Syn .expr} {op : PrefixOp} {τ : STy} : op = .inc ∨ op = .dec → e.isLValue Γ = true →
      HasType Γ e τ → τ.isNumeric = true → HasType Γ (.unaryPrefix op e) τ
  | incDecSuffix {e : Syn .expr} {op : SuffixOp} {τ : STy} : e.isLValue Γ = true → HasType Γ e τ →
      τ.isNumeric = true → HasType Γ (.unarySuffix op e) τ
  | delete {e : Syn .expr} {τ : STy} : e.isLValue Γ = true → HasType Γ e τ →
      HasType Γ (.unaryPrefix .delete e) (.tuple [])
  /-- `a ∘ b` for `+ - * / %`: numbers meeting at a common type. -/
  | arith {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.arith, a, b) →
      HasType Γ a τa → HasType Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
      τ.isNumeric = true → HasType Γ e τ
  /-- `a ∘ b` for `& | ^`: integers. -/
  | bit {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.bit, a, b) →
      HasType Γ a τa → HasType Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
      τ.isInt = true → HasType Γ e τ
  /-- `a << b`, `a >> b`: an integer by an unsigned amount, at `a`'s type. -/
  | shift {e a b : Syn .expr} {t : IntTy} {τb : STy} : e.binOp? = Option.some (.shift, a, b) →
      HasType Γ a (.int t) → HasType Γ b τb → τb.isAmount = true → HasType Γ e (.int t)
  /-- `a ** b`: an integer to an unsigned power, at `a`'s type. -/
  | exp {e a b : Syn .expr} {t : IntTy} {τb : STy} : e.binOp? = Option.some (.exp, a, b) →
      HasType Γ a (.int t) → HasType Γ b τb → τb.isAmount = true → HasType Γ e (.int t)
  | order {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.order, a, b) →
      HasType Γ a τa → HasType Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
      τ.isOrdered = true → HasType Γ e .bool
  | eq {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.eq, a, b) →
      HasType Γ a τa → HasType Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
      τ.hasEq = true → HasType Γ e .bool
  /-- A comparison of two constants is a boolean. -/
  | compareConst {e a b : Syn .expr} {k : BinKind} {qa qb : Q} :
      e.binOp? = Option.some (k, a, b) → k = .order ∨ k = .eq → a.const = Option.some qa →
      b.const = Option.some qb → HasType Γ e .bool
  | logic {e a b : Syn .expr} : e.binOp? = Option.some (.logic, a, b) → HasType Γ a .bool →
      HasType Γ b .bool → HasType Γ e .bool
  | cond {c a b : Syn .expr} {τa τb τ : STy} : HasType Γ c .bool → HasType Γ a τa → HasType Γ b τb →
      STy.common? Γ.isBase τa τb = Option.some τ → HasType Γ (.cond c a b) τ
  /-- `a = b`: `b` converts implicitly to `a`'s type. -/
  | assign {a b : Syn .expr} {τ σ : STy} : a.isLValue Γ = true → HasType Γ a τ → HasType Γ b σ →
      σ.implicit Γ.isBase τ = true → HasType Γ (.assign .assign a b) τ
  /-- `a ∘= b`: as `a = a ∘ b`. -/
  | compound {a b : Syn .expr} {op : AssignOp} {k : BinKind} {τ σ : STy} : op.kind? = Option.some k →
      a.isLValue Γ = true → HasType Γ a τ → HasType Γ b σ →
      (match k with
        | .arith => σ.implicit Γ.isBase τ && τ.isNumeric
        | .bit => σ.implicit Γ.isBase τ && τ.isInt
        | _ => τ.isInt && σ.isAmount) = true →
      HasType Γ (.assign op a b) τ
  /-- `a[i]` on an array: its element. -/
  | indexArray {a i : Syn .expr} {l : DataLoc} {τ σ : STy} {n : Option Nat} :
      HasType Γ a (.array l τ n) → HasType Γ i σ → σ.isIndex = true → HasType Γ (.index a (.some i)) τ
  /-- `m[k]` on a mapping: its value. -/
  | indexMapping {a i : Syn .expr} {τk τv σ : STy} : HasType Γ a (.mapping τk τv) → HasType Γ i σ →
      σ.implicit Γ.isBase τk = true → HasType Γ (.index a (.some i)) τv
  /-- `b[i]` on `bytes` or `bytesN`: one byte. -/
  | indexBytes {a i : Syn .expr} {τ σ : STy} : HasType Γ a τ →
      (match τ with | .bytes _ | .fixedBytes _ _ => true | _ => false) = true →
      HasType Γ i σ → σ.isIndex = true → HasType Γ (.index a (.some i)) (.fixedBytes 1 (by decide))
  /-- `x.length` on an array or `bytes` (`uint256`) or a `bytesN` (`uint8`). -/
  | length {a : Syn .expr} {τ : STy} : HasType Γ a τ →
      (match τ with | .array _ _ _ | .bytes _ => true | _ => false) = true →
      HasType Γ (.member a "length") (.int IntTy.u256)
  | lengthBytesN {a : Syn .expr} {n : Nat} {h : 1 ≤ n ∧ n ≤ 32} :
      HasType Γ a (.fixedBytes n h) → HasType Γ (.member a "length") (.int IntTy.u8)
  /-- `T(e)` for an elementary `T`: an explicit conversion. -/
  | convElem {x : Syn .expr} {el : Elem} {h : el ≠ .addressPayable} {σ : STy} : HasType Γ x σ →
      σ.explicit Γ.isBase (el.ty .memory) = true →
      HasType Γ (.call (.elemType el h) (.positional (.cons x .nil))) (el.ty .memory)
  /-- `C(e)`, `E(e)`: an explicit conversion to a contract or enum. -/
  | convUser {x : Syn .expr} {n : String} {τ σ : STy} : Γ.convTarget n = Option.some τ →
      HasType Γ x σ → σ.explicit Γ.isBase τ = true →
      HasType Γ (.call (.ident n) (.positional (.cons x .nil))) τ
  /-- `payable(e)` of an address or contract. -/
  | payable {x : Syn .expr} {σ : STy} : HasType Γ x σ →
      (match σ with | .address _ | .contract _ => true | .rational q => q.num == 0 | _ => false) = true →
      HasType Γ (.payableConv (.positional (.cons x .nil))) (.address true)
  /-- `f(args)` of an internal function: the arguments convert implicitly to
  its parameters; one return is the value, otherwise a tuple. -/
  | callInternal {f : String} {args : Syn (.list .expr)} {d : Decl} {ps rs σs : List STy} :
      d ∈ Γ.functions f → d.fnSig Γ.env = Option.some (ps, rs) → HasTypes Γ args σs →
      σs.length = ps.length → (List.zip σs ps).all (fun p => p.1.implicit Γ.isBase p.2) = true →
      HasType Γ (.call (.ident f) (.positional args)) (match rs with | [r] => r | _ => .tuple rs)

  /-- An admitted magic member: `msg.sender`, `msg.value`, `block.timestamp`. -/
  | magic {g m : String} {b : Builtin} {τ : STy} {feature : String} :
      Γ.resolve g = Option.some (.builtin b) → b.memberStatus m = Option.some (.admitted feature) →
      b.memberTy m = Option.some τ → HasType Γ (.member (.ident g) m) τ
  /-- `a.balance` of an address. -/
  | balance {a : Syn .expr} {p : Bool} : HasType Γ a (.address p) →
      HasType Γ (.member a "balance") (.int IntTy.u256)
  /-- A call of an admitted builtin function (`require`, `assert`, `revert`,
  the hashes, `addmod`/`mulmod`, `ecrecover`). -/
  | builtinCall {f : String} {args : Syn (.list .expr)} {b : Builtin} {σs : List STy} {τ : STy}
      {feature : String} : Γ.resolve f = Option.some (.builtin b) →
      b.status = .admitted feature → HasTypes Γ args σs →
      b.callTy Γ.isBase σs = Option.some τ → HasType Γ (.call (.ident f) (.positional args)) τ

/-- Typing of an argument list. -/
inductive HasTypes (Γ : Ctx) : Syn (.list .expr) → List STy → Prop where
  | nil : HasTypes Γ .nil []
  | cons {e : Syn .expr} {es : Syn (.list .expr)} {τ : STy} {τs : List STy} :
      HasType Γ e τ → HasTypes Γ es τs → HasTypes Γ (.cons e es) (τ :: τs)

/-- Typing of tuple slots, each present. -/
inductive HasSlots (Γ : Ctx) : Syn (.list (.opt .expr)) → List STy → Prop where
  | nil : HasSlots Γ .nil []
  | cons {e : Syn .expr} {es : Syn (.list (.opt .expr))} {τ : STy} {τs : List STy} :
      HasType Γ e τ → HasSlots Γ es τs → HasSlots Γ (.cons (.some e) es) (τ :: τs)

end

/-! ## Statement typing -/

mutual

/-- **Statement typing**: `s` is well typed in `Γ` and leaves the locals
of `Γ'` (a declaration adds one; a block's locals end with it). -/
inductive StmtOK : {k : SCtx} → Ctx → Syn (.stmt k) → Ctx → Prop where
  | expr {k : SCtx} {Γ : Ctx} {e : Syn .expr} {τ : STy} :
      HasType Γ e τ → StmtOK (k := k) Γ (.simpleStmt (.exprStmt e)) Γ
  /-- `T x;` -/
  | declVar {k : SCtx} {Γ : Ctx} {t : Syn .typeName} {l : Option DataLoc} {x : String} {τ : STy} :
      t.ty Γ.env Γ.scope (l.getD .memory) = Option.some τ →
      StmtOK (k := k) Γ (.simpleStmt (.declVar (.varDecl t l x) .none)) (Γ.push x τ)
  /-- `T x = e;`: `e` converts implicitly to `T`. -/
  | declInit {k : SCtx} {Γ : Ctx} {t : Syn .typeName} {l : Option DataLoc} {x : String} {e : Syn .expr}
      {τ σ : STy} : t.ty Γ.env Γ.scope (l.getD .memory) = Option.some τ → HasType Γ e σ →
      σ.implicit Γ.isBase τ = true →
      StmtOK (k := k) Γ (.simpleStmt (.declVar (.varDecl t l x) (.some e))) (Γ.push x τ)
  | block {k : SCtx} {Γ Γ' : Ctx} {b : Syn (.list (.item k))} :
      ItemsOK Γ b Γ' → StmtOK Γ (.blockStmt (.block b)) Γ
  | ifThen {k : SCtx} {Γ Γ₁ : Ctx} {c : Syn .expr} {s : Syn (.stmt k)} :
      HasType Γ c .bool → StmtOK Γ s Γ₁ → StmtOK Γ (.ifStmt c s .none) Γ
  | ifElse {k : SCtx} {Γ Γ₁ Γ₂ : Ctx} {c : Syn .expr} {s t : Syn (.stmt k)} :
      HasType Γ c .bool → StmtOK Γ s Γ₁ → StmtOK Γ t Γ₂ → StmtOK Γ (.ifStmt c s (.some t)) Γ
  | whileLoop {l u : Bool} {Γ Γ₁ : Ctx} {c : Syn .expr} {s : Syn (.stmt ⟨true, u⟩)} :
      HasType Γ c .bool → StmtOK Γ s Γ₁ → StmtOK (k := ⟨l, u⟩) Γ (.whileStmt c s) Γ
  | doWhile {l u : Bool} {Γ Γ₁ : Ctx} {c : Syn .expr} {s : Syn (.stmt ⟨true, u⟩)} :
      StmtOK Γ s Γ₁ → HasType Γ c .bool → StmtOK (k := ⟨l, u⟩) Γ (.doWhile s c) Γ
  /-- `for (; cond; post) s`. -/
  | forLoop {l u : Bool} {Γ Γ₂ : Ctx} {c : Syn (.opt .expr)} {post : Syn (.opt .expr)}
      {s : Syn (.stmt ⟨true, u⟩)} :
      (match c with | .none => True | .some e => HasType Γ e .bool) →
      (match post with | .none => True | .some e => ∃ τ, HasType Γ e τ) →
      StmtOK Γ s Γ₂ → StmtOK (k := ⟨l, u⟩) Γ (.forStmt .none c post s) Γ
  /-- `for (init; cond; post) s`: the init's local is in scope of the rest. -/
  | forInit {l u : Bool} {Γ Γ₁ Γ₂ : Ctx} {i : Syn .simple} {c : Syn (.opt .expr)}
      {post : Syn (.opt .expr)} {s : Syn (.stmt ⟨true, u⟩)} :
      StmtOK (k := ⟨true, u⟩) Γ (.simpleStmt i) Γ₁ →
      (match c with | .none => True | .some e => HasType Γ₁ e .bool) →
      (match post with | .none => True | .some e => ∃ τ, HasType Γ₁ e τ) →
      StmtOK Γ₁ s Γ₂ → StmtOK (k := ⟨l, u⟩) Γ (.forStmt (.some i) c post s) Γ
  | brk {u : Bool} {Γ : Ctx} : StmtOK (k := ⟨true, u⟩) Γ .breakStmt Γ
  | cont {u : Bool} {Γ : Ctx} : StmtOK (k := ⟨true, u⟩) Γ .continueStmt Γ
  /-- `return;` in a function without returns. -/
  | ret {k : SCtx} {Γ : Ctx} : Γ.rets = [] → StmtOK (k := k) Γ (.returnStmt .none) Γ
  /-- `return e;`: `e` converts implicitly to the single return type. -/
  | retVal {k : SCtx} {Γ : Ctx} {e : Syn .expr} {τ σ : STy} : Γ.rets = [τ] → HasType Γ e σ →
      σ.implicit Γ.isBase τ = true → StmtOK (k := k) Γ (.returnStmt (.some e)) Γ
  /-- `emit E(args);`: the arguments convert to an event's parameters. -/
  | emit {k : SCtx} {Γ : Ctx} {ev : String} {args : Syn (.list .expr)} {d : Decl} {ps σs : List STy} :
      d ∈ Γ.declsOf .event ev → d.paramTys Γ.env = Option.some ps → HasTypes Γ args σs →
      σs.length = ps.length → (List.zip σs ps).all (fun p => p.1.implicit Γ.isBase p.2) = true →
      StmtOK (k := k) Γ (.emit (.ident ev) (.positional args)) Γ
  /-- `revert E(args);`: the arguments convert to an error's parameters. -/
  | revertError {k : SCtx} {Γ : Ctx} {er : String} {args : Syn (.list .expr)} {d : Decl}
      {ps σs : List STy} :
      d ∈ Γ.declsOf .error er → d.paramTys Γ.env = Option.some ps → HasTypes Γ args σs →
      σs.length = ps.length → (List.zip σs ps).all (fun p => p.1.implicit Γ.isBase p.2) = true →
      StmtOK (k := k) Γ (.revert (.ident er) (.positional args)) Γ
  /-- The canonical rethrow, of a `bytes memory` variable. -/
  | rethrow {k : SCtx} {Γ : Ctx} {fl : List String} {body : Syn (.list .yulStmt)} {d : String} :
      isRethrow body = true → Γ.varTy d = Option.some (.bytes .memory) →
      (body.paths.map IdPath.last).all (· == d) = true →
      StmtOK (k := k) Γ (.assembly false fl body) Γ

/-- Typing of a block's items, in order. -/
inductive ItemsOK : {k : SCtx} → Ctx → Syn (.list (.item k)) → Ctx → Prop where
  | nil {k : SCtx} {Γ : Ctx} : ItemsOK (k := k) Γ .nil Γ
  | stmt {k : SCtx} {Γ Γ₁ Γ₂ : Ctx} {s : Syn (.stmt k)} {rest : Syn (.list (.item k))} :
      StmtOK Γ s Γ₁ → ItemsOK Γ₁ rest Γ₂ → ItemsOK Γ (.cons (.stmtItem s) rest) Γ₂
  | unchecked {l : Bool} {Γ Γ₁ Γ₂ : Ctx} {b : Syn (.list (.item ⟨l, true⟩))}
      {rest : Syn (.list (.item ⟨l, false⟩))} :
      ItemsOK Γ b Γ₁ → ItemsOK Γ rest Γ₂ → ItemsOK Γ (.cons (.uncheckedItem (.block b)) rest) Γ₂

end

/-! ## Laws -/

/-- A typing context's locals only grow along a statement. -/
theorem StmtOK.locals_suffix {k : SCtx} {Γ Γ' : Ctx} {s : Syn (.stmt k)} (h : StmtOK Γ s Γ') :
    ∃ ys, Γ'.locals = ys ++ Γ.locals ∧ Γ'.env = Γ.env ∧ Γ'.scope = Γ.scope ∧ Γ'.rets = Γ.rets := by
  cases h <;> first
    | exact ⟨[], rfl, rfl, rfl, rfl⟩
    | exact ⟨[_], rfl, rfl, rfl, rfl⟩

/-- **Constants have their value as type**: every constant expression is
typed by its exact rational. -/
theorem HasType.of_const {Γ : Ctx} {e : Syn .expr} {q : Q} (h : e.const = Option.some q) :
    HasType Γ e (.rational q) := .const h

/-- **Integer arithmetic stays in range of its operands' common type**: if
both operand types convert implicitly to the result type, a constant
operand that fits its type fits the result. -/
theorem fits_common {q : Q} {t t' : IntTy} (hq : q.FitsInt t) (h : t.implicit t' = true) :
    q.FitsInt t' := hq.implicit h

end Solidity.Source
