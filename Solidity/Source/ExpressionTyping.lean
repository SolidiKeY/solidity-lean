import Solidity.Source.Types
import Solidity.Source.CalldataLayout
import Solidity.Source.Resolve

/-!
# Static typing (S01)

The typing judgments of Solidity 0.8.38 over S00's syntax, with name
resolution (`Solidity/Source/Resolve.lean`), compile-time constants
(`Solidity/Source/Const.lean`) and conversions (`Solidity/Source/Types.lean`).

**Derivations are data.**  `Typed Γ e τ` (with `TypedArgs`, `TypedSlots` and
the lvalue judgment `LVal`) and `StmtD`/`ItemsD` are `Type`-valued: a
derivation records every resolution (a local's position, a state variable's
or function's declaration, the unique overload), every implicit conversion
and every constant.  `Solidity/Source/Resolved.lean` reads a derivation as
an intrinsically typed term over a context of types (`RExpr`), which is
S01's resolved layer; `HasType` and `StmtOK` are the corresponding `Prop`s
(`Nonempty`).

- `Syn.tys`: the elaboration of type names, parameter lists, struct members
  and event/error parameters to `STy`, user types resolved in scope or in a
  qualifier's scope, array lengths folded as constants, mappings only in
  `storage`, mapping keys only value types;
- `Ctx`: the environment, the enclosing contract, the locals (innermost
  first), the enclosing function's return types, whether `msg.value` may be
  read there, and whether the body is a modifier's;
- `Typed`: expression typing.  A constant expression has its exact rational
  type and meets a typed context only through a conversion; the branches of
  `? :` meet at their *mobile* types (`STy.mobile`), as solc's;
- `StmtD`/`ItemsD`: statement and block typing, threading the locals a
  declaration adds, with solc's data-location rules for local declarations.

**Fixed point (second round).** `-e` is typed at `ufixed` too (solc's type
checker accepts it; it panics at run time unless `e` is 0); shifts and `**`
have no rule at a fixed-point operand (solc reaches an internal assertion, so
no such program compiles); a fixed-point and an integer operand meet at the
fixed-point type only when the integer range fits (`FixTy.intImplicit`).
-/

namespace Solidity.Source

/-! ## Elaborating type names -/

/-- The last component of a path. -/
def IdPath.last (p : IdPath) : String := p.tail.getLast?.getD p.head

/-- The declarations a path names: a plain name by lookup in scope; a
qualified `Q.x` by `x` declared in contract, interface or library `Q` (one
qualifier; deeper paths are not resolved). -/
def Env.lookupPath (E : Env) (scope : Option String) (p : IdPath) : List Decl :=
  match p.tail with
  | [] => E.lookup scope p.head
  | [x] => E.declared (Option.some p.head) x
  | _ => []

/-- The type a user-defined type name denotes in a location. -/
def Env.userTy (E : Env) (scope : Option String) (loc : DataLoc) (p : IdPath) : Option STy :=
  match E.lookupPath scope p with
  | [d] =>
    match d.kind with
    | .struct => Option.some (.struct loc ⟨d.scope, d.name⟩)
    | .enum => Option.some (.enum ⟨d.scope, d.name⟩)
    | .udvt => Option.some (.udvt ⟨d.scope, d.name⟩)
    | .contract | .interface => Option.some (.contract ⟨d.scope, d.name⟩)
    | _ => Option.none
  | _ => Option.none

/-- The type of a mapping key: an elementary type, an enum, a value type
or a contract (solc refuses structs, arrays and mappings as keys). -/
def Env.keyTy (E : Env) (scope : Option String) : MapKey → Option STy
  | .elem e _ => Option.some (e.ty .memory)
  | .path p =>
    match E.userTy scope .memory p with
    | Option.some (.struct _ _) => Option.none
    | τ => τ

/-- An array length: a positive constant integer. -/
def arrayLen : Syn (.opt .expr) → Option (Option Nat)
  | .none => Option.some Option.none
  | .some e =>
    match e.const with
    | Option.some q => if q.isInt ∧ 0 < q.toInt then Option.some (Option.some q.toInt.toNat) else Option.none
    | Option.none => Option.none

/-- **Type elaboration**: the types a type name or a list of parameters,
members or event/error parameters denotes, in a default location (a
parameter's own location overrides it; mappings exist only in storage). -/
def Syn.tys (E : Env) (scope : Option String) (loc : DataLoc) : {c : Cat} → Syn c → Option (List STy)
  | _, .elem e => Option.some [e.ty loc]
  | _, .userType p => (E.userTy scope loc p).map ([·])
  | _, .array t len =>
    match t.tys E scope loc, arrayLen len with
    | Option.some [τ], Option.some n => Option.some [.array loc τ n]
    | _, _ => Option.none
  | _, .mapping k _ v _ =>
    if loc = .storage then
      match E.keyTy scope k, v.tys E scope .storage with
      | Option.some τk, Option.some [τv] => Option.some [.mapping τk τv]
      | _, _ => Option.none
    else Option.none
  | _, .fnType ps vis mutability rs =>
    match ps.tys E scope .memory, rs.tys E scope .memory with
    | Option.some a, Option.some r => Option.some [.fn (vis == Option.some .external) a r mutability]
    | _, _ => Option.none
  | _, .param t l _ => t.tys E scope (l.getD loc)
  | _, .eventParam t _ _ => t.tys E scope .memory
  | _, .errorParam t _ => t.tys E scope .memory
  | _, .structMember t _ => t.tys E scope loc
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

/-- The names of a parameter list, in order. -/
def Syn.paramNames : {c : Cat} → Syn c → List (Option String)
  | _, .cons x xs => x.paramNames ++ xs.paramNames
  | _, .param _ _ n => [n]
  | _, _ => []

/-! ## Declarations -/

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

/-- The visibility of a function declaration. -/
def Decl.fnVis (d : Decl) : Option Visibility :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ v _ _ _ _ _ _ => v
  | _, _, _ => Option.none

/-- Whether a function can be called by its bare name from `scope`: not
`external`, and a `private` one only from its own contract. -/
def Decl.callableFrom (d : Decl) (scope : Option String) : Bool :=
  match d.fnVis with
  | Option.some .external => false
  | Option.some .priv => d.scope == scope
  | _ => true

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

/-- A constant zero (a modulus solc refuses). -/
def STy.isZeroConst : STy → Bool
  | .rational q | .hexConst q _ => q.num == 0
  | _ => false

/-- The result type of a call of an admitted builtin function on arguments
of the given types. -/
def Builtin.callTy (isBase : DeclName → DeclName → Bool) (mapFree : DeclName → Bool) : Builtin → List STy → Option STy
  | .require, [c] | .assert, [c] => if c matches .bool then Option.some (.tuple []) else Option.none
  | .require, [c, m] =>
    if (c matches .bool) && m.isStringy then Option.some (.tuple []) else Option.none
  | .revert, [] => Option.some (.tuple [])
  | .revert, [m] => if m.isStringy then Option.some (.tuple []) else Option.none
  | .keccak256, [b] => if b.implicit isBase mapFree (.bytes .memory) then Option.some .bytes32 else Option.none
  | .sha256, [b] => if b.implicit isBase mapFree (.bytes .memory) then Option.some .bytes32 else Option.none
  | .ripemd160, [b] => if b.implicit isBase mapFree (.bytes .memory) then Option.some .bytes20 else Option.none
  | .addmod, [x, y, k] | .mulmod, [x, y, k] =>
    if [x, y, k].all (·.implicit isBase mapFree (.int IntTy.u256)) && !k.isZeroConst then
      Option.some (.int IntTy.u256)
    else Option.none
  | .ecrecover, [h, v, r, s] =>
    if h.implicit isBase mapFree .bytes32 && v.implicit isBase mapFree (.int IntTy.u8) &&
      r.implicit isBase mapFree .bytes32 && s.implicit isBase mapFree .bytes32 then Option.some (.address false)
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
  /-- Whether `msg.value` may be read: in a `payable`, `internal` or
  `private` function (solc refuses it in a non-payable public one). -/
  msgValue : Bool := true
  /-- Whether the body is a modifier's (where `_` is the placeholder). -/
  inModifier : Bool := false

/-- The inheritance relation: `d'` is `d` or one of its bases. -/
def Env.isBase (E : Env) (d d' : DeclName) : Bool :=
  d == d' || (d.scope == Option.none && d'.scope == Option.none &&
    ((E.linearize d.name).getD []).contains d'.name)

namespace Ctx

/-- The inheritance relation of the environment. -/
abbrev isBase (Γ : Ctx) : DeclName → DeclName → Bool := Γ.env.isBase

/-- What a name denotes here. -/
def resolve (Γ : Ctx) (x : String) : Option Denot :=
  Γ.env.resolve (Γ.locals.map Prod.fst) Γ.scope x

/-- The types of the locals, innermost first. -/
def tys (Γ : Ctx) : List STy := Γ.locals.map Prod.snd

/-- The function declarations a name denotes, callable from here. -/
def functions (Γ : Ctx) (x : String) : List Decl :=
  match Γ.resolve x with
  | Option.some (.decls ds) => ds.filter fun d => d.kind == .function && d.callableFrom Γ.scope
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

/-- The smallest integer type holding an integral constant
(`RationalNumberType::mobileType`): `uintM` for a non-negative one, `intM`
for a negative one. -/
def Q.mobileInt? (q : Q) : Option IntTy :=
  if q.isInt then
    ((List.range 32).filterMap fun k =>
      if h : 8 * (k + 1) % 8 = 0 ∧ 8 ≤ 8 * (k + 1) ∧ 8 * (k + 1) ≤ 256 then
        let t : IntTy := ⟨decide (q.toInt < 0), 8 * (k + 1), h⟩
        if t.lo ≤ q.toInt ∧ q.toInt ≤ t.hi then Option.some t else Option.none
      else Option.none).head?
  else Option.none

/-- The mobile type of an expression's type: an integral constant's
smallest integer type, a string literal's `string memory`; otherwise the
type itself (a fractional constant keeps its rational type, which no
variable has). -/
def STy.mobile : STy → STy
  | .rational q => match q.mobileInt? with
    | Option.some t => .int t
    | Option.none => .rational q
  | .hexConst q n => match q.mobileInt? with
    | Option.some t => .int t
    | Option.none => .hexConst q n
  | .stringLit _ => .string .memory
  | τ => τ

/-- A constant's type: its rational, or a hexadecimal literal's. -/
def STy.isConstTy : STy → Bool
  | .rational _ | .hexConst _ _ => true
  | _ => false

/-- Whether a type is `bytesN`. -/
def STy.isFixedBytes : STy → Bool
  | .fixedBytes _ _ => true
  | _ => false

/-- **The type two operands meet at** (solc's `Type::commonType` with its
mobile-type step): the left operand's mobile type if the right converts to
it, else the right's mobile type if the left converts to it.  Two constants
never meet (they fold), and a constant on the left of a `bytesN` operand
does not either (solc's `RationalNumberType::binaryOperatorResult`). -/
def STy.common? (isBase : DeclName → DeclName → Bool) (mapFree : DeclName → Bool) (a b : STy) : Option STy :=
  if a.isConstTy && (b.isConstTy || b.isFixedBytes) then Option.none
  else if b.implicit isBase mapFree a.mobile then Option.some a.mobile
  else if a.implicit isBase mapFree b.mobile then Option.some b.mobile else Option.none

/-- The type of a shift's or power's left operand: a constant at `uint256`
(`int256` when negative), as solc types `lit << x` and `lit ** x` with a
non-constant amount; any other type as it is. -/
def STy.shiftTy : STy → STy
  | .rational q =>
    if q.FitsInt IntTy.u256 then .int IntTy.u256
    else if q.FitsInt ⟨true, 256, by decide⟩ then .int ⟨true, 256, by decide⟩ else .rational q
  | .hexConst q n =>
    if q.FitsInt IntTy.u256 then .int IntTy.u256
    else if q.FitsInt ⟨true, 256, by decide⟩ then .int ⟨true, 256, by decide⟩ else .hexConst q n
  | τ => τ

/-- Numbers: integers and fixed-point values (`+ - * / %`, order). -/
def STy.isNumeric : STy → Bool
  | .int _ | .fixed _ => true
  | _ => false

/-- Integers. -/
def STy.isInt : STy → Bool
  | .int _ => true
  | _ => false

/-- Bit operands: integers and `bytesN` (`& | ^ ~`, shifted values). -/
def STy.isBits : STy → Bool
  | .int _ | .fixedBytes _ _ => true
  | _ => false

/-- An unsigned integer, or a non-negative integral constant: a shift
amount or an exponent. -/
def STy.isAmount : STy → Bool
  | .int t => !t.signed
  | .rational q | .hexConst q _ => q.isInt && decide (0 ≤ q.toInt)
  | _ => false

/-- Ordered types besides numbers: `bytesN`, addresses, enums. -/
def STy.isOrdered : STy → Bool
  | .int _ | .fixed _ | .fixedBytes _ _ | .address _ | .enum _ => true
  | _ => false

/-- Types with `==`: the value types except internal function types and
contracts (solc: compare `address(c)`). -/
def STy.hasEq : STy → Bool
  | .int _ | .fixed _ | .fixedBytes _ _ | .address _ | .enum _ | .bool => true
  | .fn ext _ _ _ => ext
  | _ => false

/-- An index: an unsigned integer, or a constant that fits `uint256`. -/
def STy.isIndex : STy → Bool
  | .int t => !t.signed
  | .rational q | .hexConst q _ => decide (q.FitsInt IntTy.u256)
  | _ => false

/-- A constant index within a static length (a non-constant index is
checked at run time). -/
def inBounds (σ : STy) (n : Option Nat) : Bool :=
  match σ, n with
  | .rational q, Option.some len | .hexConst q _, Option.some len => decide (q.toInt < len)
  | _, _ => true

/-- Reference types: `bytes`, `string`, arrays, structs, mappings. -/
def STy.isRef : STy → Bool
  | .bytes _ | .string _ | .array _ _ _ | .struct _ _ | .mapping _ _ => true
  | _ => false

/-- A `storage` reference type (a mapping included). -/
def STy.storageRef : STy → Bool
  | .bytes l | .string l | .array l _ _ | .struct l _ => l == .storage
  | .mapping _ _ => true
  | _ => false

/-- solc's location rule for a local declaration: a reference type names
its location (a `mapping` only `storage`), a value type none, and a
`storage` reference is initialized (no dangling storage pointer). -/
def locOK (τ : STy) (l : Option DataLoc) (init : Bool) : Bool :=
  match τ with
  | .mapping _ _ => l == Option.some .storage && init
  | τ => if τ.isRef then l.isSome && (l != Option.some .storage || init) else l.isNone

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

/-- Whether a compound assignment's operand `σ` fits the target `τ`: as
`τ ∘ σ` would for the operator's family. -/
def AssignOp.fits (isBase : DeclName → DeclName → Bool) (mapFree : DeclName → Bool) (op : AssignOp) (σ τ : STy) : Bool :=
  match op.kind? with
  | Option.some .arith => σ.implicit isBase mapFree τ && τ.isNumeric
  | Option.some .bit => σ.implicit isBase mapFree τ && τ.isBits
  | Option.some _ => τ.isBits && σ.isAmount
  | Option.none => false

/-- The type of `length` on a type: `uint256` on arrays and `bytes`,
`uint8` on `bytesN`. -/
def STy.lengthTy : STy → Option STy
  | .array _ _ _ | .bytes _ => Option.some (.int IntTy.u256)
  | .fixedBytes _ _ => Option.some (.int IntTy.u8)
  | _ => Option.none

/-- The value of a call returning `rs`: the single return, or a tuple. -/
def STy.ret (rs : List STy) : STy :=
  match rs with
  | [r] => r
  | _ => .tuple rs

/-- A division or modulo (solc refuses a constant zero divisor: error
1211, "Division by zero"). -/
def Syn.isDivMod : Syn .expr → Bool
  | .mulDivMod .div _ _ | .mulDivMod .mod _ _ => true
  | _ => false

/-- A checksummed 40-digit hexadecimal literal: an address, not a number. -/
def Syn.isAddressLit : {c : Cat} → Syn c → Bool
  | _, .lit (.num (.hex ds true)) => ds.length == 40
  | _, .tuple (.some e) .nil => e.isAddressLit
  | _, _ => false

/-- The compatible bytes length of a hexadecimal literal of `2·len` digits
(`1 ≤ len ≤ 32`), through parentheses; a checksummed 40-digit literal is
an address, not bytes.  solc types such a literal as a constant that also
converts to `bytes{len}` (`STy.hexConst`). -/
def Syn.hexLen? : {c : Cat} → Syn c → Option Nat
  | _, .lit (.num (.hex ds _)) =>
    if ds.length % 2 = 0 ∧ 2 ≤ ds.length ∧ ds.length ≤ 64 ∧ ¬ (39 ≤ ds.length ∧ ds.length ≤ 41) then
      Option.some (ds.length / 2)
    else Option.none
  | _, .tuple (.some e) .nil => e.hexLen?
  | _, _ => Option.none

/-- Whether an lvalue names a local variable (through parentheses): a
local `storage` pointer is rebound by `=`, never copied into, and is not
deleted (solc 7407, "delete cannot be applied to storage pointers"). -/
def Ctx.namesLocal (Γ : Ctx) : {c : Cat} → Syn c → Bool
  | _, .ident x =>
    match Γ.resolve x with
    | Option.some (.loc _) => true
    | _ => false
  | _, .tuple (.some e) .nil => Γ.namesLocal e
  | _, _ => false

/-- A `calldata` reference type. -/
def STy.calldataRef : STy → Bool
  | .bytes l | .string l | .array l _ _ | .struct l _ => l == .calldata
  | _ => false

/-- Whether `delete e` at type `τ` is refused: a local `storage` pointer
(solc: "delete cannot be applied to storage pointers") or a `calldata`
reference (calldata is read-only; decision 2026-10-30). -/
def Ctx.deleteRefused (Γ : Ctx) (τ : STy) (e : Syn .expr) : Bool :=
  τ.storageRef && Γ.namesLocal e || τ.calldataRef

/-- The buffer the canonical rethrow `revert(add(D, 32), mload(D))` names
(`isRethrow`'s shape with both `D` equal). `Syn.paths` collects no Yul
names, so this is what determines the rethrown local. -/
def rethrowVar? (body : Syn (.list .yulStmt)) : Option String :=
  match body with
  | .cons (.yulExprStmt (.yulCall "revert" (.cons (.yulCall "add" (.cons (.yulPath d [])
      (.cons (.yulLit (.dec 32)) .nil))) (.cons (.yulCall "mload" (.cons (.yulPath d' []) .nil))
      .nil)))) .nil => if d == d' then Option.some d else Option.none
  | _ => Option.none

/-- The placeholder identifier `_`. -/
def Syn.isUnderscore : {c : Cat} → Syn c → Bool
  | _, .ident "_" => true
  | _, _ => false

/-- A declaration statement (solc refuses one as the body of `if` or a
loop: "Variable declarations can only be used inside blocks"). -/
def Syn.isDecl {k : SCtx} : Syn (.stmt k) → Bool
  | .simpleStmt (.declVar _ _) | .simpleStmt (.declTuple _ _ _ _) => true
  | _ => false

/-! ## Expression typing -/

/-- Whether arguments convert pointwise to parameters. -/
def argsFit (isBase : DeclName → DeclName → Bool) (mapFree : DeclName → Bool) (σs ps : List STy) : Bool :=
  σs.length == ps.length && (List.zip σs ps).all (fun p => p.1.implicit isBase mapFree p.2)

/-- Whether an event or error accepts arguments of types `σs`. -/
def Decl.fitsParams (E : Env) (isBase : DeclName → DeclName → Bool) (mapFree : DeclName → Bool) (σs : List STy) (d : Decl) : Bool :=
  match d.paramTys E with
  | Option.some ps => argsFit isBase mapFree σs ps
  | Option.none => false


/-! ## Structs, external functions, payments and ABI encoding (S02 prerequisites) -/

/-- The member names of a struct, in order. -/
def Syn.memberNames : {c : Cat} → Syn c → List String
  | _, .cons x xs => x.memberNames ++ xs.memberNames
  | _, .structMember _ n => [n]
  | _, _ => []

/-- A struct declaration's members, at a location: their names and types. -/
def Decl.structFields (E : Env) (d : Decl) (l : DataLoc) : Option (List (String × STy)) :=
  match d.kind, d.top, d.node with
  | .struct, _, .struct _ m ms =>
    match (Syn.cons m ms).tys E d.scope l with
    | Option.some τs => Option.some ((Syn.cons m ms).memberNames.zip τs)
    | Option.none => Option.none
  | _, _, _ => Option.none

/-- The declaration a resolved type name denotes. -/
def Env.declOf (E : Env) (k : DeclKind) (dn : DeclName) : Option Decl :=
  E.decls.find? fun d => d.kind == k && d.scope == dn.scope && d.name == dn.name

/-- The members of struct `dn` at location `l`. -/
def Env.structFields (E : Env) (dn : DeclName) (l : DataLoc) : Option (List (String × STy)) :=
  (E.declOf .struct dn).bind (·.structFields E l)

/-- Whether a type is a mapping or holds one through arrays, a struct's
members asked of `f`. -/
def STy.mapsWith (f : DeclName → Bool) : STy → Bool
  | .mapping _ _ => true
  | .array _ σ _ => σ.mapsWith f
  | .struct _ d => f d
  | _ => false

/-- Whether a type contains a mapping, through arrays and struct members
(`n` levels of structs; a struct beyond them counts as none). -/
def Env.hasMapping (E : Env) : Nat → STy → Bool
  | 0, τ => τ.mapsWith fun _ => false
  | n + 1, τ => τ.mapsWith fun d => ((E.structFields d .storage).getD []).any fun f => E.hasMapping n f.2

/-- The number of struct declarations: a shortest path from a type to a
mapping it contains visits each struct at most once. -/
def Env.structCount (E : Env) : Nat := (E.decls.filter (·.kind == .struct)).length

/-- Whether a type name or member list names a mapping outside any user
type, and the user types it names (through arrays and members). -/
def Syn.mappingRefs : {c : Cat} → Syn c → Bool × List IdPath
  | _, .mapping _ _ _ _ => (true, [])
  | _, .array t _ => t.mappingRefs
  | _, .structMember t _ => t.mappingRefs
  | _, .userType p => (false, [p])
  | _, .cons x xs => let a := x.mappingRefs; let b := xs.mappingRefs; (a.1 || b.1, a.2 ++ b.2)
  | _, _ => (false, [])

/-- Whether the struct a user type name denotes holds a mapping through its
members, nested structs read `n` levels deep. -/
def Env.structHoldsMapping (E : Env) : Nat → Option String → IdPath → Bool
  | 0, _, _ => false
  | n + 1, scope, p =>
    match E.lookupPath scope p with
    | [d] =>
      match d.kind, d.top, d.node with
      | .struct, _, .struct _ m ms =>
        let r := (Syn.cons m ms).mappingRefs
        r.1 || r.2.any (E.structHoldsMapping n d.scope)
      | _, _, _ => false
    | _ => false

/-- **Whether struct `d` holds no mapping** (through its members, arrays and
nested structs, one level per struct declaration): a struct a conversion
may copy out of `storage` (`STy.implicit`'s `mapFree`; solc refuses the
copy otherwise). It reads the members' type names, not their elaborated
types (`Env.hasMapping`), so that it depends on no axiom: a conversion
proof embedded in an elaborated term mentions it. -/
def Env.mapFree (E : Env) (d : DeclName) : Bool :=
  match E.declOf .struct d with
  | Option.some dc =>
    match dc.kind, dc.top, dc.node with
    | .struct, _, .struct _ m ms =>
      let r := (Syn.cons m ms).mappingRefs
      !(r.1 || r.2.any (E.structHoldsMapping E.structCount dc.scope))
    | _, _, _ => true
  | Option.none => true

/-- Which structs of the environment hold no mapping (`Env.mapFree`). -/
abbrev Ctx.mapFree (Γ : Ctx) : DeclName → Bool := Γ.env.mapFree

/-- Whether a value of type `τ` contains a mapping (one level per struct
declaration reaches every struct a type can contain). -/
def Ctx.assignsMapping (Γ : Ctx) (τ : STy) : Bool := Γ.env.hasMapping (Γ.env.structCount + 1) τ

/-- Whether `a = …` at type `τ` is refused: a type containing a mapping is
copied, which solc refuses (9214), unless `a` names a local or return
variable, which is a storage pointer rebound (solc's exemption). -/
def Ctx.assignRefused (Γ : Ctx) (τ : STy) (a : Syn .expr) : Bool := Γ.assignsMapping τ && !Γ.namesLocal a

/-- The type of the `i`-th member of struct `dn` at location `l`. -/
def Env.fieldTy? (E : Env) (dn : DeclName) (l : DataLoc) (i : Nat) : Option STy :=
  (E.structFields dn l).bind fun fs => (fs[i]?).map Prod.snd

/-- The position and type of member `x` of struct `dn` at location `l`. -/
def Env.fieldAt (E : Env) (dn : DeclName) (l : DataLoc) (x : String) : Option (Nat × STy) :=
  (E.structFields dn l).bind fun fs =>
    ((fs.zipIdx).find? (·.1.1 == x)).map fun (p, i) => (i, p.2)

/-- The struct a call's callee names (`S(…)`). -/
def Ctx.structOf (Γ : Ctx) (x : String) : Option DeclName :=
  match Γ.resolve x with
  | Option.some (.decls [d]) => if d.kind == .struct then Option.some ⟨d.scope, d.name⟩ else Option.none
  | _ => Option.none

/-- The mutability of a function declaration. -/
def Decl.fnMut (d : Decl) : Option Mutability :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ m _ _ _ _ _ => m
  | _, _, _ => Option.none

/-- The functions named `f` that contract `dn` exposes externally
(`external` or `public`, found along its linearization). -/
def Env.extFunctions (E : Env) (dn : DeclName) (f : String) : List Decl :=
  (E.lookup (Option.some dn.name) f).filter fun d =>
    d.kind == .function && (d.fnVis == Option.some .external || d.fnVis == Option.some .pub)

/-- The external overload that accepts arguments of types `σs`. -/
def extOverloads (E : Env) (B : DeclName → DeclName → Bool) (M : DeclName → Bool) (dn : DeclName) (f : String)
    (σs : List STy) : List Decl :=
  (E.extFunctions dn f).filter fun d' => match d'.fnSig E with
    | Option.some (ps', _) => argsFit B M σs ps'
    | Option.none => false

/-- The ABI encoding functions. -/
inductive AbiKind where
  | encode | encodePacked | encodeWithSelector | encodeWithSignature
  deriving DecidableEq, Repr

/-- The `abi` member of an encoding function. -/
def AbiKind.ofMember : String → Option AbiKind
  | "encode" => Option.some .encode
  | "encodePacked" => Option.some .encodePacked
  | "encodeWithSelector" => Option.some .encodeWithSelector
  | "encodeWithSignature" => Option.some .encodeWithSignature
  | _ => Option.none

/-- A type `abi.encode*` takes as an argument here: a value type other than
an internal function, an integral constant (at its mobile type), a string
literal or a `bytes`/`string` in memory. -/
def STy.abiArg : STy → Bool
  | .int _ | .bool | .address _ | .fixedBytes _ _ | .fixed _ | .enum _ | .udvt _ | .contract _ => true
  | .fn ext _ _ _ => ext
  | .rational q | .hexConst q _ => q.isInt
  | .stringLit _ | .bytes .memory | .string .memory => true
  | _ => false

/-- The arguments an encoding function accepts: a `bytes4` selector or a
signature string first, where it takes one. -/
def AbiKind.argsOK (B : DeclName → DeclName → Bool) (M : DeclName → Bool) : AbiKind → List STy → Bool
  | .encode, σs | .encodePacked, σs => σs.all STy.abiArg
  | .encodeWithSelector, σ :: σs => σ.implicit B M (.fixedBytes 4 (by decide)) && σs.all STy.abiArg
  | .encodeWithSignature, σ :: σs => σ.isStringy && σs.all STy.abiArg
  | _, _ => false

/-! ### `abi.decode` -/

/-- The user-defined type a name denotes as a type expression (solc's
`TypeType` of the declaration), in `memory`: a struct, an enum, a
user-defined value type, a contract or an interface. A local or any
other declaration is not a type. -/
def Ctx.typeNameOf (Γ : Ctx) (x : String) : Option STy :=
  match Γ.resolve x with
  | Option.some (.decls [d]) =>
    match d.kind with
    | .struct => Option.some (.struct .memory ⟨d.scope, d.name⟩)
    | .enum => Option.some (.enum ⟨d.scope, d.name⟩)
    | .udvt => Option.some (.udvt ⟨d.scope, d.name⟩)
    | .contract | .interface => Option.some (.contract ⟨d.scope, d.name⟩)
    | _ => Option.none
  | _ => Option.none

/-- The types a list of type expressions names, in `memory`: an
elementary type name, a user-defined type by an unqualified name, an
array of one (`T[]`, `T[k]` with a positive constant `k`); qualified names
(`L.S`) are not read. -/
def Syn.typeExprs (Γ : Ctx) : {c : Cat} → Syn c → Option (List STy)
  | _, .elemType el _ => Option.some [el.ty .memory]
  | _, .ident x => (Γ.typeNameOf x).map ([·])
  | _, .index t o =>
    match t.typeExprs Γ, arrayLen o with
    | Option.some [σ], Option.some k => Option.some [.array .memory σ k]
    | _, _ => Option.none
  | _, .some x => x.typeExprs Γ
  | _, .nil => Option.some []
  | _, .cons x xs =>
    match x.typeExprs Γ, xs.typeExprs Γ with
    | Option.some a, Option.some b => Option.some (a ++ b)
    | _, _ => Option.none
  | _, _ => Option.none

/-- A top-level `address` component of `abi.decode` is `address payable`
(solc: "We force address payable for address types"); an array's elements
keep their type. -/
def STy.payableTop : STy → STy
  | .address _ => .address true
  | τ => τ

/-- The types `abi.decode`'s second argument names: the components of a
parenthesized list of type expressions (`(T)` and `(T, U)`, every
component present, none itself parenthesized), or a single type
expression; a top-level `address` is `address payable`. -/
def Ctx.decodeTys (Γ : Ctx) (e : Syn .expr) : Option (List STy) :=
  (match e with
   | .tuple o s => (Syn.cons o s).typeExprs Γ
   | e => e.typeExprs Γ).map (fun τs : List STy => τs.map STy.payableTop)

/-- The data `abi.decode` reads: `bytes` in memory or storage, or a string
literal (all implicitly `bytes memory`), or `bytes calldata` (lane FU2-B,
read through its reference), as solc requires. -/
def STy.decodeSrc : STy → Bool
  | .bytes .memory | .bytes .storage | .bytes .calldata | .stringLit _ => true
  | _ => false

/-- solc's `Type::commonType` of two element types of an inline array:
`a`'s mobile type if `b` converts to it, else `b`'s if `a`'s mobile type
converts to it (lane FU2-B; solc's fold starts at the first element's
mobile type, so `[1, -1]` has none: `uint8` and `int8`). -/
def STy.common (B : DeclName → DeclName → Bool) (M : DeclName → Bool) (a b : STy) : Option STy :=
  if b.implicit B M a.mobile then Option.some a.mobile
  else if a.mobile.implicit B M b.mobile then Option.some b.mobile else Option.none

/-- The common type of an inline array's element types, folded left to
right from the first's mobile type, as solc's `TypeChecker` does. -/
def STy.commonOf (B : DeclName → DeclName → Bool) (M : DeclName → Bool) (a : STy) : List STy → Option STy
  | [] => Option.some a.mobile
  | b :: bs => match STy.common B M a b with
    | Option.some c => STy.commonOf B M c bs
    | Option.none => Option.none

/-- **A type `new` allocates with a length** (lane FU2-B): `bytes`,
`string`, a dynamic memory array of one-word elements. -/
def STy.newable : STy → Bool
  | .bytes .memory | .string .memory => true
  | .array .memory σ none => σ.oneWord
  | _ => false

/-- **A sliceable type** (`a[s:e]`): bytes/string calldata or a dynamic
calldata array with a represented statically encoded element. Dynamically
encoded base elements remain refused (solc2148); struct layouts remain open. -/
def STy.sliceable : STy → Bool
  | .bytes .calldata | .string .calldata => true
  | .array .calldata σ none => 0 < σ.cdStaticWords
  | _ => false

/-- A one-word ABI value the decoder reads (`decodeElemWord`), other than
fixed point (solc's ABI coder does not implement it) and function types. -/
def STy.wordElem : STy → Bool
  | .int _ | .bool | .address _ | .fixedBytes _ _ | .enum _ | .contract _ => true
  | _ => false

/-- The underlying type of a user-defined value type, as `Env.layout`
(`Solidity/Source/Machine.lean`) reads it. -/
def Env.udvtUnderlying (E : Env) (d : DeclName) : STy :=
  match E.declOf .udvt d with
  | Option.some ⟨.udvt, _, _, _, .udvt _ el⟩ => el.ty .memory
  | _ => .bool

/-- A one-word value the decoder reads: a user-defined value type at its
underlying type, any other type by `STy.wordElem`. -/
def STy.decodableElem (E : Env) : STy → Bool
  | .udvt d => (E.udvtUnderlying d).wordElem
  | τ => τ.wordElem

/-- **A type `abi.decode` reads in the source semantics**: the types the
ABI decoder of S02/S04 (`decodeArgs`) decodes: a one-word value type, an
enum at its member count, a user-defined value type at its underlying
type, `bytes`/`string` in memory, and a dynamic memory array of
one-word values. Static arrays, structs, nested arrays, fixed point and
external function types are refused (a named refusal: the decoder does
not read them). -/
def STy.decodable (E : Env) : STy → Bool
  | .bytes .memory | .string .memory => true
  | .array .memory σ none => σ.decodableElem E
  | τ => τ.decodableElem E

/-- A copy into storage (`s = m`): the source is the target's type in
`memory` or `calldata`, or a string literal into `bytes`/`string`
`storage` (solc copies member by member; S01's `assign` covers pointer
assignments). -/
def STy.copiesTo (σ τ : STy) : Bool :=
  match σ, τ with
  | .stringLit _, .bytes .storage | .stringLit _, .string .storage => true
  | .bytes l, .bytes .storage | .string l, .string .storage => l != .storage
  | .array l σ n, .array .storage τ n' => l != .storage && n == n' && STy.same (σ.withLoc .storage) τ
  | .struct l d, .struct .storage d' => l != .storage && d == d'
  | _, _ => false


mutual

/-- **Expression typing**, as data: a derivation is the elaborated term. -/
inductive Typed (Γ : Ctx) : Syn .expr → STy → Type where
  /-- A constant expression has its exact value as its type. -/
  | const {e : Syn .expr} {q : Q} : e.const = Option.some q → e.isAddressLit = false →
      e.hexLen? = Option.none → Typed Γ e (.rational q)
  /-- A hexadecimal literal of `2·len` digits: its value, convertible to
  `bytes{len}` (solc: a literal is always a constant, `STy.hexConst`). -/
  | litBytes {n : NumLit} {len : Nat} : (Syn.lit (.num n)).hexLen? = Option.some len →
      Typed Γ (.lit (.num n)) (.hexConst n.value len)
  /-- A checksummed 40-digit hexadecimal literal is an `address`. -/
  | litAddress {ds : List (Fin 16)} : ds.length = 40 → Typed Γ (.lit (.num (.hex ds true))) (.address false)
  | bool (b : Bool) : Typed Γ (.lit (.bool b)) .bool
  | str (bs : List UInt8) : Typed Γ (.lit (.str bs)) (.stringLit bs)
  | hexStr (bs : List UInt8) : Typed Γ (.lit (.hexStr bs)) (.stringLit bs)
  | unicodeStr (bs : List UInt8) : Typed Γ (.lit (.unicodeStr bs)) (.stringLit bs)
  /-- A local, by its position. -/
  | loc {x : String} {i : Nat} {τ : STy} : Γ.resolve x = Option.some (.loc i) →
      Γ.tys[i]? = Option.some τ → Typed Γ (.ident x) τ
  /-- A state variable or constant, by its declaration. -/
  | state {x : String} {d : Decl} {τ : STy} : Γ.resolve x = Option.some (.decls [d]) →
      d.varTy Γ.env = Option.some τ → Typed Γ (.ident x) τ
  | this {c : String} : Γ.resolve "this" = Option.some (.builtin .this) → Γ.scope = Option.some c →
      Typed Γ (.ident "this") (.contract ⟨Option.none, c⟩)
  | paren {e : Syn .expr} {τ : STy} : Typed Γ e τ → Typed Γ (.tuple (.some e) .nil) τ
  /-- `(a, b, …)` with every slot present, at the components' mobile types. -/
  | tuple {e : Syn .expr} {s : Syn (.list (.opt .expr))} {τ : STy} {τs : List STy} :
      Typed Γ e τ → TypedSlots Γ s τs → τs ≠ [] →
      Typed Γ (.tuple (.some e) s) (.tuple (τ.mobile :: τs.map STy.mobile))
  /-- `-e` on a signed integer. -/
  | neg {e : Syn .expr} {t : IntTy} : Typed Γ e (.int t) → t.signed = true →
      Typed Γ (.unaryPrefix .neg e) (.int t)
  /-- `-e` on any fixed-point type, `ufixed` included (second round). -/
  | negFixed {e : Syn .expr} {f : FixTy} : Typed Γ e (.fixed f) →
      Typed Γ (.unaryPrefix .neg e) (.fixed f)
  | not {e : Syn .expr} : Typed Γ e .bool → Typed Γ (.unaryPrefix .not e) .bool
  /-- `~e` on an integer or `bytesN`. -/
  | bitNot {e : Syn .expr} {τ : STy} : Typed Γ e τ → τ.isBits = true → Typed Γ (.unaryPrefix .bitNot e) τ
  /-- `++e`, `--e` on an assignable number (fixed point: `±1`). -/
  | incDec {e : Syn .expr} {op : PrefixOp} {τ : STy} : op = .inc ∨ op = .dec → LVal Γ e τ →
      τ.isNumeric = true → Typed Γ (.unaryPrefix op e) τ
  | incDecSuffix {e : Syn .expr} {op : SuffixOp} {τ : STy} : LVal Γ e τ → τ.isNumeric = true →
      Typed Γ (.unarySuffix op e) τ
  /-- `delete e` on an assignable non-mapping, not a local `storage`
  pointer or a `calldata` reference (`Ctx.deleteRefused`). -/
  | delete {e : Syn .expr} {τ : STy} : LVal Γ e τ → (τ matches .mapping _ _) = false →
      Γ.deleteRefused τ e = false →
      Typed Γ (.unaryPrefix .delete e) (.tuple [])
  /-- `a ∘ b` for `+ - * / %`: numbers meeting at a common type. -/
  | arith {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.arith, a, b) →
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase Γ.mapFree τa τb = Option.some τ →
      τ.isNumeric = true → (e.isDivMod && τb.isZeroConst) = false → Typed Γ e τ
  /-- `a ∘ b` for `& | ^`: integers or `bytesN`. -/
  | bit {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.bit, a, b) →
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase Γ.mapFree τa τb = Option.some τ →
      τ.isBits = true → Typed Γ e τ
  /-- `a << b`, `a >> b`: an integer or `bytesN` by an unsigned amount, at
  `a`'s type (a constant `a` with a non-constant amount: `uint256`, or
  `int256` when negative, `STy.shiftTy`).
  Two constant operands are folded (`const`), never typed here. -/
  | shift {e a b : Syn .expr} {τa τb : STy} : e.binOp? = Option.some (.shift, a, b) →
      Typed Γ a τa → Typed Γ b τb → τa.shiftTy.isBits = true → τb.isAmount = true →
      (a.const.isSome && b.const.isSome) = false → Typed Γ e τa.shiftTy
  /-- `a ** b`: an integer to an unsigned power, at `a`'s type (`STy.shiftTy`); two
  constants are folded. -/
  | exp {e a b : Syn .expr} {τa τb : STy} : e.binOp? = Option.some (.exp, a, b) →
      Typed Γ a τa → Typed Γ b τb → τa.shiftTy.isInt = true → τb.isAmount = true →
      (a.const.isSome && b.const.isSome) = false → Typed Γ e τa.shiftTy
  | order {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.order, a, b) →
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase Γ.mapFree τa τb = Option.some τ →
      τ.isOrdered = true → Typed Γ e .bool
  | eq {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.eq, a, b) →
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase Γ.mapFree τa τb = Option.some τ →
      τ.hasEq = true → Typed Γ e .bool
  /-- A comparison of two constants is a boolean. -/
  | compareConst {e a b : Syn .expr} {k : BinKind} {qa qb : Q} :
      e.binOp? = Option.some (k, a, b) → k = .order ∨ k = .eq → a.const = Option.some qa →
      b.const = Option.some qb → Typed Γ e .bool
  | logic {e a b : Syn .expr} : e.binOp? = Option.some (.logic, a, b) → Typed Γ a .bool →
      Typed Γ b .bool → Typed Γ e .bool
  /-- `c ? a : b`: the branches' mobile types meet. -/
  | cond {c a b : Syn .expr} {τa τb τ : STy} : Typed Γ c .bool → Typed Γ a τa → Typed Γ b τb →
      STy.common? Γ.isBase Γ.mapFree τa.mobile τb.mobile = Option.some τ → Typed Γ (.cond c a b) τ
  /-- `a = b`: `b` converts implicitly to `a`'s type; a type containing a
  mapping is never copied, only rebound by a local (`Ctx.assignRefused`). -/
  | assign {a b : Syn .expr} {τ σ : STy} : LVal Γ a τ → Typed Γ b σ →
      σ.implicit Γ.isBase Γ.mapFree τ = true → Γ.assignRefused τ a = false → Typed Γ (.assign .assign a b) τ
  /-- `a ∘= b`: as `a = a ∘ b`. -/
  | compound {a b : Syn .expr} {op : AssignOp} {τ σ : STy} :
      LVal Γ a τ → Typed Γ b σ → op.fits Γ.isBase Γ.mapFree σ τ = true → Typed Γ (.assign op a b) τ
  /-- `a[i]` on an array: its element. -/
  | indexArray {a i : Syn .expr} {l : DataLoc} {τ σ : STy} {n : Option Nat} :
      Typed Γ a (.array l τ n) → Typed Γ i σ → σ.isIndex = true → inBounds σ n = true →
      Typed Γ (.index a (.some i)) τ
  /-- `m[k]` on a mapping: its value. -/
  | indexMapping {a i : Syn .expr} {τk τv σ : STy} : Typed Γ a (.mapping τk τv) → Typed Γ i σ →
      σ.implicit Γ.isBase Γ.mapFree τk = true → Typed Γ (.index a (.some i)) τv
  /-- `b[i]` on `bytes` or `bytesN`: one byte (read only for `bytesN`). -/
  | indexBytes {a i : Syn .expr} {τ σ : STy} : Typed Γ a τ →
      (match τ with | .bytes _ => true | .fixedBytes _ _ => true | _ => false) = true →
      Typed Γ i σ → σ.isIndex = true →
      inBounds σ (match τ with | .fixedBytes n _ => Option.some n | _ => Option.none) = true →
      Typed Γ (.index a (.some i)) (.fixedBytes 1 (by decide))
  /-- `x.length` on an array or `bytes` (`uint256`) or a `bytesN` (`uint8`). -/
  | length {a : Syn .expr} {τ ρ : STy} : Typed Γ a τ → τ.lengthTy = Option.some ρ →
      Typed Γ (.member a "length") ρ
  /-- `T(e)` for an elementary `T`: an explicit conversion (`bytes`/`string`
  keep the argument's location). -/
  | convElem {x : Syn .expr} {el : Elem} {h : el ≠ .addressPayable} {σ τ : STy} : Typed Γ x σ →
      τ = el.ty (match σ with | .bytes l => l | .string l => l | _ => .memory) →
      σ.explicit Γ.isBase Γ.mapFree τ = true →
      Typed Γ (.call (.elemType el h) (.positional (.cons x .nil))) τ
  /-- `C(e)`, `E(e)`: an explicit conversion to a contract or enum. -/
  | convUser {x : Syn .expr} {n : String} {τ σ : STy} : Γ.convTarget n = Option.some τ →
      Typed Γ x σ → σ.explicit Γ.isBase Γ.mapFree τ = true →
      Typed Γ (.call (.ident n) (.positional (.cons x .nil))) τ
  /-- `payable(e)` of an address or contract. -/
  | payable {x : Syn .expr} {σ : STy} : Typed Γ x σ →
      (match σ with | .address _ => true | .contract _ => true | _ => false) = true →
      Typed Γ (.payableConv (.positional (.cons x .nil))) (.address true)
  /-- `f(args)` of an internal function: exactly one callable overload
  accepts the arguments; one return is the value, otherwise a tuple. -/
  | callInternal {f : String} {args : Syn (.list .expr)} {d : Decl} {ps rs σs : List STy} :
      TypedArgs Γ args σs →
      (Γ.functions f).filter (fun d' => match d'.fnSig Γ.env with
        | Option.some (ps', _) => argsFit Γ.isBase Γ.mapFree σs ps'
        | Option.none => false) = [d] →
      d.fnSig Γ.env = Option.some (ps, rs) →
      Typed Γ (.call (.ident f) (.positional args)) (STy.ret rs)
  /-- An admitted magic member: `msg.sender`, `msg.value` (where allowed),
  `block.timestamp`. -/
  | magic {g m : String} {b : Builtin} {τ : STy} {feature : String} :
      Γ.resolve g = Option.some (.builtin b) → b.memberStatus m = Option.some (.admitted feature) →
      b.memberTy m = Option.some τ → (b == .msg && m == "value" && !Γ.msgValue) = false →
      Typed Γ (.member (.ident g) m) τ
  /-- `a.balance` of an address. -/
  | balance {a : Syn .expr} {p : Bool} : Typed Γ a (.address p) →
      Typed Γ (.member a "balance") (.int IntTy.u256)
  /-- A call of an admitted builtin function (`require`, `assert`, `revert`,
  the hashes, `addmod`/`mulmod`, `ecrecover`). -/
  | builtinCall {f : String} {args : Syn (.list .expr)} {b : Builtin} {σs : List STy} {τ : STy}
      {feature : String} : Γ.resolve f = Option.some (.builtin b) →
      b.status = .admitted feature → TypedArgs Γ args σs →
      b.callTy Γ.isBase Γ.mapFree σs = Option.some τ → Typed Γ (.call (.ident f) (.positional args)) τ
  /-- `a.x` on a struct: its member. -/
  | member {a : Syn .expr} {x : String} {l : DataLoc} {dn : DeclName} {i : Nat} {τ : STy} :
      Typed Γ a (.struct l dn) → Γ.env.fieldAt dn l x = Option.some (i, τ) → Typed Γ (.member a x) τ
  /-- `S(args)`: a new struct in memory, the members accepting the arguments. -/
  | structNew {S : String} {args : Syn (.list .expr)} {dn : DeclName} {fs : List (String × STy)}
      {σs : List STy} : Γ.structOf S = Option.some dn → Γ.env.structFields dn .memory = Option.some fs →
      TypedArgs Γ args σs → argsFit Γ.isBase Γ.mapFree σs (fs.map Prod.snd) = true →
      Typed Γ (.call (.ident S) (.positional args)) (.struct .memory dn)
  /-- `c.f(args)`: an external call; exactly one exposed overload accepts
  the arguments. -/
  | extCall {c : Syn .expr} {f : String} {args : Syn (.list .expr)} {dn : DeclName} {d : Decl}
      {ps rs σs : List STy} : Typed Γ c (.contract dn) → TypedArgs Γ args σs →
      extOverloads Γ.env Γ.isBase Γ.mapFree dn f σs = [d] → d.fnSig Γ.env = Option.some (ps, rs) →
      Typed Γ (.call (.member c f) (.positional args)) (STy.ret rs)
  /-- `c.f{value: v}(args)`: an external call of a `payable` function with
  value. -/
  | extCallValue {c v : Syn .expr} {f : String} {args : Syn (.list .expr)} {dn : DeclName} {d : Decl}
      {ps rs σs : List STy} {σ : STy} : Typed Γ c (.contract dn) → Typed Γ v σ →
      σ.implicit Γ.isBase Γ.mapFree (.int IntTy.u256) = true → TypedArgs Γ args σs →
      extOverloads Γ.env Γ.isBase Γ.mapFree dn f σs = [d] → d.fnSig Γ.env = Option.some (ps, rs) →
      d.fnMut = Option.some .payable →
      Typed Γ (.call (.callOptions (.member c f) (.namedArg "value" v) .nil) (.positional args)) (STy.ret rs)
  /-- `a.transfer(v)` on an `address payable`. -/
  | transfer {a v : Syn .expr} {σ : STy} : Typed Γ a (.address true) → Typed Γ v σ →
      σ.implicit Γ.isBase Γ.mapFree (.int IntTy.u256) = true →
      Typed Γ (.call (.member a "transfer") (.positional (.cons v .nil))) (.tuple [])
  /-- `a.send(v)` on an `address payable`: whether the payment succeeded. -/
  | send {a v : Syn .expr} {σ : STy} : Typed Γ a (.address true) → Typed Γ v σ →
      σ.implicit Γ.isBase Γ.mapFree (.int IntTy.u256) = true →
      Typed Γ (.call (.member a "send") (.positional (.cons v .nil))) .bool
  /-- `abi.encode(…)`, `abi.encodePacked(…)`, `abi.encodeWithSelector(…)`,
  `abi.encodeWithSignature(…)`: `bytes memory`. -/
  | abiEncode {g m : String} {args : Syn (.list .expr)} {σs : List STy} {k : AbiKind} :
      Γ.resolve g = Option.some (.builtin .abi) → AbiKind.ofMember m = Option.some k →
      TypedArgs Γ args σs → k.argsOK Γ.isBase Γ.mapFree σs = true →
      Typed Γ (.call (.member (.ident g) m) (.positional args)) (.bytes .memory)
  /-- `s = e` copying into storage: from `memory`, `calldata`, or a string
  literal; the target is a storage location, not a local `storage` pointer. -/
  | assignCopy {a b : Syn .expr} {τ σ : STy} : LVal Γ a τ → Typed Γ b σ → σ.copiesTo τ = true →
      Γ.namesLocal a = false → Typed Γ (.assign .assign a b) τ
  /-- `a[s:e]`, `a[s:]`, `a[:e]`, `a[:]` (lane FU2-B): a slice of a
  `calldata` `bytes` or dynamic array, at the array's type (solc's slice
  type converts implicitly to it), the bounds unsigned indices. -/
  | slice {a s e : Syn .expr} {τ σ ρ : STy} : Typed Γ a τ → τ.sliceable = true →
      Typed Γ s σ → σ.isIndex = true → Typed Γ e ρ → ρ.isIndex = true →
      Typed Γ (.slice a (.some s) (.some e)) τ
  | sliceFrom {a s : Syn .expr} {τ σ : STy} : Typed Γ a τ → τ.sliceable = true →
      Typed Γ s σ → σ.isIndex = true → Typed Γ (.slice a (.some s) .none) τ
  | sliceTo {a e : Syn .expr} {τ ρ : STy} : Typed Γ a τ → τ.sliceable = true →
      Typed Γ e ρ → ρ.isIndex = true → Typed Γ (.slice a .none (.some e)) τ
  | sliceAll {a : Syn .expr} {τ : STy} : Typed Γ a τ → τ.sliceable = true →
      Typed Γ (.slice a .none .none) τ
  /-- `abi.decode(data, (T₁, …, Tₙ))` (FU2-B): the values the ABI decoder
  reads from `bytes` data, at the named types in `memory`, each one the
  decoder reads (`STy.decodable`); one type is its value, more a tuple. -/
  | abiDecode {g : String} {x ts : Syn .expr} {σ : STy} {τs : List STy} :
      Γ.resolve g = Option.some (.builtin .abi) → Typed Γ x σ → σ.decodeSrc = true →
      Γ.decodeTys ts = Option.some τs → τs.all (STy.decodable Γ.env) = true →
      Typed Γ (.call (.member (.ident g) "decode") (.positional (.cons x (.cons ts .nil)))) (STy.ret τs)
  /-- `[e₁, …, eₙ]` (lane FU2-B): a new `T[n] memory`, `T` the elements'
  common type (`STy.commonOf`), each element converting to it; only
  one-word element types (references are not modelled). -/
  | inlineArray {e : Syn .expr} {es : Syn (.list .expr)} {τ σ : STy} {τs : List STy} :
      Typed Γ e τ → TypedArgs Γ es τs → STy.commonOf Γ.isBase Γ.mapFree τ τs = Option.some σ → σ.oneWord = true →
      argsFit Γ.isBase Γ.mapFree (τ :: τs) (List.replicate (τs.length + 1) σ) = true →
      Typed Γ (.inlineArray e es) (.array .memory σ (Option.some (τs.length + 1)))
  /-- `new T[](n)`, `new bytes(n)`, `new string(n)` (lane FU2-B): a new
  memory object of `n` zeroed elements (`STy.newable`); `n` an index. -/
  | newArray {t : Syn .typeName} {x : Syn .expr} {τ σ : STy} :
      t.ty Γ.env Γ.scope .memory = Option.some τ → τ.newable = true → Typed Γ x σ → σ.isIndex = true →
      Typed Γ (.call (.new t) (.positional (.cons x .nil))) τ

/-- Typing of an argument list. -/
inductive TypedArgs (Γ : Ctx) : Syn (.list .expr) → List STy → Type where
  | nil : TypedArgs Γ .nil []
  | cons {e : Syn .expr} {es : Syn (.list .expr)} {τ : STy} {τs : List STy} :
      Typed Γ e τ → TypedArgs Γ es τs → TypedArgs Γ (.cons e es) (τ :: τs)

/-- Typing of tuple slots, each present. -/
inductive TypedSlots (Γ : Ctx) : Syn (.list (.opt .expr)) → List STy → Type where
  | nil : TypedSlots Γ .nil []
  | cons {e : Syn .expr} {es : Syn (.list (.opt .expr))} {τ : STy} {τs : List STy} :
      Typed Γ e τ → TypedSlots Γ es τs → TypedSlots Γ (.cons (.some e) es) (τ :: τs)

/-- **Lvalues**: a local; a state variable neither `constant` nor
`immutable`; an element of a `storage` or `memory` array; a mapping value.
`length`, `balance`, magic members, `bytesN` elements and `calldata`
elements are not lvalues; a `bytes` byte is. -/
inductive LVal (Γ : Ctx) : Syn .expr → STy → Type where
  | loc {x : String} {i : Nat} {τ : STy} : Γ.resolve x = Option.some (.loc i) →
      Γ.tys[i]? = Option.some τ → LVal Γ (.ident x) τ
  | state {x : String} {d : Decl} {τ : STy} : Γ.resolve x = Option.some (.decls [d]) →
      d.varTy Γ.env = Option.some τ → d.mutable = true → LVal Γ (.ident x) τ
  | paren {e : Syn .expr} {τ : STy} : LVal Γ e τ → LVal Γ (.tuple (.some e) .nil) τ
  | indexArray {a i : Syn .expr} {l : DataLoc} {τ σ : STy} {n : Option Nat} :
      Typed Γ a (.array l τ n) → l ≠ .calldata → Typed Γ i σ → σ.isIndex = true →
      inBounds σ n = true → LVal Γ (.index a (.some i)) τ
  | indexMapping {a i : Syn .expr} {τk τv σ : STy} : Typed Γ a (.mapping τk τv) → Typed Γ i σ →
      σ.implicit Γ.isBase Γ.mapFree τk = true → LVal Γ (.index a (.some i)) τv
  /-- A byte of a `storage` or `memory` `bytes`. -/
  | indexBytes {a i : Syn .expr} {l : DataLoc} {σ : STy} : Typed Γ a (.bytes l) → l ≠ .calldata →
      Typed Γ i σ → σ.isIndex = true → LVal Γ (.index a (.some i)) (.fixedBytes 1 (by decide))
  /-- A member of a `storage` or `memory` struct. -/
  | member {a : Syn .expr} {x : String} {l : DataLoc} {dn : DeclName} {i : Nat} {τ : STy} :
      Typed Γ a (.struct l dn) → l ≠ .calldata → Γ.env.fieldAt dn l x = Option.some (i, τ) →
      LVal Γ (.member a x) τ

end

/-- Expression typing as a proposition. -/
def HasType (Γ : Ctx) (e : Syn .expr) (τ : STy) : Prop := Nonempty (Typed Γ e τ)

end Solidity.Source
