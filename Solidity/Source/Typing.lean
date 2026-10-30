import Solidity.Source.Types
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
    if [x, y, k].all (·.implicit isBase (.int IntTy.u256)) && !k.isZeroConst then
      Option.some (.int IntTy.u256)
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
def STy.common? (isBase : DeclName → DeclName → Bool) (a b : STy) : Option STy :=
  if a.isConstTy && (b.isConstTy || b.isFixedBytes) then Option.none
  else if b.implicit isBase a.mobile then Option.some a.mobile
  else if a.implicit isBase b.mobile then Option.some b.mobile else Option.none

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
def AssignOp.fits (isBase : DeclName → DeclName → Bool) (op : AssignOp) (σ τ : STy) : Bool :=
  match op.kind? with
  | Option.some .arith => σ.implicit isBase τ && τ.isNumeric
  | Option.some .bit => σ.implicit isBase τ && τ.isBits
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
def argsFit (isBase : DeclName → DeclName → Bool) (σs ps : List STy) : Bool :=
  σs.length == ps.length && (List.zip σs ps).all (fun p => p.1.implicit isBase p.2)

/-- Whether an event or error accepts arguments of types `σs`. -/
def Decl.fitsParams (E : Env) (isBase : DeclName → DeclName → Bool) (σs : List STy) (d : Decl) : Bool :=
  match d.paramTys E with
  | Option.some ps => argsFit isBase σs ps
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
def extOverloads (E : Env) (B : DeclName → DeclName → Bool) (dn : DeclName) (f : String)
    (σs : List STy) : List Decl :=
  (E.extFunctions dn f).filter fun d' => match d'.fnSig E with
    | Option.some (ps', _) => argsFit B σs ps'
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
def AbiKind.argsOK (B : DeclName → DeclName → Bool) : AbiKind → List STy → Bool
  | .encode, σs | .encodePacked, σs => σs.all STy.abiArg
  | .encodeWithSelector, σ :: σs => σ.implicit B (.fixedBytes 4 (by decide)) && σs.all STy.abiArg
  | .encodeWithSignature, σ :: σs => σ.isStringy && σs.all STy.abiArg
  | _, _ => false

/-- A reference type moved to a location (nested arrays with it). -/
def STy.withLoc (l : DataLoc) : STy → STy
  | .bytes _ => .bytes l
  | .string _ => .string l
  | .array _ τ n => .array l (τ.withLoc l) n
  | .struct _ d => .struct l d
  | τ => τ

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
  /-- `delete e` on an assignable non-mapping. -/
  | delete {e : Syn .expr} {τ : STy} : LVal Γ e τ → (τ matches .mapping _ _) = false →
      Typed Γ (.unaryPrefix .delete e) (.tuple [])
  /-- `a ∘ b` for `+ - * / %`: numbers meeting at a common type. -/
  | arith {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.arith, a, b) →
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
      τ.isNumeric = true → (e.isDivMod && τb.isZeroConst) = false → Typed Γ e τ
  /-- `a ∘ b` for `& | ^`: integers or `bytesN`. -/
  | bit {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.bit, a, b) →
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
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
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
      τ.isOrdered = true → Typed Γ e .bool
  | eq {e a b : Syn .expr} {τa τb τ : STy} : e.binOp? = Option.some (.eq, a, b) →
      Typed Γ a τa → Typed Γ b τb → STy.common? Γ.isBase τa τb = Option.some τ →
      τ.hasEq = true → Typed Γ e .bool
  /-- A comparison of two constants is a boolean. -/
  | compareConst {e a b : Syn .expr} {k : BinKind} {qa qb : Q} :
      e.binOp? = Option.some (k, a, b) → k = .order ∨ k = .eq → a.const = Option.some qa →
      b.const = Option.some qb → Typed Γ e .bool
  | logic {e a b : Syn .expr} : e.binOp? = Option.some (.logic, a, b) → Typed Γ a .bool →
      Typed Γ b .bool → Typed Γ e .bool
  /-- `c ? a : b`: the branches' mobile types meet. -/
  | cond {c a b : Syn .expr} {τa τb τ : STy} : Typed Γ c .bool → Typed Γ a τa → Typed Γ b τb →
      STy.common? Γ.isBase τa.mobile τb.mobile = Option.some τ → Typed Γ (.cond c a b) τ
  /-- `a = b`: `b` converts implicitly to `a`'s type; a mapping is never
  assigned. -/
  | assign {a b : Syn .expr} {τ σ : STy} : LVal Γ a τ → Typed Γ b σ →
      σ.implicit Γ.isBase τ = true → (τ matches .mapping _ _) = false → Typed Γ (.assign .assign a b) τ
  /-- `a ∘= b`: as `a = a ∘ b`. -/
  | compound {a b : Syn .expr} {op : AssignOp} {τ σ : STy} :
      LVal Γ a τ → Typed Γ b σ → op.fits Γ.isBase σ τ = true → Typed Γ (.assign op a b) τ
  /-- `a[i]` on an array: its element. -/
  | indexArray {a i : Syn .expr} {l : DataLoc} {τ σ : STy} {n : Option Nat} :
      Typed Γ a (.array l τ n) → Typed Γ i σ → σ.isIndex = true → inBounds σ n = true →
      Typed Γ (.index a (.some i)) τ
  /-- `m[k]` on a mapping: its value. -/
  | indexMapping {a i : Syn .expr} {τk τv σ : STy} : Typed Γ a (.mapping τk τv) → Typed Γ i σ →
      σ.implicit Γ.isBase τk = true → Typed Γ (.index a (.some i)) τv
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
      σ.explicit Γ.isBase τ = true →
      Typed Γ (.call (.elemType el h) (.positional (.cons x .nil))) τ
  /-- `C(e)`, `E(e)`: an explicit conversion to a contract or enum. -/
  | convUser {x : Syn .expr} {n : String} {τ σ : STy} : Γ.convTarget n = Option.some τ →
      Typed Γ x σ → σ.explicit Γ.isBase τ = true →
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
        | Option.some (ps', _) => argsFit Γ.isBase σs ps'
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
      b.callTy Γ.isBase σs = Option.some τ → Typed Γ (.call (.ident f) (.positional args)) τ
  /-- `a.x` on a struct: its member. -/
  | member {a : Syn .expr} {x : String} {l : DataLoc} {dn : DeclName} {i : Nat} {τ : STy} :
      Typed Γ a (.struct l dn) → Γ.env.fieldAt dn l x = Option.some (i, τ) → Typed Γ (.member a x) τ
  /-- `S(args)`: a new struct in memory, the members accepting the arguments. -/
  | structNew {S : String} {args : Syn (.list .expr)} {dn : DeclName} {fs : List (String × STy)}
      {σs : List STy} : Γ.structOf S = Option.some dn → Γ.env.structFields dn .memory = Option.some fs →
      TypedArgs Γ args σs → argsFit Γ.isBase σs (fs.map Prod.snd) = true →
      Typed Γ (.call (.ident S) (.positional args)) (.struct .memory dn)
  /-- `c.f(args)`: an external call; exactly one exposed overload accepts
  the arguments. -/
  | extCall {c : Syn .expr} {f : String} {args : Syn (.list .expr)} {dn : DeclName} {d : Decl}
      {ps rs σs : List STy} : Typed Γ c (.contract dn) → TypedArgs Γ args σs →
      extOverloads Γ.env Γ.isBase dn f σs = [d] → d.fnSig Γ.env = Option.some (ps, rs) →
      Typed Γ (.call (.member c f) (.positional args)) (STy.ret rs)
  /-- `c.f{value: v}(args)`: an external call of a `payable` function with
  value. -/
  | extCallValue {c v : Syn .expr} {f : String} {args : Syn (.list .expr)} {dn : DeclName} {d : Decl}
      {ps rs σs : List STy} {σ : STy} : Typed Γ c (.contract dn) → Typed Γ v σ →
      σ.implicit Γ.isBase (.int IntTy.u256) = true → TypedArgs Γ args σs →
      extOverloads Γ.env Γ.isBase dn f σs = [d] → d.fnSig Γ.env = Option.some (ps, rs) →
      d.fnMut = Option.some .payable →
      Typed Γ (.call (.callOptions (.member c f) (.namedArg "value" v) .nil) (.positional args)) (STy.ret rs)
  /-- `a.transfer(v)` on an `address payable`. -/
  | transfer {a v : Syn .expr} {σ : STy} : Typed Γ a (.address true) → Typed Γ v σ →
      σ.implicit Γ.isBase (.int IntTy.u256) = true →
      Typed Γ (.call (.member a "transfer") (.positional (.cons v .nil))) (.tuple [])
  /-- `a.send(v)` on an `address payable`: whether the payment succeeded. -/
  | send {a v : Syn .expr} {σ : STy} : Typed Γ a (.address true) → Typed Γ v σ →
      σ.implicit Γ.isBase (.int IntTy.u256) = true →
      Typed Γ (.call (.member a "send") (.positional (.cons v .nil))) .bool
  /-- `abi.encode(…)`, `abi.encodePacked(…)`, `abi.encodeWithSelector(…)`,
  `abi.encodeWithSignature(…)`: `bytes memory`. -/
  | abiEncode {g m : String} {args : Syn (.list .expr)} {σs : List STy} {k : AbiKind} :
      Γ.resolve g = Option.some (.builtin .abi) → AbiKind.ofMember m = Option.some k →
      TypedArgs Γ args σs → k.argsOK Γ.isBase σs = true →
      Typed Γ (.call (.member (.ident g) m) (.positional args)) (.bytes .memory)
  /-- `s = e` copying into storage: from `memory`, `calldata`, or a string
  literal. -/
  | assignCopy {a b : Syn .expr} {τ σ : STy} : LVal Γ a τ → Typed Γ b σ → σ.copiesTo τ = true →
      Typed Γ (.assign .assign a b) τ

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
      σ.implicit Γ.isBase τk = true → LVal Γ (.index a (.some i)) τv
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

/-! ## Statement typing -/

/-- The context of a function body with the given locals. -/
def Ctx.at (C : Ctx) (L : List (String × STy)) : Ctx := { C with locals := L }

/-- An optional loop condition, typed. -/
inductive OptCond (Γ : Ctx) : Syn (.opt .expr) → Type where
  | none : OptCond Γ .none
  | some {e : Syn .expr} : Typed Γ e .bool → OptCond Γ (.some e)

/-- An optional loop step, typed at some type. -/
inductive OptExpr (Γ : Ctx) : Syn (.opt .expr) → Type where
  | none : OptExpr Γ .none
  | some {e : Syn .expr} {τ : STy} : Typed Γ e τ → OptExpr Γ (.some e)

mutual

/-- **Statement typing**, as data, in a function body `C` (its environment,
contract, return types, `msg.value` and modifier flags, which no statement
changes): `s` is well typed with locals `L` and leaves locals `L'` (a
declaration adds one; a block's locals end with it). -/
inductive StmtD (C : Ctx) : {k : SCtx} → List (String × STy) → Syn (.stmt k) → List (String × STy) → Type where
  /-- An expression statement; in a modifier, `_;` is the placeholder, not an
  expression. -/
  | expr {k : SCtx} {L : List (String × STy)} {e : Syn .expr} {τ : STy} :
      Typed (C.at L) e τ → (C.inModifier && e.isUnderscore) = false →
      StmtD C (k := k) L (.simpleStmt (.exprStmt e)) L
  /-- `_;` in a modifier body. -/
  | placeholder {k : SCtx} {L : List (String × STy)} : C.inModifier = true →
      StmtD C (k := k) L (.simpleStmt (.exprStmt (.ident "_"))) L
  /-- `T l x;` with solc's location rule. -/
  | declVar {k : SCtx} {L : List (String × STy)} {t : Syn .typeName} {l : Option DataLoc} {x : String}
      {τ : STy} : t.ty C.env C.scope (l.getD .memory) = Option.some τ → locOK τ l false = true →
      StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t l x) .none)) ((x, τ) :: L)
  /-- `T l x = e;`: `e` converts implicitly to `T`. -/
  | declInit {k : SCtx} {L : List (String × STy)} {t : Syn .typeName} {l : Option DataLoc} {x : String}
      {e : Syn .expr} {τ σ : STy} : t.ty C.env C.scope (l.getD .memory) = Option.some τ →
      locOK τ l true = true → Typed (C.at L) e σ → σ.implicit C.isBase τ = true →
      StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t l x) (.some e))) ((x, τ) :: L)
  | block {k : SCtx} {L L' : List (String × STy)} {b : Syn (.list (.item k))} :
      ItemsD C L b L' → StmtD C L (.blockStmt (.block b)) L
  | ifThen {k : SCtx} {L L₁ : List (String × STy)} {c : Syn .expr} {s : Syn (.stmt k)} :
      Typed (C.at L) c .bool → s.isDecl = false → StmtD C L s L₁ → StmtD C L (.ifStmt c s .none) L
  | ifElse {k : SCtx} {L L₁ L₂ : List (String × STy)} {c : Syn .expr} {s t : Syn (.stmt k)} :
      Typed (C.at L) c .bool → s.isDecl = false → t.isDecl = false → StmtD C L s L₁ →
      StmtD C L t L₂ → StmtD C L (.ifStmt c s (.some t)) L
  | whileLoop {l u : Bool} {L L₁ : List (String × STy)} {c : Syn .expr} {s : Syn (.stmt ⟨true, u⟩)} :
      Typed (C.at L) c .bool → s.isDecl = false → StmtD C L s L₁ →
      StmtD C (k := ⟨l, u⟩) L (.whileStmt c s) L
  | doWhile {l u : Bool} {L L₁ : List (String × STy)} {c : Syn .expr} {s : Syn (.stmt ⟨true, u⟩)} :
      s.isDecl = false → StmtD C L s L₁ → Typed (C.at L) c .bool →
      StmtD C (k := ⟨l, u⟩) L (.doWhile s c) L
  /-- `for (; cond; post) s`. -/
  | forLoop {l u : Bool} {L L₂ : List (String × STy)} {c post : Syn (.opt .expr)}
      {s : Syn (.stmt ⟨true, u⟩)} : OptCond (C.at L) c → OptExpr (C.at L) post → s.isDecl = false →
      StmtD C L s L₂ → StmtD C (k := ⟨l, u⟩) L (.forStmt .none c post s) L
  /-- `for (init; cond; post) s`: the init's local is in scope of the rest. -/
  | forInit {l u : Bool} {L L₁ L₂ : List (String × STy)} {i : Syn .simple} {c post : Syn (.opt .expr)}
      {s : Syn (.stmt ⟨true, u⟩)} : StmtD C (k := ⟨true, u⟩) L (.simpleStmt i) L₁ →
      OptCond (C.at L₁) c → OptExpr (C.at L₁) post → s.isDecl = false → StmtD C L₁ s L₂ →
      StmtD C (k := ⟨l, u⟩) L (.forStmt (.some i) c post s) L
  | brk {u : Bool} {L : List (String × STy)} : StmtD C (k := ⟨true, u⟩) L .breakStmt L
  | cont {u : Bool} {L : List (String × STy)} : StmtD C (k := ⟨true, u⟩) L .continueStmt L
  /-- `return;` in a function without returns (solc error 6777 otherwise,
  named returns included). -/
  | ret {k : SCtx} {L : List (String × STy)} : C.rets = [] → StmtD C (k := k) L (.returnStmt .none) L
  /-- `return e;`: `e` converts implicitly to the single return type. -/
  | retVal {k : SCtx} {L : List (String × STy)} {e : Syn .expr} {τ σ : STy} : C.rets = [τ] →
      Typed (C.at L) e σ → σ.implicit C.isBase τ = true → StmtD C (k := k) L (.returnStmt (.some e)) L
  /-- `return (a, b, …);`: each component converts to its return type. -/
  | retTuple {k : SCtx} {L : List (String × STy)} {e : Syn .expr} {s : Syn (.list (.opt .expr))}
      {σ : STy} {σs : List STy} : Typed (C.at L) e σ → TypedSlots (C.at L) s σs → σs ≠ [] →
      argsFit C.isBase (σ :: σs) C.rets = true →
      StmtD C (k := k) L (.returnStmt (.some (.tuple (.some e) s))) L
  /-- `emit E(args);`: exactly one event accepts the arguments. -/
  | emit {k : SCtx} {L : List (String × STy)} {ev : String} {args : Syn (.list .expr)} {d : Decl}
      {σs : List STy} : TypedArgs (C.at L) args σs →
      ((C.at L).declsOf .event ev).filter (·.fitsParams C.env C.isBase σs) = [d] →
      StmtD C (k := k) L (.emit (.ident ev) (.positional args)) L
  /-- `revert E(args);`: exactly one error accepts the arguments. -/
  | revertError {k : SCtx} {L : List (String × STy)} {er : String} {args : Syn (.list .expr)} {d : Decl}
      {σs : List STy} : TypedArgs (C.at L) args σs →
      ((C.at L).declsOf .error er).filter (·.fitsParams C.env C.isBase σs) = [d] →
      StmtD C (k := k) L (.revert (.ident er) (.positional args)) L
  /-- The canonical rethrow, of the `bytes memory` local it names
  (`rethrowVar?`). -/
  | rethrow {k : SCtx} {L : List (String × STy)} {fl : List String} {body : Syn (.list .yulStmt)}
      {d : String} {i : Nat} : isRethrow body = true → (C.at L).resolve d = Option.some (.loc i) →
      (L.map Prod.snd)[i]? = Option.some (.bytes .memory) →
      rethrowVar? body = Option.some d →
      StmtD C (k := k) L (.assembly false fl body) L

/-- Typing of a block's items, in order. -/
inductive ItemsD (C : Ctx) : {k : SCtx} → List (String × STy) → Syn (.list (.item k)) →
    List (String × STy) → Type where
  | nil {k : SCtx} {L : List (String × STy)} : ItemsD C (k := k) L .nil L
  | stmt {k : SCtx} {L L₁ L₂ : List (String × STy)} {s : Syn (.stmt k)} {rest : Syn (.list (.item k))} :
      StmtD C L s L₁ → ItemsD C L₁ rest L₂ → ItemsD C L (.cons (.stmtItem s) rest) L₂
  | unchecked {l : Bool} {L L₁ L₂ : List (String × STy)} {b : Syn (.list (.item ⟨l, true⟩))}
      {rest : Syn (.list (.item ⟨l, false⟩))} :
      ItemsD C L b L₁ → ItemsD C L rest L₂ → ItemsD C L (.cons (.uncheckedItem (.block b)) rest) L₂

end

/-- Statement typing as a proposition. -/
def StmtOK {k : SCtx} (C : Ctx) (L : List (String × STy)) (s : Syn (.stmt k))
    (L' : List (String × STy)) : Prop := Nonempty (StmtD C L s L')

/-- Block typing as a proposition. -/
def ItemsOK {k : SCtx} (C : Ctx) (L : List (String × STy)) (b : Syn (.list (.item k)))
    (L' : List (String × STy)) : Prop := Nonempty (ItemsD C L b L')

/-! ## Laws -/

/-- A statement only adds locals. -/
theorem StmtD.locals_suffix {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)}
    (d : StmtD C L s L') : ∃ ys, L' = ys ++ L := by
  cases d <;> first
    | exact ⟨[], rfl⟩
    | exact ⟨[_], rfl⟩

/-- **Constants have their value as type**: every constant expression other
than an address literal or a bare hexadecimal literal is typed by its exact
rational. -/
theorem HasType.of_const {Γ : Ctx} {e : Syn .expr} {q : Q} (h : e.const = Option.some q)
    (ha : e.isAddressLit = false) (hx : e.hexLen? = Option.none) : HasType Γ e (.rational q) :=
  ⟨.const h ha hx⟩

end Solidity.Source
