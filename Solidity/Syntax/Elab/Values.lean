import Solidity.Syntax.Elab.Context
import Solidity.Syntax.Numeric

/-!
# The elaborator's values

Memory objects, function values, selectors and external function values,
narrow widths and byte types.

A piece of `Syntax/Elab.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics

variable {C : Contract}

variable [FreshNames]

section Elab

variable (C)

/-- A memory object of type `R` holds no mapping: solc has none in memory. -/
def memOk (R : RefTy) : Except String (PLift ((Ty.ref R).mapFree = true)) :=
  if h : (Ty.ref R).mapFree = true then pure ⟨h⟩
  else throw s!"a {Ty.ref R} in memory: it holds a mapping"

/-- The literal `n` at the numeric type `p`, if it is in `p`'s range: one
out of it is solc's compile error. -/
def litAt (Γ : NCtx) (p : PrimTy) (n : Int) : Except String (Simple C Γ.ctx p) :=
  match h : p.inRange n with
  | true => pure (.lit n h)
  | false =>
    if p.isNumeric then throw s!"the literal {n} is out of the range of {p.toStr}"
    else throw s!"a number where a {p.toStr} is expected"

/-- Arithmetic on two literals as solc folds it, exactly (a rational
constant): `+`, `-`, `*`, and `/` when it divides.  The rest is not folded. -/
def BinOp.foldLit? : BinOp → Int → Int → Option Int
  | .add, a, b | .addW, a, b => some (a + b)
  | .sub, a, b | .subW, a, b => some (a - b)
  | .mul, a, b | .mulW, a, b => some (a * b)
  | .div, a, b => if b != 0 && a % b == 0 then some (a / b) else none
  | _, _, _ => none

/-- `E.m` for an enum `E` of the contract that no local or state variable
shadows: the position of `m`. -/
def enumLit? (Γ : NCtx) : RawExpr → String → Option Nat
  | .name x, m =>
    if (Γ.lookupTy (Var.ofName x)).isNone && (C.rootType x).isNone then
      (lookupBy x C.enums).bind fun ms =>
        -- `type(E).min`, `type(E).max` (the macro's `type(min)`, `type(max)`)
        if m == "type(min)" then (if ms.isEmpty then none else some 0)
        else if m == "type(max)" then (if ms.isEmpty then none else some (ms.length - 1))
        else ms.findIdx? (· == m)
    else none
  | _, _ => none

/-! ### Function values

A function's value is its tag, its position in `C.funs` from `1`
("Function types", `Syntax.lean`); a call through a value is a dispatch over
the functions of its signature (`fnDispatch`). -/

/-- Imported implementation helpers have direct calls only. The reserved
width-table marker remains compatible with older imported contracts;
`sourceDecl` supplies the ordinary source visibility and entry distinctions. -/
def fnSource (g : String) : Bool :=
  (lookupBy (g ++ "#internalEntry") C.widths).isNone

/-- Source-only roles constrain values; native contracts retain their existing API. -/
def fnInternal (g : String) : Bool :=
  fnSource C g && ((lookupBy g C.funs).bind (·.sourceDecl)).all SourceFunction.internalValue

def fnExternalValue (g : String) : Bool :=
  fnSource C g && ((lookupBy g C.funs).bind (·.sourceDecl)).all SourceFunction.externalValue

def fnExternalEntry (g : String) : Bool :=
  fnSource C g && ((lookupBy g C.funs).bind (·.sourceDecl)).all SourceFunction.externalEntry

/-- The functions of `C` named as a value somewhere in its code (not as a
callee): only these may be reached through a value taken inside `C`. -/
def fnTaken : List String :=
  let stmts : List RawStmt := C.funs.flatMap (fun (_, d) => d.body ++ d.mods.flatMap (·.body)) ++
    (C.ctor.map (·.body)).getD []
  let es : List RawExpr := C.funs.flatMap (fun (_, d) => d.mods.flatMap (·.args)) ++
    C.inits.map (·.2)
  let ns := RawStmt.namesList stmts ++ es.flatMap RawExpr.names
  (C.funs.map (·.1)).filter fun g => fnInternal C g && ns.contains g

/-- Whether the function `d` (its modifiers too) calls through a name that is
not a function: a parameter, a local or a state variable, possibly of a
function type. -/
def callsThroughValue (d : FunDecl) : Bool :=
  let own := d.params.map (·.1) ++ RawStmt.declsList d.body ++ C.vars.map (·.1) ++
    d.mods.flatMap fun m => m.params.map (·.1) ++ RawStmt.declsList m.body
  (FunDecl.callees d).any fun h => own.contains h && !C.funs.any (·.1 == h)

/-- Whether a value of the function `g` may exist: `g` is named as a value
in the contract, or no function declared before it (nor it) calls through a
value (`fnTag` refuses `g`'s value elsewhere). -/
def fnReachable (g : String) : Bool :=
  fnInternal C g && ((fnTaken C).contains g ||
    match C.funs.findIdx? (·.1 == g) with
    | some i => !(C.funs.take (i + 1)).any (callsThroughValue C ·.2)
    | none => false)

/-- The tag of the function `g`.  One named as a value only outside `C`'s code
(a `sol{ … }` program) is refused when a function declared before it, or it,
calls through a value: that function's dispatch leaves `g` out
(`fnDispatch`), as `g` is not declared before it. -/
def fnTag (g : String) : Except String (Option Nat) := do
  unless fnInternal C g do throw s!"{g}: this declaration has no Solidity internal function value"
  let some i := C.funs.findIdx? (·.1 == g) | return none
  unless fnReachable C g do
    throw s!"{g} is taken as a value only outside the contract's functions, and a function \
        declared before it calls through a function value: name it as a value in the contract"
  return some (i + 1)

/-- The spelling of a function type at the key `k` of the width table `ws`
(its marker row, `valueRows?`). -/
def fnRow? (ws : List (String × Nat)) (k : String) : Option String :=
  ws.findSome? fun (k', _) =>
    if k'.startsWith (k ++ "#function(") then some (k'.drop (k.length + 1)) else none

/-- The function-type marker of the nearest binding of `x`. -/
def localFn? (Γ : ECtx) (x : Name) : Option String := do
  fnRow? (← lookupBy x Γ).shape ""

/-- The function type of the name `h` (a value local, else a state
variable), as `canonFnTy` reads it. -/
def fnTyOf? (Γ : ECtx) (h : String) : Option String :=
  (match lookupBy h Γ with
    | some (.val ..) => localFn? Γ h
    | some _ => none
    | none => fnRow? C.widths h).map (canonFnTy (C.enums.map fun (e : Name × List Name) => e.1))

/-- The signature of the function `d`, as a function type spelled
(`canonFnTy`), retaining the supported memory-byte return location. -/
def FunDecl.sigTy? (d : FunDecl) : Option String := do
  let comp (k : String) : Ty → Option String
    | .prim p => some ((fnRow? d.widths k).getD (declTyName d.widths k p))
    | .ref R => do
      guard (d.retMem && !d.retStorage && d.rets.any (·.1 == k) && R == bytesR)
      guard (lookupBy (k ++ "[]#bytes") d.widths == some 1)
      guard (!(d.widths.any fun (n, _) => n == k ++ "#string"))
      pure "bytesmemory"
  let ps ← d.params.mapM fun (n, T) => do
    if T matches .ref _ then none else comp n T
  let rs ← d.rets.mapM fun (n, T) => comp n T
  pure (canonFnTy (C.enums.map fun (e : Name × List Name) => e.1) (fnTyStr ps rs false))

/-- The functions a call through a value in `d` (or its modifiers) may
reach: for a callee whose function type is known (a parameter's, a local's,
a state variable's marker) the functions of that type a value may name
(`fnReachable`); for another (`callValueName`, a call statement through a
member or an element) every function the contract names as a value. -/
def FunDecl.valueCallees (d : FunDecl) : List String :=
  let fns := C.funs.map (·.1)
  let stmts := d.body ++ d.mods.flatMap (·.body)
  let locals : List (String × String) := stmts.flatMap (RawStmt.flatMapDeep fun s =>
    match s with
    | .decl (.named t) x _ => if fnTy? t then [(x, t)] else []
    | _ => [])
  let enums := C.enums.map fun (e : Name × List Name) => e.1
  let typed (ty : String) : List String :=
    C.funs.filterMap fun (g, e) =>
      if FunDecl.sigTy? C e == some (canonFnTy enums ty) && fnReachable C g then some g else none
  let viaStmt := stmts.any fun st => !(RawStmt.flatMapDeep (fun s => match s with
      | .call (.name _) _ => []
      | .call (.field _ m) _ => if ["push", "pop", "transfer"].contains m then [] else [()]
      | .call _ _ => [()]
      | _ => []) st).isEmpty
  let hs := (FunDecl.callees d).filter (!fns.contains ·)
  let some' := hs.flatMap fun h =>
    if h == callValueName then fnTaken C else
    match fnRow? d.widths h, lookupBy h locals, fnRow? C.widths h with
    | some ty, _, _ | none, some ty, _ | none, none, some ty => typed ty
    | none, none, none => []
  (if viaStmt then fnTaken C else []) ++ some'

/-- The functions of `C` reachable from `f`, a call through a value a call of
each function it may reach (`FunDecl.valueCallees`). -/
def reachableC (f : String) : List String :=
  reachableBy (fun d => FunDecl.callees d ++ FunDecl.valueCallees C d) C.funs f

/-- Whether `f` calls itself, through values too (`reachableC`). -/
def isRecursiveC (f : String) : Bool := (reachableC C f).contains f

/-- The functions mutually recursive with `f`, through values too. -/
def recPartnersC (f : String) : List String :=
  (reachableC C f).filter fun g => (reachableC C g).contains f

/-- A function type's component as a value: its primitive type and width. -/
def fnCompTy? (c : String) : Option (PrimTy × Nat) :=
  if fnTy? c then some (.uint, 256) else
  match narrowTy? c, bytesTy? c, PrimTy.ofName? c with
  | some t, _, _ => some t
  | none, some n, _ => some (.uint, 8 * n)
  | none, none, some p => some (p, 256)
  | none, none, none => if (lookupBy c C.enums).isSome then some (.uint, 256) else none

mutual

def synth (Γ : NCtx) : RawExpr → Except String (TExpr C Γ.ctx)
  | .num n => return .val .uint (.simple (← litAt C Γ .uint n))
  | .unop .neg (.num n) => return .val .int (.simple (← litAt C Γ .int (-(n : Int))))
  | .bool b => pure (.val .bool (.simple (.bool b)))
  | .name x =>
    let v := Var.ofName x
    match Γ.lookupTy v with
    | some (.val p) => do pure (.val p (.simple (.local (← Γ.idx v (.val p)))))
    | some (.alias R) => do pure (.path (.ref R) (.alias (← Γ.idx v (.alias R))))
    | some (.mem R) =>
      match hm : (Ty.ref R).mapFree with
      | true => do pure (.mpath (.ref R) (.var (← Γ.idx v (.mem R)) hm))
      | false => throw s!"{x} is a memory local of a type that holds a mapping"
    | some .old | some .oldNet => throw s!"{x} is a storage variable, not a program value"
    | some .kint => throw s!"{x} is a logical variable (KeY's `int`), not a program value"
    | none =>
      match hr : C.rootType x with
      | some T => pure (.path T (.loc (.root x hr)))
      | none => do
        -- a function as a value: its tag
        match ← fnTag C x with
        | some t => return .val .uint (.simple (← litAt C Γ .uint t))
        | none => throw s!"unknown name {x}"
  | .field e f => do
    if let some i := enumLit? C Γ e f then return .val .uint (.simple (← litAt C Γ .uint i))
    match ← synth Γ e with
    | .path (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.len b rfl))
      else throw s!"member access .{f} on an array"
    | .mpath (.ref (.array _)) b =>
      if f == "length" then pure (.val .uint (.mlen b rfl))
      -- `keccak256(b)`, `sha256(b)`, …, as `hoist` leaves it (`hashMember`)
      else if let some k := hashMember? f then pure (.val .uint (.hash k b rfl))
      else throw s!"member access .{f} on an array"
    -- a fixed-size array's length is its type's: the literal, as solc folds
    -- it.  A base that indexes is evaluated first (it may revert), so
    -- `hoist` captured it; one left is where no capture may go.
    | .path (.ref (.fixed _ n)) _ | .mpath (.ref (.fixed _ n)) _ =>
      if f != "length" then throw s!"member access .{f} on an array"
      else if e.hasIndex then
        throw "the length of an indexed fixed-size array under a short-circuit operator or in a conditional's branch"
      else return .val .uint (.simple (← litAt C Γ .uint n))
    | .path (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.path T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | .mpath (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.mpath T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | _ => throw s!"member access .{f} on a non-struct"
  | .index e k => do
    match ← synth Γ e with
    | .path (.ref (.mapping kp V)) b => pure (.path V (.loc (.index .map b (← check Γ kp k))))
    | .path (.ref (.array E)) b => pure (.path E (.loc (.index (.arr .dyn) b (← check Γ .uint k))))
    | .mpath (.ref (.array E)) b => pure (.mpath E (.loc (.index .dyn b (← check Γ .uint k))))
    -- a literal index past a fixed-size array's end is solc's compile error
    | .path (.ref (.fixed E n)) b =>
      if let .num i := k then if n ≤ i then throw s!"index {i} out of bounds of a length-{n} array"
      pure (.path E (.loc (.index (.arr .fixed) b (← check Γ .uint k))))
    | .mpath (.ref (.fixed E n)) b =>
      if let .num i := k then if n ≤ i then throw s!"index {i} out of bounds of a length-{n} array"
      pure (.mpath E (.loc (.index .fixed b (← check Γ .uint k))))
    | t => throw s!"{e.toStr} is indexed, but it is a {t.ty}, not a mapping or an array"
  | .binop op a b => do
    if let some (n, d) := (RawExpr.binop op a b).constRat? then
      if d == 0 || n % d != 0 then throw "a non-integral rational constant"
      let v := n / d
      if v < 0 then return .val .int (.simple (← litAt C Γ .int v))
      else return .val .uint (.simple (← litAt C Γ .uint v))
    -- the operand type: the first operand that is not a literal gives it
    let t ← if a.isLit && !(op matches .pow | .powW | .shl | .shr) then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? |
      throw s!"{(if a.isLit then b else a).toStr}: an operand of reference type {t.ty}"
    if p == .int && op == .pow then
      let av ← check Γ .int a
      let bv ← check Γ .uint b
      return .val .int (.checkedSignedPower av bv)
    if p == .int && op == .shr then
      let av ← check Γ .int a
      let bv ← check Γ .uint b
      -- Preserve the decision procedure's literal-count fragment after checking
      -- Solidity's unsigned count range. Nonliteral counts still saturate below.
      if let some n := b.litVal? then
        let count : Val C Γ.ctx .int := .simple (← litAt C Γ .int (min n 256))
        return .val .int (.binop .shr rfl rfl av count)
      let limit : Val C Γ.ctx .uint := .simple (← litAt C Γ .uint 256)
      -- Saturate before converting: a uint count can exceed int256.max.
      let bounded : Val C Γ.ctx .uint := .ternary (.binop .lt rfl rfl bv limit) bv limit
      let count : Val C Γ.ctx .int := .unop .toInt rfl rfl bounded
      return .val .int (.binop .shr rfl rfl av count)
    if p == .int && op == .shl then
      let av ← check Γ .int a
      let bv ← check Γ .uint b
      let word : Val C Γ.ctx .uint := .unop .toUint rfl rfl av
      return .val .int (.unop .toInt rfl rfl (.binop .shl rfl rfl word bv))
    match h : op.accepts p with
    | true => pure (.val _ (.binop op h rfl (← check Γ p a) (← check Γ p b)))
    | false => throw s!"operator {BinOp.sym op} does not take {p.toStr}"
  | .ternary c a b => do
    -- two literals: an `int` where one is negative (`c ? -1 : -127`, `mobileTy`)
    if let (some u, some v) := (a.litVal?, b.litVal?) then
      let p : PrimTy := if u < 0 || v < 0 then .int else .uint
      return .val p (.ternary (← check Γ .bool c) (← check Γ p a) (← check Γ p b))
    let t ← if a.isLit then synth Γ b else synth Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "a conditional of reference type"
    pure (.val p (.ternary (← check Γ .bool c) (← check Γ p a) (← check Γ p b)))
  | .unop op a => do
    let t ← synth Γ a
    let some ⟨p, v⟩ := t.toVal? | throw s!"{a.toStr}: an operand of reference type {t.ty}"
    match h : op.accepts p with
    | true => pure (.val _ (.unop op h rfl v))
    | false => throw s!"operator {UnOp.sym op} does not take {p.toStr}"
  | .incDec .. => throw "`++` or `−−` under a short-circuit operator or in a conditional's branch"
  | .assign .. | .opAssign .. =>
    throw "an assignment inside an expression in a conditional's branch"
  | .newArr .. => throw "`new` stands only on the right of `=`"
  | .modular op a b k => do
    let m ← check Γ .uint k
    if let .simple (.lit n _) := m then
      if n == 0 then throw s!"{op.toStr}: arithmetic modulo zero"
    pure (.val .uint (.modular op (← check Γ .uint a) (← check Γ .uint b) m))
  | .call "address" [a] => do
    if let some v := a.litVal? then
      unless 0 ≤ v && v < (2 : Int) ^ 160 do
        throw "an address literal does not fit 160 bits"
      return .val .uint (← check Γ .uint a)
    if let .env k := a then
      if k == .msgSender || k == .selfAddress then
        return .val .uint (.simple (.env k rfl))
    pure (.val .uint (.binop .mod rfl rfl (← check Γ .uint a)
      (.simple (← litAt C Γ .uint (2 ^ 160)))))
  | .call f _ => throw s!"the call {f}(…) under a short-circuit operator or in a conditional's branch"
  | .named f .. => throw s!"the constructor {f}(\{…}) under a short-circuit operator or in a conditional's branch"
  | .env k => pure (.val .uint (.simple (.env k rfl)))
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
termination_by e => (sizeOf e, 0)

/-- `e` checked at `p` through its synthesised type. -/
def checkVia (Γ : NCtx) (p : PrimTy) (e : RawExpr) : Except String (Val C Γ.ctx p) := do
  let some ⟨q, v⟩ := (← synth Γ e).toVal? |
    throw s!"a storage reference where a {p.toStr} is expected"
  if h : q = p then pure (h ▸ v) else throw s!"a {q.toStr} where a {p.toStr} is expected"
termination_by (sizeOf e, 1)

def check (Γ : NCtx) (p : PrimTy) : RawExpr → Except String (Val C Γ.ctx p)
  | .num n => return .simple (← litAt C Γ p n)
  -- a negative literal takes the type it is checked at: `int e = -5;`
  | .unop .neg (.num n) =>
    if p = .int then return .simple (← litAt C Γ p (-(n : Int)))
    else checkVia Γ p (.unop .neg (.num n))
  -- so does arithmetic on literals alone: `int e = -5 + 2;`; an operand out
  -- of `p`'s range is folded as solc folds a constant (`foldLit?`):
  -- `uint x = 2**256 - 1` written out is the literal `2**256 - 1`
  | .binop op a b => do
    if let some (n, d) := (RawExpr.binop op a b).constRat? then
      if d == 0 || n % d != 0 then throw "a non-integral rational constant"
      return .simple (← litAt C Γ p (n / d))
    if a.isLit && b.isLit && op.isArith then
      match h : op.accepts p with
      | true =>
        if hq : op.ret p = p then
          match (do pure (.binop op h hq (← check Γ p a) (← check Γ p b)) :
              Except String (Val C Γ.ctx p)) with
          | .ok v => pure v
          | .error e =>
            match a.litVal?, b.litVal? with
            | some x, some y =>
              match op.foldLit? x y with
              | some v => if p.inRange v then return .simple (← litAt C Γ p v) else throw e
              | none => throw e
            | _, _ => throw e
        else checkVia Γ p (.binop op a b)
      | false => checkVia Γ p (.binop op a b)
    else checkVia Γ p (.binop op a b)
  | e => checkVia Γ p e
termination_by e => (sizeOf e, 2)

end

/-- `e` as a storage path of type `T`. -/
def checkPath (Γ : NCtx) (T : Ty) (e : RawExpr) : Except String (SPath C Γ.ctx T) := do
  match ← synth C Γ e with
  | .path T' p =>
    if h : T' = T then pure (h ▸ p)
    else throw s!"{e.toStr}: a storage reference to a {T'} where a {T} is expected"
  | .mpath .. | .val .. => throw "a value where a storage reference is expected"

/-- A storage-copy source, retaining a compatible fixed-array shape change
as one intrinsic source rather than expanding it into element writes. -/
def checkStorageCopy (Γ : NCtx) (R : RefTy) (e : RawExpr) : Except String (Src C Γ.ctx (.ref R)) := do
  match ← synth C Γ e with
  | .path T p =>
    if ht : T = .ref R then
      match hm : (Ty.ref R).mapFree with
      | true => pure (.copy (ht ▸ p) hm)
      | false => throw "a storage copy of a type that holds a mapping"
    else match T, p with
      | .ref (.fixed E n), p =>
        match hm : E.mapFree with
        | false => throw "a storage copy of a type that holds a mapping"
        | true =>
          match R with
          | .array E' =>
            if he : E = E' then
              if hb : n < 2 ^ 256 then
                pure (he ▸ Src.fixedCopy p (.dynamic hb) hm)
              else throw "a fixed-array length exceeds the dynamic-array bound"
            else throw "an array copy changes its element type"
          | .fixed E' m =>
            if he : E = E' then
              if hf : n ≤ m then pure (he ▸ Src.fixedCopy p (.fixed m hf) hm)
              else throw "a fixed-array copy would truncate source elements"
            else throw "an array copy changes its element type"
          | _ => throw s!"{e.toStr}: incompatible storage-copy shapes {T} and {Ty.ref R}"
      | _, _ => throw s!"{e.toStr}: a storage reference to a {T} where a {Ty.ref R} is expected"
  | .mpath T p =>
    if ht : T = .ref R then pure (.copyMem (ht ▸ p))
    else match T, p with
      | .ref (.fixed E n), p =>
        match R with
        | .array E' =>
          if he : E = E' then
            if hb : n < 2 ^ 256 then pure (he ▸ Src.fixedCopyMem p (.dynamic hb))
            else throw "a fixed-array length exceeds the dynamic-array bound"
          else throw "an array copy changes its element type"
        | .fixed E' m =>
          if he : E = E' then
            if hf : n ≤ m then pure (he ▸ Src.fixedCopyMem p (.fixed m hf))
            else throw "a fixed-array copy would truncate source elements"
          else throw "an array copy changes its element type"
        | _ => throw s!"{e.toStr}: incompatible memory-to-storage copy shapes {T} and {Ty.ref R}"
      | _, _ => throw s!"{e.toStr}: a memory reference to a {T} where a {Ty.ref R} is expected"
  | _ => throw "a value where a storage reference is expected"

/-- `e` as a memory path of type `T`. -/
def checkMPath (Γ : NCtx) (T : Ty) (e : RawExpr) : Except String (MPath C Γ.ctx T) := do
  match ← synth C Γ e with
  | .mpath T' p =>
    if h : T' = T then pure (h ▸ p)
    else throw s!"{e.toStr}: a memory reference to a {T'} where a {T} is expected"
  | .path .. | .val .. => throw "a memory reference is expected"

/-- What a memory local is bound to: a memory path by identity, or a storage
path deep-copied. -/
def elabMRhs (Γ : NCtx) (R : RefTy) (e : RawExpr) : Except String (MRhs C Γ.ctx R) := do
  match ← synth C Γ e with
  | .mpath T p =>
    if h : T = .ref R then pure (.alias (h ▸ p))
    else throw s!"{e.toStr}: a memory reference to a {T} where a {Ty.ref R} is expected"
  | .path T p =>
    if h : T = .ref R then
      match hm : (Ty.ref R).mapFree with
      | true => pure (.copy (h ▸ p) hm)
      | false => throw "a copy into memory of a type that holds a mapping"
    else throw s!"{e.toStr}: a storage reference to a {T} where a {Ty.ref R} is expected"
  | .val .. => throw "a value where a memory reference is expected"

/-- The slot `b.push()` appends, as what an alias of `R` is bound to. -/
def elabPush (Γ : NCtx) (R : RefTy) (b : RawExpr) : Except String (ARhs C Γ.ctx R) := do
  match hd : (Ty.ref R).defaultOkS with
  | true => pure (.push (← checkPath C Γ (.array (.ref R)) b) hd)
  | false => throw "push() of an element whose default is not well-formed"

/-- The typed array `y = b.push();` grows. Receiver capture belongs to the
calculus so its named rule remains visible in a derivation. -/
def elabPrimPush (Γ : NCtx) (p : PrimTy) (b : RawExpr) :
    Except String (SPath C Γ.ctx (.array (.prim p))) :=
  checkPath C Γ (.array (.prim p)) b

/-- `x` may be declared: it is neither a local in scope nor a state variable. -/
def checkFresh (Γ : ECtx) (x : Name) : Except String Unit :=
  if (lookupBy x Γ).isSome || (C.rootType x).isSome then
    throw s!"{x} is already declared, or names a state variable"
  else pure ()

/-- What elaboration reads: the functions a call may name — the contract's,
and in a function's body the ones declared before it — and whether the block
is a program's own statements (`top`), where `constructor(args);` may stand,
rather than an inlined body or a branch, loop or block of the program. -/
structure ElabScope where
  funs : List (Name × FunDecl)
  top : Bool := true
  /-- The fresh indices each enclosing inlined call gave its callee's locals
  (`elabCallRet`: its parameters, return variables, renamed locals, its
  modifiers' parameters, its loops' flags), `[k₀, k₁)` per call.  A fresh
  name in one is a local, which an effect may write, not a capture
  (`captureExpr`). -/
  inlined : List (Nat × Nat) := []
  /-- Names supplied by imported source, including fresh-shaped user locals
  such as `se1`. They are mutable values, never written-out captures. -/
  mutableFreshNames : List String := []
  /-- Inside `checked { … }` or `ignoringOverflow { … }`: a narrow type's
  check is the mode's guard statement (`narrowCheck`). -/
  overflow : Option OFMode := none
  /-- Inside `unchecked { … }`: signed `-` and `/` wrap (`narrowWrapNode`);
  an inlined callee's body is checked again. -/
  unchecked : Bool := false
  /-- Inside the body of a function called externally by the contract itself
  (`this.f()`, `trySelfBody`): `msg.sender` is `address(this)` and
  `msg.value` is `0` (`RawStmt.selfFrame`), in its inlined calls too. -/
  selfFrame : Bool := false
  /-- Retain failure bytes at an externally observed entry without rewriting
  its caller environment. Default calculus elaboration keeps its old reading. -/
  retainFailureData : Bool := false
  /-- What `msg.value` reads in a self-call's frame (`RawExpr.selfFrame`):
  `0` for a `try`; in the calls a `receive` run by a value call to the
  contract inlines, a name no frame has, so that a callee reading it is not
  run (`receiveSelfBody`). -/
  selfValue : RawExpr := .num 0
  /-- The recursive functions whose bodies are being elaborated, innermost
  first: a call of one is the frame below (`elabCallRet`). -/
  recs : List RecFrame := []

/-- Where each callee's body was first elaborated: the first index its
names took, by the callee and what its elaboration reads besides
(`calleeKey`).  A later call of it elaborates it again from that index, so
that its body is the same term at every call (`elabCallRet`), and a nested
callee's body is one term however many paths reach it (`docs/automation.md`,
M6, "One body a function"). -/
structure CallMemo where
  /-- The first index each callee's names took, by its key. -/
  starts : List (String × Nat) := []
  /-- The bodies elaborated, by their key and first index: a contract and a
  block of it with the index after it, erased (`CallMemo.setBody`). -/
  bodies : List ((String × Nat) × NonScalar) := []

/-- Elaboration threads the locals in scope, newest first, and the index of
the next variable a capture declares, and reads its scope (`ElabScope`);
below them, the callees elaborated so far (`CallMemo`). -/
abbrev ElabM := ReaderT ElabScope (StateT (ECtx × Nat) (StateT CallMemo (Except String)))

instance : Inhabited CallMemo := ⟨{}⟩

/-- A checking step, in the elaborator. -/
def ElabM.lift {α : Type} (x : Except String α) : ElabM α := fun _ => StateT.lift (StateT.lift x)

/-- What a callee's elaboration reads besides its declaration: its name,
whether it runs in a self-call's frame, the overflow mode and what
`msg.value` reads there (`CallMemo`). -/
def calleeKey (f : String) (selfFrame : Bool) (sc : ElabScope) : String :=
  s!"{f}|{selfFrame}|{sc.retainFailureData}|{reprStr sc.overflow}|{reprStr sc.selfValue}"

/-- Entering a callee of key `key`: where its first call's locals were
numbered, and the index the caller is at.  For a callee that is `shared`, the
numbering goes back to its first call's, or, at its first call, is recorded. -/
def CallMemo.enter (shared : Bool) (f : String) (selfFrame : Bool) : ElabM (Option Nat × Nat) := do
  let kEntry := (← get).2
  if !shared then return (none, kEntry)
  let key := calleeKey f selfFrame (← read)
  match lookupBy key (← getThe CallMemo).starts with
  | some k =>
    modify fun (Γc, _) => (Γc, k)
    pure (some k, kEntry)
  | none =>
    modifyThe CallMemo fun m => { m with starts := (key, kEntry) :: m.starts }
    pure (none, kEntry)

/-- `body?`, compiled: the body `setBody` recorded under the key, if it is a
block of the same contract (the same object). -/
unsafe def CallMemo.bodyImpl? (C : Contract) (key : String) (k₀ : Nat) :
    ElabM (Option (SProg C × Nat)) := do
  match lookupBy (key, k₀) (← getThe CallMemo).bodies with
  | some x =>
    let e : (C' : Contract) × (SProg C' × Nat) := unsafeCast x
    if ptrAddrUnsafe e.1 == ptrAddrUnsafe C then pure (some (unsafeCast e.2)) else pure none
  | none => pure none

/-- **A shared callee's body, read back**: the body its first call elaborated
from `k₀` (`CallMemo`), and the index after it.  It is the body this call
elaborates (the elaboration reads nothing else, `calleeKey`), so the logical
reading is `none`, elaborate it again; the compiled one reads it back, so
that elaboration is linear in the functions, not in the calls. -/
@[implemented_by CallMemo.bodyImpl?]
def CallMemo.body? (C : Contract) (_key : String) (_k₀ : Nat) : ElabM (Option (SProg C × Nat)) :=
  pure none

/-- `setBody`, compiled: the block and its contract, erased. -/
unsafe def CallMemo.setBodyImpl (C : Contract) (key : String) (k₀ : Nat) (P : SProg C)
    (kEnd : Nat) : ElabM Unit :=
  let e : (C' : Contract) × (SProg C' × Nat) := ⟨C, (P, kEnd)⟩
  modifyThe CallMemo fun m => { m with bodies := ((key, k₀), unsafeCast e) :: m.bodies }

/-- Record a shared callee's body (`body?`); logically nothing. -/
@[implemented_by CallMemo.setBodyImpl]
def CallMemo.setBody (C : Contract) (_key : String) (_k₀ : Nat) (_P : SProg C) (_kEnd : Nat) :
    ElabM Unit :=
  pure ()

/-- Leaving a callee entered at `kEntry`: after a repeated one, the caller's
numbering goes on from where it was. -/
def CallMemo.leave (entry : Option Nat × Nat) : ElabM Unit :=
  if entry.1.isSome then modify fun (Γc, k) => (Γc, max k entry.2) else pure ()

/-- Run an elaboration from the scope `sc` and the state `st`, with no
callee elaborated yet. -/
def ElabM.runFrom {α : Type} (x : ElabM α) (sc : ElabScope) (st : ECtx × Nat) :
    Except String (α × (ECtx × Nat)) :=
  ((x.run sc).run st).run' {}

/-- `runFrom`, the state dropped. -/
def ElabM.runFrom' {α : Type} (x : ElabM α) (sc : ElabScope) (st : ECtx × Nat) :
    Except String α :=
  (x.runFrom sc st).map (·.1)

/-- A fresh variable for a capture, `ie1`, `sp2`: numbered past every
variable the program itself writes. -/
def freshCapture (base : String) : ElabM Var := do
  let (Γ, k) ← get
  set (Γ, k + 1)
  pure (.fresh base k)

/-- The locals in scope. -/
def ctx : ElabM ECtx := do pure (← get).1

/-- The locals in scope, named: the context a statement elaborated now is
read in. -/
def nctx : ElabM NCtx := do pure (ECtx.toNCtx (← get).1)

/-- `synth`, in the locals in scope, with them. -/
def synthM (e : RawExpr) : ElabM ((Γ : NCtx) × TExpr C Γ.ctx) := do
  let Γ ← nctx
  pure ⟨Γ, ← ElabM.lift (synth C Γ e)⟩

/-- `check`, in the locals in scope `Γ`. -/
def checkIn (Γ : NCtx) (p : PrimTy) (e : RawExpr) : ElabM (Val C Γ.ctx p) :=
  ElabM.lift (check C Γ p e)

/-- Declare `x` in scope, the newest local. -/
def declare (x : Name) (t : LocalTy) : ElabM Unit := do
  let (Γ, k) ← get
  checkFresh C Γ x
  set ((x, t) :: Γ, k)

/-- Attach inferred width/ABI metadata to the existing local `x`. -/
def declareShape (x : Name) (ws : List (String × Nat)) : ElabM Unit := do
  let (Γ, k) ← get
  let Γ ← ElabM.lift (Γ.setShape x ws)
  set (Γ, k)

/-- A capture: a fresh `base` variable (`freshCapture`), declared at `t`. -/
def captureAs (base : String) (t : LocalTy) : ElabM Var := do
  let x ← freshCapture base
  declare C (toString x) t
  pure x

/-- What `Γ` is read as after a capture, and the capture's position. -/
def afterCapture (Γ : NCtx) (x : Var) (t : LTy) : ElabM ((Γ' : NCtx) × Thin Γ.ctx Γ'.ctx × Idx Γ'.ctx t) := do
  let Γ' ← nctx
  pure ⟨Γ', ← ElabM.lift (Γ.wkTo Γ'), ← ElabM.lift (Γ'.idx x t)⟩

/-- A compound assignment's target, with a non-simple index captured into a
fresh `ie` first: `values[i + 1] += 1;` is `uint ie1 = i + 1; values[ie1] += 1;`.
The target is read in the context the capture leaves. -/
def elabOpTarget (l : RawExpr) :
    ElabM (SProg C × (Γ : NCtx) × (p : PrimTy) × OpLoc C Γ.ctx p) := do
  let ⟨Γ, t⟩ ← synthM C l
  match t with
  | .val p (.simple (.local x)) => pure ([], ⟨Γ, p, .local x⟩)
  | .path (.prim p) (.loc (.root r h)) => pure ([], ⟨Γ, p, .root r h⟩)
  | .path (.prim p) (.loc (.field b f h)) => pure ([], ⟨Γ, p, .field b f h⟩)
  | .path (.prim p) (.loc (@Loc.index _ _ _ k _ it b i)) =>
    match i.toSimple? with
    | some ie => pure ([], ⟨Γ, p, .index it b ie⟩)
    | none =>
      let x ← captureAs C "ie" (.val k)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.val k)
      pure ([.of Γ (.declLocal k x (some i))], ⟨Γ', p, .index it (b.wk th) (.local ix)⟩)
  | .mpath (.prim p) (.loc (.field b f h)) => pure ([], ⟨Γ, p, .mfield b f h⟩)
  | .mpath (.prim p) (.loc (.index a b i)) =>
    match i.toSimple? with
    | some ie => pure ([], ⟨Γ, p, .mindex a b ie⟩)
    | none =>
      let x ← captureAs C "ie" (.val .uint)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.val .uint)
      pure ([.of Γ (.declLocal .uint x (some i))], ⟨Γ', p, .mindex a (b.wk th) (.local ix)⟩)
  | _ => throw "a compound assignment needs a local or a place of value type"

/-- An inc/dec target for the assignment form, with a non-simple receiver
captured into a fresh `sp` or `mv` first: `y = folks[i].age++;` is
`Person storage sp1 = folks[i]; y = sp1.age++;`. -/
def elabIncTarget (l : RawExpr) :
    ElabM (SProg C × (Γ : NCtx) × (p : PrimTy) × (t : OpLoc C Γ.ctx p) ×' t.recvSimple = true) := do
  let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
  match hs : t.recvSimple with
  | true => pure (pre, ⟨Γ, p, t, hs⟩)
  | false =>
    match t with
    | @OpLoc.field _ _ s _ b f h =>
      let x ← captureAs C "sp" (.alias (.struct s))
      let ⟨Γ', _, ix⟩ ← afterCapture Γ x (.alias (.struct s))
      pure (pre ++ [.of Γ (.declStorage (.struct _) x (some (.path b)))],
        ⟨Γ', p, .field (.alias ix) f h, rfl⟩)
    | @OpLoc.index _ _ R _ _ it b i =>
      let x ← captureAs C "sp" (.alias R)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.alias R)
      pure (pre ++ [.of Γ (.declStorage _ x (some (.path b)))], ⟨Γ', p, .index it (.alias ix) (i.wk th), rfl⟩)
    | @OpLoc.mfield _ _ s _ b f h =>
      let x ← captureAs C "mv" (.mem (.struct s))
      let ⟨Γ', _, ix⟩ ← afterCapture Γ x (.mem (.struct s))
      pure (pre ++ [.of Γ (.declMem (.struct _) x (some (.alias b)) rfl b.mapFree)],
        ⟨Γ', p, .mfield (.var ix b.mapFree) f h, rfl⟩)
    | @OpLoc.mindex _ _ R _ a b i =>
      let x ← captureAs C "mv" (.mem R)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.mem R)
      pure (pre ++ [.of Γ (.declMem _ x (some (.alias b)) rfl b.mapFree)],
        ⟨Γ', p, .mindex a (.var ix b.mapFree) (i.wk th), rfl⟩)
    | .local _ | .root .. => nomatch hs

/-- Width and ABI metadata of the nearest binding of `x`. -/
def localShape (Γ : ECtx) (x : Name) : List (String × Nat) :=
  ((lookupBy x Γ).map LocalTy.shape).getD []

/-- A local storage mapping alias, whose binding can be rebound. -/
def storageMappingAlias? (Γ : ECtx) (e : RawExpr) : Bool :=
  match synth C Γ.toNCtx e with
  | .ok (.path (.ref (.mapping _ _)) (.alias _)) => true
  | _ => false

/-- Where the widths of the place `e` are kept: a width table, `e`'s key in
it, and `e`'s type.  A state variable's table is `Contract.widths`
(`values[i]` is `values[]`), a reference local's its shape (`m[i]` is `[]`,
`localShape`), a struct member's its struct's (`structWidths`: `p.xs[i]` is
`xs[]` of `Packed`).  A local shadows a state variable. -/
def widthPath? (Γ : ECtx) : RawExpr → Option (List (String × Nat) × String × Ty)
  | .name x =>
    match lookupBy x Γ with
    | some (.alias R ws) | some (.mem R ws) => some (ws, "", .ref R)
    | some _ => none
    | none => (C.rootType x).map (C.widths, x, ·)
  | .assign l _ =>
    if storageMappingAlias? C Γ l then widthPath? Γ l else none
  | .index e _ => do
    let (tb, k, t) ← widthPath? Γ e
    match t with
    | .ref (.array E) | .ref (.fixed E _) | .ref (.mapping _ E) => some (tb, k ++ "[]", E)
    | _ => none
  | .field e f => do
    let (_, _, .ref (.struct s)) ← widthPath? Γ e | none
    let T ← lookupBy f (structDef s)
    pure (structWidths s, f, T)
  | _ => none

/-- The type of a place of primitive type, at its width (`widthPath?`). -/
def pathWidth? (Γ : ECtx) (e : RawExpr) : Option (PrimTy × Nat) := do
  let (tb, k, .prim p) ← widthPath? C Γ e | none
  pure (p, (lookupBy k tb).getD 256)

/-- The narrow positions below the place `e` of reference type, keyed by their
path below it: `small` of `uint8[] small` is `[("[]", 8)]`. -/
def placeShape (Γ : ECtx) (e : RawExpr) : List (String × Nat) :=
  match widthPath? C Γ e with
  | some (tb, k, .ref _) => shapeUnder tb k
  | _ => []

/-- The external function type of `g`, as `canonFnTy` spells it. -/
def FunDecl.extTy? (d : FunDecl) : Option String :=
  (FunDecl.sigTy? C d).map fun ty =>
    match fnParts? ty with
    | some (ps, rs, _) => fnTyStr ps rs true
    | none => ty

/-- Whether `r` in `r.g` is a receiver, not a struct: `this`, or a value. -/
def extRecv? (Γ : ECtx) (r : RawExpr) : Option RawExpr :=
  match r with
  | .name "this" | .env .selfAddress => some (.env .selfAddress)
  | _ => match synth C (Γ.toNCtx) r with
    | .ok (.val .uint _) => some r
    | _ => none

/-- `r.g` names the function `g` of `C` at the address `r` (`extRecv?`):
the receiver and `g`. -/
def extMember? (Γ : ECtx) : RawExpr → Option (RawExpr × String)
  | .field r g =>
    if fnExternalValue C g && (lookupBy g C.funs).isSome then (extRecv? C Γ r).map (·, g) else none
  | _ => none

/-- The function type of the expression `e`, as `canonFnTy` spells it: a
name's (`fnTyOf?`), a place's marker (a struct member, an element), a
call's return's, a conditional's first branch's, `r.g`'s external type. -/
partial def fnTyOfExpr (Γ : ECtx) (e : RawExpr) : Option String :=
  let canon := canonFnTy (C.enums.map fun (e : Name × List Name) => e.1)
  match e with
  | .name x => fnTyOf? C Γ x
  | .ternary _ a _ => fnTyOfExpr Γ a
  | .call g args => do
    if g == callValueName then
      let h ← args.head?
      let ty ← fnTyOfExpr Γ h
      let (_, [r], _) ← fnParts? ty | none
      guard (fnTy? r)
      return canon r
    if let some ty := fnTyOf? C Γ g then
      let (_, [r], _) ← fnParts? ty | none
      guard (fnTy? r)
      return canon r
    let d ← lookupBy g C.funs
    let (r, .prim _) ← d.ret | none
    (fnRow? d.widths r).map canon
  | e =>
    match extMember? C Γ e with
    | some (_, g) => (lookupBy g C.funs).bind (FunDecl.extTy? C)
    | none => do
      let (tb, k, .prim _) ← widthPath? C Γ e | none
      (fnRow? tb k).map canon

/-- A type written in `abi.decode`'s types: `T`, `T[]`, `T[][]`, `T[k]`. -/
partial def abiTyExpr? : RawExpr → Option RawTy
  | .name t =>
    if t.endsWith "[]" then (abiTyExpr? (.name (t.dropRight 2))).map .array else some (.named t)
  | .index t (.num m) => (abiTyExpr? t).map (.fixed · m)
  | .call "#abiArrayType" [t] => (abiTyExpr? t).map .array
  | _ => none

/-- The narrow positions of a value of reference type: a place's
(`placeShape`), a `new`'s type's, a function's return's, a conditional's
first branch's (`narrowWholeAt?` admits one whose branches agree). -/
def exprShape (Γ : ECtx) : RawExpr → List (String × Nat)
  | .newArr T _ => ((elabTyW C T).toOption.map (·.2)).getD []
  | .ternary _ a _ => exprShape Γ a
  | .call "#sliceCopy" [v] | .call "#sliceRaw" [v, _, _]
  | .call "#sliceDesc" [v, _, _] => exprShape Γ v
  | .call f as =>
    if (f == "bytes" || f == "string") && as.length == 1 && (lookupBy f C.funs).isNone then
      dynBytesRowsOf f else
    if f == "string.concat" && (lookupBy f C.funs).isNone then dynBytesRowsOf "string" else
    if f == bytesLitName || (encodeBuiltin f && (lookupBy f C.funs).isNone) then dynBytesRows else
    -- `abi.decode` of a byte string (`abiDecodeBytes`)
    if (f == "abi.decode" || f == "#abiDecode") && (lookupBy f C.funs).isNone then
      match as with
      | _ :: T :: _ =>
        -- Use the same recursive type reader as the decoder. Compound fixed
        -- and dynamic dimensions retain their nested width/nominal rows.
        (((abiTyExpr? T).bind fun T => (elabTyW C T).toOption).map (·.2)).getD []
      | _ => []
    else
    match lookupBy f C.funs with
    | some d => match d.ret with
      | some (r, .ref _) => shapeUnder d.widths r
      | _ => []
    | none =>
      let ty := if f == callValueName then as.head?.bind (fnTyOfExpr C Γ) else fnTyOf? C Γ f
      if (ty.bind fnParts?).any (fun (ps, rs, ext) =>
          !ext && ps.isEmpty && rs == ["bytesmemory"]) then dynBytesRows else []
  | e => placeShape C Γ e

/-- An assignment expression keeps its mapping target's declared shape.
Admission checks the RHS shape separately. -/
theorem mappingAssignmentShape (Γ : ECtx) (l r : RawExpr)
    (h : storageMappingAlias? C Γ l = true) :
    exprShape C Γ (.assign l r) = placeShape C Γ l := by
  simp only [exprShape, placeShape, widthPath?, h, ↓reduceIte]

/-- A computed Error reason retains its source string type before byte casts
and ABI lowering erase it. Raw assembly buffers need no string marker. -/
def stringReason? (Γ : ECtx) : RawExpr → Bool
  | .ternary _ a b => stringReason? Γ a && stringReason? Γ b
  | .call "string" [a] =>
    match a.bytesLit? with
    | none => true
    | some bs => (String.fromUTF8? ⟨bs.toArray.map UInt8.ofNat⟩).isSome
  | .call "string.concat" as => as.attach.all fun ⟨a, _ha⟩ => stringReason? Γ a
  | e =>
    match e.bytesLit? with
    | some bs => (String.fromUTF8? ⟨bs.toArray.map UInt8.ofNat⟩).isSome
    | none => (exprShape C Γ e).contains ("#string", 1)

/-- Fixed byte prefixes accept byte strings, retaining the string/bytes ABI distinction. -/
def dynamicBytesExpr (Γ : ECtx) : RawExpr → Bool
  | .ternary _ a b => dynamicBytesExpr Γ a && dynamicBytesExpr Γ b
  | e =>
    let ws := exprShape C Γ e
    sameShape ws dynBytesRows && !ws.any (fun row => row.1.endsWith "#string")

/-- The narrow positions of `ws`, below a place written `·` (`·[]` 8 bits wide). -/
def shapeStr (ws : List (String × Nat)) : String :=
  if ws.isEmpty then "none" else ", ".intercalate (ws.map fun (k, n) => s!"·{k} {n} bits wide")

/-- A whole use of `e` where `ws` is expected: the narrow positions must agree
(solc converts no reference type to one of another element type). -/
def shapeCheck (Γ : ECtx) (ws : List (String × Nat)) : RawExpr → Except String Unit
  | .call "#array" _ => pure () -- checked on the inferred memory local after hoisting
  | .ternary _ a b => do shapeCheck Γ ws a; shapeCheck Γ ws b
  | e => do
  let got := exprShape C Γ e
  unless sameShape got ws do
    throw s!"{e.toStr} has narrow positions {shapeStr got} where {shapeStr ws} are expected: \
      solc converts no reference type to one of another element type"

/-- A storage value copy may widen integer elements. Unlike an alias, the
copy observes values rather than reusing an object at a different type.
Noninteger source markers stay exact; byte widening needs a value shift. -/
def storageCopyShape (Γ : ECtx) (ws : List (String × Nat)) (e : RawExpr) : Except String Unit := do
  if e matches .call "#array" _ then return ()
  let got := exprShape C Γ e
  if sameShape got ws then return ()
  let marks := fun (rs : List (String × Nat)) => rs.filter (fun r => r.1.contains '#')
  unless (marks got).all (marks ws |>.contains ·) && (marks ws).all (marks got |>.contains ·) do
    throw "a storage copy changes a noninteger source type"
  let keys := ((got ++ ws).filter (fun r => !r.1.contains '#')).map (·.1)
  unless keys.all (fun k => (lookupBy k got).getD 256 ≤ (lookupBy k ws).getD 256) do
    throw "a storage copy would narrow an integer element"

/-- Whether `e` names, whole, a place with a narrow position below it (`small`
of `uint8[] small`, `lists[i]` of `mapping(uint => uint8[]) lists`, a
`uint8[] memory m`). -/
def narrowWhole (Γ : ECtx) (e : RawExpr) : Bool := !(placeShape C Γ e).isEmpty

/-! ### Selectors and external function values

An external function's value is its address and its selector, packed as
solc packs them in the ABI's `bytes24`: `address * 2^32 + selector`
(`docs/semantic-gaps.md`, "Function types").  A selector is the first four
bytes of the Keccak-256 of the function's canonical signature, folded here
as solc folds it (`Keccak.selector`); a signature's types are read off the
width table's markers (`#address`, `#bytes`, `#enum`, `#string`, a function
type's). -/

/-- `2^32`: an external function value's address is above its selector. -/
def selShift : Nat := 2 ^ 32

/-- The canonical ABI name of the type `T` at the key `k` of the width table
`ws`, as a signature writes it: `uint256`, `address`, `bytes4`, `string`,
`uint8[]`, a struct as the tuple of its members.  None for a mapping. -/
partial def abiTyName (ws : List (String × Nat)) (k : String) : Ty → Option String
  | .prim .bool => some "bool"
  | .prim .int => some s!"int{(lookupBy k ws).getD 256}"
  | .prim .uint =>
    if (lookupBy (k ++ "#address") ws).isSome then some "address"
    else if let some n := lookupBy (k ++ "#bytes") ws then some s!"bytes{n}"
    else if (lookupBy (k ++ "#enum") ws).isSome then some "uint8"
    else if (fnRow? ws k).isSome then some "function"
    else some s!"uint{(lookupBy k ws).getD 256}"
  | .ref (.array E) =>
    if lookupBy (k ++ "[]#bytes") ws == some 1 then
      some (if (lookupBy (k ++ "#string") ws).isSome then "string" else "bytes")
    else (abiTyName ws (k ++ "[]") E).map (· ++ "[]")
  | .ref (.fixed E n) => (abiTyName ws (k ++ "[]") E).map (s!"{·}[{n}]")
  | .ref (.struct s) => do
    let ms ← (structDef s).mapM fun (f, T) => abiTyName (structWidths s) f T
    pure s!"({",".intercalate ms})"
  | .ref (.mapping ..) => none

/-- The canonical signature of the function `g` of `C`, `g(uint256,address)`. -/
def fnSignature? (g : String) : Option String := do
  guard (fnSource C g)
  let d ← lookupBy g C.funs
  if let some source := d.sourceDecl then
    guard source.externalValue
    return ← source.signature
  let ps ← d.params.mapM fun (n, T) => abiTyName d.widths n T
  pure s!"{g}({",".intercalate ps})"

/-- The custom error `e` of `C` and its canonical signature, `E(uint256,address)`. -/
def errorSignature? (e : String) : Option (FunDecl × String) := do
  let d ← lookupBy e C.errors
  let ps ← d.params.mapM fun (n, T) => abiTyName d.widths n T
  pure (d, s!"{e}({",".intercalate ps})")

/-- The selector of the function `g` of `C` (`Keccak.selector`). -/
def fnSelector? (g : String) : Option Nat := do
  guard (fnExternalValue C g)
  let d ← lookupBy g C.funs
  if let some source := d.sourceDecl then
    match source.callable with
    | .getter selector => return selector.val
    | .abi _ _ (some selector) => return selector.val
    | .abi _ _ none => return Keccak.selector (← source.signature)
    | _ => none
  else (fnSignature? C g).map Keccak.selector

/-- Function ABI components retain the parameter markers that dispatch's
canonical signature intentionally erases. Mutability is not represented here. -/
def FunDecl.rawExtTy? (d : FunDecl) : Option String := do
  let component (n : Name) (t : Ty) : Option String :=
    (fnRow? d.widths n).orElse fun _ => abiTyName d.widths n t
  let ps ← d.params.mapM fun (n, t) => component n t
  let rs ← d.rets.mapM fun (n, t) => component n t
  pure (fnTyStr ps rs true)

/-- A function value's source components before dispatch canonicalization. -/
partial def rawFnTyOfExpr? (Γ : ECtx) : RawExpr → Option String
  | .name g =>
    match lookupBy g Γ with
    | some (.val ..) => localFn? Γ g
    | some _ => none
    | none => fnRow? C.widths g
  | .ternary _ a b => do
    let ta ← rawFnTyOfExpr? Γ a
    guard (rawFnTyOfExpr? Γ b == some ta)
    pure ta
  | .call g _ => do
    let d ← lookupBy g C.funs
    let (r, .prim _) ← d.ret | none
    fnRow? d.widths r
  | e => do
    if let some (_, g) := extMember? C Γ e then
      return ← (lookupBy g C.funs).bind FunDecl.rawExtTy?
    let (tb, k, .prim _) ← widthPath? C Γ e | none
    fnRow? tb k

/-- Raw ABI parameter spellings, before function-dispatch canonicalization
forgets address, enum and fixed-byte distinctions. -/
def encodeCallTypes? (Γ : ECtx) (h : RawExpr) : Option (List String) := do
  let declared (g : String) : Option (List String) := do
    let d ← lookupBy g C.funs
    d.params.mapM fun (n, T) => (fnRow? d.widths n).orElse fun _ => abiTyName d.widths n T
  match h with
  | .name g =>
    if (lookupBy g Γ).isNone && (C.rootType g).isNone then
      if let some ps := declared g then return ps
    let ty ← (localFn? Γ g).orElse fun _ => fnRow? C.widths g
    let (ps, _, true) ← fnParts? ty | none
    pure ps
  | e =>
    if let some (_, g) := extMember? C Γ e then return ← declared g
    let (tb, k, .prim _) ← widthPath? C Γ e | none
    let ty ← fnRow? tb k
    let (ps, _, true) ← fnParts? ty | none
    pure ps

/-- A capture of the reference `e`, declared at `t`, with its narrow positions
(`exprShape`, `LocalTy.shape`). -/
def captureRef (base : String) (t : LocalTy) (e : RawExpr) : ElabM Var := do
  let ws := exprShape C (← ctx) e
  captureAs C base (t.withShape ws)

/-- `e` as a simple value of type `p`, captured into a fresh local first
when it is not one: read in the context the capture leaves. -/
def simpleOf (p : PrimTy) (e : RawExpr) : ElabM (SProg C × (Γ : NCtx) × Simple C Γ.ctx p) := do
  let Γ ← nctx
  let v ← checkIn C Γ p e
  match v.toSimple? with
  | some se => pure ([], ⟨Γ, se⟩)
  | none =>
    let x ← captureAs C "se" (.val p)
    let ⟨Γ', _, ix⟩ ← afterCapture Γ x (.val p)
    pure ([.of Γ (.declLocal p x (some v))], ⟨Γ', .local ix⟩)

/-- The size of `new T[](n)` as a simple value: a size that is not one is
captured into a fresh `uint` first (KeY's `memoryArrayFreshAlloc` takes a
`SimpleExpression`). -/
def elabSize (n : RawExpr) : ElabM (SProg C × (Γ : NCtx) × Simple C Γ.ctx .uint) :=
  simpleOf C .uint n

/-- The array type `new T(n)` allocates, if it may be allocated. -/
def elabNewTy (T : RawTy) : ElabM ((R : RefTy) ×' R.newArrOk = true) := do
  let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw "`new` of a value type"
  match h : R.newArrOk with
  | true => pure ⟨R, h⟩
  | false => throw "`new` of an array whose elements a memory array cannot hold"

/-! ### Narrow widths -/

/-- Two operands' type: a literal takes the other's, and the wider wins (solc
converts a `uint8` to a `uint16` implicitly). -/
def joinIT : Option (PrimTy × Nat) → Option (PrimTy × Nat) → Option (PrimTy × Nat)
  | none, t => t
  | t, none => t
  | some (p, n), some (_, m) => some (p, max n m)

/-- A reference type. -/
def isRefTy : Ty → Bool
  | .ref _ => true
  | .prim _ => false

mutual
/-- A use of a place `narrowWhole` names other than through an index, a
member (`.length`, `.push`, `.pop`), `delete`, or where its narrow positions
are checked against the target's (a reference local's initializer, a
reference assignment, a function's reference argument: `shapeCheck`).  A
reference type has no width (`uint[]` is `uint8[]`'s `Ty`), so any other use
(an operand of a conditional, a tuple, a named argument) would lose it. -/
partial def narrowWholeUse? (Γ : ECtx) : RawExpr → Option RawExpr
  | e@(.name _) => if narrowWhole C Γ e then some e else none
  | e@(.index b k) =>
    if narrowWhole C Γ e then some e else (narrowBase? Γ b).orElse fun _ => narrowWholeUse? Γ k
  | e@(.field b _) => if narrowWhole C Γ e then some e else narrowBase? Γ b
  -- a function's reference argument: its shape is checked against the
  -- parameter's (`elabCallRet`); a struct constructor's arguments, each
  -- against its member's, by the member writes it is lowered to (`hoist`)
  | .call "#array" as => as.findSome? (narrowWholeAt? Γ)
  | .call f as =>
    if f.startsWith "#bytesPrefix" && (lookupBy f C.funs).isNone then
      -- The prefix lowering validates the bytes kind before hoisting.
      as.findSome? fun a => narrowWholeAt? Γ (match a with
        | .call "bytes" [v] => v
        | _ => a)
    else
    if (lookupBy f C.funs).isNone && !(C.structFields f).isEmpty then
      as.findSome? (narrowWholeAt? Γ)
    -- a byte string read whole by `keccak256` or the ABI (`abiKind` admits
    -- no other array)
    else if (lookupBy f C.funs).isNone &&
        (byteBuiltin f || f == "erc7201" || f == sliceViewName || f.startsWith "#slice" ||
          ((bytesTy? f).isSome && as.length == 1 &&
            as.all (fun a => dynamicBytesExpr C Γ a))) then
      as.findSome? (narrowBase? Γ)
    else
    let refs : List Bool := ((lookupBy f C.funs).map fun d => d.params.map fun (_, T) => isRefTy T).getD []
    as.zipIdx.findSome? fun (a, i) =>
      if refs.getD i false then narrowWholeAt? Γ a else narrowWholeUse? Γ a
  | .assign a b =>
    if storageMappingAlias? C Γ a && sameShape (placeShape C Γ a) (exprShape C Γ b) then
      (narrowWholeAt? Γ a).orElse fun _ => narrowWholeAt? Γ b
    else (narrowWholeUse? Γ a).orElse fun _ => narrowWholeUse? Γ b
  | .binop _ a b | .opAssign _ a b => (narrowWholeUse? Γ a).orElse fun _ => narrowWholeUse? Γ b
  | .unop _ a | .incDec _ a | .newArr _ a => narrowWholeUse? Γ a
  | .ternary c a b =>
    ((narrowWholeUse? Γ c).orElse fun _ => narrowWholeUse? Γ a).orElse fun _ => narrowWholeUse? Γ b
  | .named f _ as =>
    if (lookupBy f C.funs).isNone && !(C.structFields f).isEmpty then as.findSome? (narrowWholeAt? Γ)
    else as.findSome? (narrowWholeUse? Γ)
  | .tuple as => as.findSome? (narrowWholeUse? Γ)
  | .modular _ a b k => [a, b, k].findSome? (narrowWholeUse? Γ)
  | _ => none

/-- `narrowBase?` at a whole use whose shape is checked (`shapeCheck`): a
conditional's branches too, when their narrow positions agree (solc has no
common type of `uint8[]` and `uint[]`). -/
partial def narrowWholeAt? (Γ : ECtx) : RawExpr → Option RawExpr
  | e@(.ternary c a b) =>
    if sameShape (exprShape C Γ a) (exprShape C Γ b) then
      ((narrowWholeUse? Γ c).orElse fun _ => narrowWholeAt? Γ a).orElse fun _ => narrowWholeAt? Γ b
    else some e
  | e => narrowBase? Γ e

/-- `narrowWholeUse?` of an index's or a member's base, or of a use whose
shape is checked (`shapeCheck`): its own indices only. -/
partial def narrowBase? (Γ : ECtx) : RawExpr → Option RawExpr
  | .index b k => (narrowBase? Γ b).orElse fun _ => narrowWholeUse? Γ k
  | .field b _ => narrowBase? Γ b
  | .name _ => none
  | e => narrowWholeUse? Γ e
end

/-- The smallest integer type holding the literals `u` and `v` (solc's mobile
type, of both): `uintN` when neither is negative, else `intN`. -/
def mobileTy (u v : Int) : PrimTy × Nat :=
  let signed := u < 0 || v < 0
  let fits (n : Nat) (w : Int) : Bool :=
    if signed then -((2 ^ (n - 1) : Nat) : Int) ≤ w && w < ((2 ^ (n - 1) : Nat) : Int)
    else w < ((2 ^ n : Nat) : Int)
  let n := ((List.range 32).map (8 * · + 8)).find? (fun n => fits n u && fits n v) |>.getD 256
  (if signed then .int else .uint, n)

/-- The integer type solc gives `e`: `some (p, n)` for `n` bits (a value not
built from a narrow variable or a cast is 256 bits wide), `none` for a literal,
which takes the type of what it meets.  `a ** b`, `a << b` and `a >> b` have
`a`'s type (a literal base is 256 bits wide, solc ≥ 0.7). -/
def intTyOf (Γ : ECtx) : RawExpr → Option (PrimTy × Nat)
  | .num _ => none
  | .name x =>
    match lookupBy x Γ with
    | some (.val p n _) => some (p, n)
    | some _ => some (.uint, 256)
    | none =>
      match C.rootType x with
      | some (.prim p) => some (p, (lookupBy x C.widths).getD 256)
      | _ => some (.uint, 256)
  | .unop .not _ => some (.bool, 256)
  | .unop .toInt _ => some (.int, 256)
  | .unop .toUint _ => some (.uint, 256)
  | .unop _ a => intTyOf Γ a
  | .binop op a b =>
    if !op.isArith then some (.bool, 256)
    else if op matches .pow | .powW | .shl | .shr then
      match a.litVal? with
      | some v => some (if v < 0 then .int else .uint, 256)
      | none => intTyOf Γ a
    else joinIT (intTyOf Γ a) (intTyOf Γ b)
  -- solc's conditional has the common type of its branches' mobile types: a
  -- literal's is the smallest type holding it (`c ? 63 : 255` is a `uint8`,
  -- `c ? x : 300` a `uint16` at `uint8 x`)
  | .ternary _ a b =>
    match a.litVal?, b.litVal? with
    | some u, some v => some (mobileTy u v)
    | some u, none => joinIT (some (mobileTy u u)) (intTyOf Γ b)
    | none, some v => joinIT (intTyOf Γ a) (some (mobileTy v v))
    | none, none => joinIT (intTyOf Γ a) (intTyOf Γ b)
  | .incDec _ e => intTyOf Γ e
  | .call f _ =>
    -- a cast's type, else a declared function's return at its width
    match castTy? f, lookupBy f C.funs with
    | some t, _ => some t
    | none, some d =>
      match d.ret with
      | some (r, .prim p) => some (p, (lookupBy r d.widths).getD 256)
      | _ => some (.uint, 256)
    | none, none => some (.uint, 256)
  | .bool _ => some (.bool, 256)
  -- an element or a member: its declared width (`uint8[] values`, `p.a` of a
  -- `Packed p`)
  | .index e k => (pathWidth? C Γ (.index e k)).orElse fun _ => some (.uint, 256)
  -- `ripemd160`'s and `ecrecover`'s word is below `2^160` (`hashMember`)
  | .field e f =>
    if hashMember? f matches some .ripemd160 | some .ecrecover then some (.uint, 160)
    else (pathWidth? C Γ (.field e f)).orElse fun _ => some (.uint, 256)
  | _ => some (.uint, 256)

/-- `e`'s width in bits: `intTyOf`'s, `256` for a literal. -/
def widthIn (Γ : ECtx) (e : RawExpr) : Nat := ((intTyOf C Γ e).map (·.2)).getD 256

/-! ### Byte types

A `bytesN` is a `uint` of `8N` bits (`valueRows?`, `Syntax.lean`); what solc
does differently from a `uint8N` is rewritten before the statement is
elaborated (`bytesPure`), where the marker rows tell which positions hold
bytes. -/

/-- The `bytesN` marker attached to the nearest binding of `x`. -/
def localBytes? (Γ : ECtx) (x : Name) : Option Nat := do
  lookupBy "#bytes" (← lookupBy x Γ).shape

/-- The marker `m` (`#address`, `#enum`) attached to the local `x`. -/
def localMark? (Γ : ECtx) (x : Name) (m : String) : Option Nat := do
  lookupBy m (← lookupBy x Γ).shape

/-- The marker `m` of the value `e`'s static type, as the ABI reads it: a
variable's, an element's or a member's (`widthPath?`), a call's return's;
`msg.sender` and `address(this)` are `address`es, an enum's member and
conversion `E(x)` an enum's. -/
def markOf? (Γ : ECtx) (m : String) : RawExpr → Option Nat
  | .name x =>
    match lookupBy x Γ with
    | some (.val ..) => localMark? Γ x m
    | some _ => none
    | none => lookupBy (x ++ m) C.widths
  | .env k =>
    if m == "#address" && (k == .msgSender || k == .selfAddress) then some 20 else none
  | .call "address" [_] => if m == "#address" then some 20 else none
  | .ternary _ a b => do
    let left ← markOf? Γ m a
    let right ← markOf? Γ m b
    guard (left == right)
    pure left
  | .call f _ =>
    if m == "#enum" && (lookupBy f C.enums).isSome then some 1 else do
      let d ← lookupBy f C.funs
      let (r, .prim _) ← d.ret | none
      lookupBy (r ++ m) d.widths
  | e@(.field b g) =>
    if m == "#enum" && (enumLit? C Γ.toNCtx b g).isSome then some 1 else do
      let (tb, k, .prim _) ← widthPath? C Γ e | none
      lookupBy (k ++ m) tb
  | e@(.index ..) => do
    let (tb, k, .prim _) ← widthPath? C Γ e | none
    lookupBy (k ++ m) tb
  | _ => none

/-- Two operands' `bytesN`: a literal takes the other's, the longer wins. -/
def joinBytes : Option Nat → Option Nat → Option Nat
  | none, t => t
  | t, none => t
  | some n, some m => some (max n m)

/-- The `N` of `e` when solc types it `bytesN`: a variable, an element, a
member or a function's return marked so, a conversion `bytesN(…)`, an
element `b[i]` of a `bytesN` (a `bytes1`), and the bitwise operators of
them. -/
partial def bytesOf? (Γ : ECtx) : RawExpr → Option Nat
  | .name x =>
    match lookupBy x Γ with
    | some (.val ..) => localBytes? Γ x
    | some _ => none
    | none => lookupBy (x ++ "#bytes") C.widths
  | e@(.index b _) =>
    if (bytesOf? Γ b).isSome then some 1 else do
      let (tb, k, .prim _) ← widthPath? C Γ e | none
      lookupBy (k ++ "#bytes") tb
  | .field _ "length" => none
  | e@(.field f m) => do
    if m == "selector" && ((extMember? C Γ f).isSome ||
        ((fnTyOfExpr C Γ f).bind fnParts?).any (·.2.2)) then return 4
    let (tb, k, .prim _) ← widthPath? C Γ e | none
    lookupBy (k ++ "#bytes") tb
  | .call f _ =>
    match bytesTy? f with
    | some n => some n
    | none => do
      -- the builtin `keccak256` is a `bytes32`
      if (f == "keccak256" || f == "sha256") && (lookupBy f C.funs).isNone then return 32
      if f == "ripemd160" && (lookupBy f C.funs).isNone then return 20
      let d ← lookupBy f C.funs
      let (r, .prim _) ← d.ret | none
      lookupBy (r ++ "#bytes") d.widths
  | .binop op a b =>
    if op matches .band | .bor | .bxor then joinBytes (bytesOf? Γ a) (bytesOf? Γ b)
    else if op matches .shl | .shr then bytesOf? Γ a
    else none
  | .unop .bnot a => bytesOf? Γ a
  | .ternary _ a b => joinBytes (bytesOf? Γ a) (bytesOf? Γ b)
  | .assign l _ | .opAssign _ l _ => bytesOf? Γ l
  | _ => none

/-- ABI aliases normalize without erasing integer widths or byte/address kinds. -/
partial def abiFnType (T : String) : String :=
  match fnParts? T with
  | some (ps, rs, ext) => fnTyStr (ps.map abiFnType) (rs.map abiFnType) ext
  | none =>
    if T.startsWith "(" && T.endsWith ")" then
      "(" ++ ",".intercalate ((splitTopCommas ((T.drop 1).dropRight 1)).map abiFnType) ++ ")"
    else match T.splitOn "[" with
    | base :: rest@(_ :: _) => abiFnType base ++ "[" ++ "[".intercalate rest
    | _ => if T == "uint" then "uint256" else if T == "int" then "int256" else T

/-- Check the implicit conversion before contextual ABI encoding. The raw
syntax retains widths/byte markers, but not nominal enum identity; that limit
is shared with declaration metadata, not repaired by an explicit narrowing cast. -/
def encodeCallArg (Γ : ECtx) (T : String) (a : RawExpr) : Except String RawExpr := do
  let bad : Except String RawExpr := throw s!"abi.encodeCall: {a.toStr} is not implicitly convertible to {T}"
  if let some n := bytesTy? T then
    if let some bs := a.bytesLit? then
      if bs.length ≤ n then return .call T [a] else return ← bad
    if let some m := bytesOf? C Γ a then
      if m ≤ n then return .call T [a] else return ← bad
    return ← bad
  if let some expected := fnParts? T then
    if expected.2.2 && (rawFnTyOfExpr? C Γ a).map abiFnType == some (abiFnType T) then return a
    return ← bad
  if T == "bytes" || T == "string" then
    if a.bytesLit?.isSome then return a
    let ws := exprShape C Γ a
    if ws.contains ("[]#bytes", 1) && ((T == "string") == ws.contains ("#string", 1)) then return a
    return ← bad
  let prim := if T == "bool" then some (PrimTy.bool, 256)
    else if T == "address" then some (PrimTy.uint, 160) else castTy? T
  if let some (p, n) := prim then
    if (bytesOf? C Γ a).isSome || (rawFnTyOfExpr? C Γ a).isSome then return ← bad
    let addr := (markOf? C Γ "#address" a).isSome ||
      (match a with | .call "address" [_] => true | _ => false)
    if T == "address" then
      if addr then return a
      -- Numeric address literals in the imported AST have already passed solc.
      if let some v := a.litVal? then
        if 0 ≤ v && v < (2^160 : Nat) then return a
      return ← bad
    if addr || (markOf? C Γ "#enum" a).isSome then return ← bad
    if let some v := a.litVal? then
      if p == .bool then return ← bad
      let (lo, hi) := intRange p n
      if lo ≤ v && v ≤ hi then return .call T [a]
      return ← bad
    let some (q, m) := intTyOf C Γ a | return ← bad
    if p == .bool then
      if q == .bool then return a else return ← bad
    if q == .bool || n < m || (p == .uint && q == .int) ||
        (p == .int && q == .uint && n ≤ m) then return ← bad
    -- Reference expressions must not pass through intTyOf's fallback.
    if let .ok (.path (.ref _) _) := synth C Γ.toNCtx a then return ← bad
    if let .ok (.mpath (.ref _) _) := synth C Γ.toNCtx a then return ← bad
    return .call T [a]
  let ty ← match a with
    | .newArr R _ => (elabTyW C R).map (·.1)
    | .call f _ => do
      let some d := lookupBy f C.funs | throw s!"abi.encodeCall: unknown reference argument {a.toStr}"
      let some (_, t) := d.ret | throw "abi.encodeCall: argument has no return value"
      pure t
    | _ => do
      match ← synth C Γ.toNCtx a with
      | .path t _ | .mpath t _ => pure t
      | _ => throw s!"abi.encodeCall: {a.toStr} is not a reference argument"
  if abiTyName (exprShape C Γ a) "" ty == some T then return a
  return ← bad

/-- External function values and their members, as `uint`s: `r.g` (`g` a
function of `C`, `r` an address or `this`) is `r * 2^32 + selector(g)`;
`h.selector` of an external function value `h` is `h % 2^32`, `h.address`
`h / 2^32` (`r.g.selector` the literal, `r.g.address` `r`), the remainder
written `h - h / 2^32 * 2^32`.  The callee of
a call through a value (`callValueName`) is left as written. -/
partial def fnPure (Γ : ECtx) : RawExpr → Except String RawExpr
  | .call f (h :: as) =>
    -- `abi.encodeCall(this.g, …)`: the function, whose selector it reads
    if f == "abi.encodeCall" then do
      let h' ← match extMember? C Γ h with
        | some (r, g) => do pure (.field (← fnPure Γ r) g)
        | none => fnPure Γ h
      let [t] := as | throw "abi.encodeCall takes a function and an argument tuple"
      let actual := match t with | .tuple xs => xs | a => [a]
      let some expected := encodeCallTypes? C Γ h |
        throw "abi.encodeCall: the function's ABI parameter types are unavailable"
      unless actual.length == expected.length do
        throw s!"abi.encodeCall takes {expected.length} arguments, not {actual.length}"
      let converted ← (expected.zip actual).mapM fun (T, a) => do
        let a ← encodeCallArg C Γ T a
        let lowered ← fnPure Γ a
        if ((rawFnTyOfExpr? C Γ a).bind fnParts?).any (·.2.2) then
          return RawExpr.call "bytes24" [lowered]
        return lowered
      return .call f [h', .tuple converted]
    else if encodeBuiltin f && (lookupBy f C.funs).isNone then do
      let encoded ← (h :: as).mapM fun a => do
        let lowered ← fnPure Γ a
        if let some ty := rawFnTyOfExpr? C Γ a then
          if f == "bytes.concat" || f == "string.concat" then
            throw "concat does not accept function values"
          let some (_, _, true) := fnParts? ty |
            throw "ABI encoding an internal function value is not allowed"
          return RawExpr.call "bytes24" [lowered]
        if let .name g := a then
          if (lookupBy g Γ).isNone && (C.rootType g).isNone &&
              fnSource C g && (lookupBy g C.funs).isSome then
            throw "ABI encoding an internal function value is not allowed"
        return lowered
      return .call f encoded
    else if f == callValueName then do
      let h' ← match extMember? C Γ h with
        | some (r, g) => do pure (.field (← fnPure Γ r) g)
        | none => fnPure Γ h
      pure (.call f (h' :: (← as.mapM (fnPure Γ))))
    else do pure (.call f ((← fnPure Γ h) :: (← as.mapM (fnPure Γ))))
  | .field e m => do
    if m == "selector" || m == "address" then
      if let some (r, g) := extMember? C Γ e then
        if m == "address" then return ← fnPure Γ r
        let some sel := fnSelector? C g | throw s!"{g}: its signature has a type the ABI does not name"
        return .num sel
      if let some ty := fnTyOfExpr C Γ e then
        if let some (_, _, true) := fnParts? ty then
          let e' ← fnPure Γ e
          -- the selector as `h - h / 2^32 * 2^32`, which the closers read as
          -- linear arithmetic over the quotient (a remainder they do not)
          let a : RawExpr := .binop .div e' (.num selShift)
          return if m == "selector" then .binop .sub e' (.binop .mul a (.num selShift)) else a
    match extMember? C Γ (.field e m) with
    | some (r, g) =>
      let some sel := fnSelector? C g | throw s!"{g}: its signature has a type the ABI does not name"
      pure (.binop .add (.binop .mul (← fnPure Γ r) (.num selShift)) (.num sel))
    | none => do pure (.field (← fnPure Γ e) m)
  | .call f as => do pure (.call f (← as.mapM (fnPure Γ)))
  | .index a b => do pure (.index (← fnPure Γ a) (← fnPure Γ b))
  | .binop op a b => do pure (.binop op (← fnPure Γ a) (← fnPure Γ b))
  | .unop op a => do pure (.unop op (← fnPure Γ a))
  | .ternary c a b => do pure (.ternary (← fnPure Γ c) (← fnPure Γ a) (← fnPure Γ b))
  | .incDec op e => do pure (.incDec op (← fnPure Γ e))
  | .newArr T e => do pure (.newArr T (← fnPure Γ e))
  | .modular op a b k => do pure (.modular op (← fnPure Γ a) (← fnPure Γ b) (← fnPure Γ k))
  | .named f ns as => do pure (.named f ns (← as.mapM (fnPure Γ)))
  | .tuple as => do pure (.tuple (← as.mapM (fnPure Γ)))
  | .assign l r => do pure (.assign l (← fnPure Γ r))
  | .opAssign op l r => do pure (.opAssign op l (← fnPure Γ r))
  | e => pure e

/-- The bytes `bs` as a `bytesN`: left-aligned, the rest zero. -/
def bytesAlign (n : Nat) (bs : List Nat) : Except String Nat := do
  if n < bs.length then throw s!"a literal of {bs.length} bytes does not fit bytes{n}"
  pure ((bs ++ List.replicate (n - bs.length) 0).foldl (fun a b => 256 * a + b) 0)

/-- A `bytesM` as a `bytesN`, `M < N`: padded on the right. -/
def widenBytes (m n : Nat) (e : RawExpr) : RawExpr :=
  .binop .shl (.call (tyName .uint (8 * n)) [e]) (.num (8 * (n - m)))

/-- `e`, rewritten from `o`, where a `bytesN` is expected (solc's implicit
conversion): a literal of bytes left-aligned, a shorter `bytesM` padded on
the right; a longer one is refused, as solc refuses it. -/
def toBytesAt (Γ : ECtx) (n : Nat) (o e : RawExpr) : Except String RawExpr := do
  if let some bs := o.bytesLit? then return .num (← bytesAlign n bs)
  match bytesOf? C Γ o with
  | some m =>
    if m == n then pure e
    else if m < n then pure (widenBytes m n e)
    else throw s!"{o.toStr}: a bytes{m} where a bytes{n} is expected: write bytes{n}(…)"
  | none => pure e

/-- `toBytesAt` where the expected type is a `bytesN`, else `e`. -/
def toBytesAt? (Γ : ECtx) (n : Option Nat) (o e : RawExpr) : Except String RawExpr :=
  match n with
  | some n => toBytesAt C Γ n o e
  | none => pure e

/-- The byte `i` of the `bytesN` `b`, a `bytes1`: `b`'s byte counted from the
left, `b >> 8((N-1) -% i)` cut to 8 bits, divided by `i < N ? 1 : 0` so that
an index out of range reverts, as an array's does (`Storage.checkIndex`); a
literal index is checked here. -/
def bytesAt (n : Nat) (b i : RawExpr) : Except String RawExpr :=
  match i.litVal? with
  | some k =>
    -- a literal index: in range, or solc's compile error
    if 0 ≤ k && k < n then
      pure (.call "uint8" [.binop .mod (.binop .shr b (.num (8 * (n - 1 - k.toNat)))) (.num 256)])
    else throw s!"index {k} out of range of a bytes{n}"
  | none =>
    let sh : RawExpr := .binop .mulW (.num 8) (.binop .subW (.num (n - 1)) i)
    pure (.call "uint8" [.binop .div (.binop .mod (.binop .shr b sh) (.num 256))
      (.ternary (.binop .lt i (.num n)) (.num 1) (.num 0))])

/-- The mark of a `bytesN` argument of `abi.encode`/`encodePacked`/
`bytes.concat`, put by `bytesPure` (which rewrites the value to a `uint`)
and read by `hoist`. -/
def abiBytesMark (n : Nat) : String := s!"#abiBytes{n}"

/-- The width a mark names. -/
def abiBytesMark? (f : String) : Option Nat :=
  if f.startsWith "#abiBytes" then (f.drop 9).toNat? else none

/-- Solc's operations on `bytesN` that are not `uint8N`'s, as `uint`
operations (`docs/semantic-gaps.md`, "Bytes and strings"): a conversion, an
index, `.length`, a literal of bytes, an implicit widening; read bottom up,
the types from the expression as written. -/
partial def bytesPure (Γ : ECtx) : RawExpr → Except String RawExpr
  | .call "#array" as => pure (.call "#array" as)
  | .call f as => do
    -- A lazy branch is elaborated as a statement again. Validate the raw
    -- prefix witness before recursively rewriting its backing value, then
    -- rebuild the bytes marker that an ordinary bytes conversion would erase.
    if f.startsWith "#bytesPrefix" && (lookupBy f C.funs).isNone then
      let some n := (f.drop 12).toNat? | throw "a fixed byte prefix needs its width"
      unless 0 < n && n ≤ 32 do throw "a fixed byte prefix needs one through 32 bytes"
      let [witness] := as | throw "a fixed byte prefix takes one bytes argument"
      unless dynamicBytesExpr C Γ witness do
        throw "a fixed byte prefix takes bytes, not another reference type"
      let backing := match witness with
        | .call "bytes" [value] => value
        | value => value
      let backing ← bytesPure Γ backing
      return .call f [.call "bytes" [backing]]
    if f == "string.concat" && (lookupBy f C.funs).isNone then
      unless as.all (stringReason? C Γ) do throw "string.concat takes strings"
    if f == "bytes.concat" && (lookupBy f C.funs).isNone then
      let bytesArg (a : RawExpr) : Bool :=
        if a.bytesLit?.isSome || (bytesOf? C Γ a).isSome then true else
        match a with
        | .call "bytes" [_] => true
        | _ => let ws := exprShape C Γ a
               ws.contains ("[]#bytes", 1) && !ws.contains ("#string", 1)
      unless as.all bytesArg do throw "bytes.concat takes bytes or fixed bytes"
    if f == "erc7201" && (lookupBy f C.funs).isNone then
      let [a] := as | throw "erc7201 takes one string argument"
      unless stringReason? C Γ a do throw "erc7201 takes a string; convert bytes with string(data)"
    let as' ← as.mapM (bytesPure Γ)
    if let some n := bytesTy? f then
      let ([o], [a]) := (as, as') | throw s!"a conversion {f}(…) takes one argument"
      if let some bs := o.bytesLit? then return .num (← bytesAlign n bs)
      -- A dynamic bytes-to-fixed-bytes conversion takes the first N bytes,
      -- right padded with zero, rather than converting a memory reference
      -- numerically. A hidden bounded lowering captures the receiver once.
      if dynamicBytesExpr C Γ o then
        -- Keep the bytes kind explicit when `bytesPure` erased a valid
        -- `bytes(text)` conversion from a string-backed memory reference.
        return .call ("#bytesPrefix" ++ toString n) [.call "bytes" [a]]
      return match bytesOf? C Γ o with
        | some m =>
          if m == n then a
          else if m < n then widenBytes m n a
          else .call (tyName .uint (8 * n)) [.binop .shr a (.num (8 * (m - n)))]
        | none => .call (tyName .uint (8 * n)) [a]
    if dynBytesTy f then
      let [a] := as' | throw s!"a conversion {f}(…) takes one argument"
      return a
    -- an argument of the ABI's that is a `bytesN`: marked, its width lost to
    -- the rewrite (`abiBytesMark`)
    if encodeBuiltin f && (lookupBy f C.funs).isNone then
      let mark (o a : RawExpr) : RawExpr := match bytesOf? C Γ o with
        | some n => .call (abiBytesMark n) [a]
        | none => a
      return .call f ((as.zip as').map fun (o, a) =>
        match o, a with
        | .tuple os, .tuple vs => .tuple ((os.zip vs).map fun (o, a) => mark o a)
        | _, _ => mark o a)
    match lookupBy f C.funs with
    | some d =>
      if d.params.length != as.length then return .call f as'
      let as'' ← ((d.params.zip as).zip as').mapM fun (((n, _), o), a) =>
        toBytesAt? C Γ (lookupBy (n ++ "#bytes") d.widths) o a
      pure (.call f as'')
    | none => pure (.call f as')
  | .index b i => do
    let b' ← bytesPure Γ b
    let i' ← bytesPure Γ i
    if let some n := bytesOf? C Γ b then
      if i.hasIncDec then throw s!"{(RawExpr.index b i).toStr}: an index of a bytes{n} with an effect"
      return ← bytesAt n b' i'
    -- a mapping's `bytesN` key; a byte string key hashed (`hashKeyRows`)
    let (key, hashed) := match widthPath? C Γ b with
      | some (tb, k, .ref (.mapping ..)) =>
        (lookupBy (k ++ "{}#bytes") tb, (lookupBy (k ++ "{}#hash") tb).isSome)
      | _ => (none, false)
    if hashed then return .index b' (.call "keccak256" [i'])
    pure (.index b' (← toBytesAt? C Γ key i i'))
  | .field b "length" => do
    if let some n := bytesOf? C Γ b then
      if b.hasIncDec then throw s!"{b.toStr}.length: a bytes{n} with an effect"
      return .num n
    pure (.field (← bytesPure Γ b) "length")
  | .field b f => do pure (.field (← bytesPure Γ b) f)
  | .binop op a b => do
    let a' ← bytesPure Γ a
    let b' ← bytesPure Γ b
    if op matches .lt | .gt | .le | .ge | .eqB | .neB | .band | .bor | .bxor then
      let n := joinBytes (bytesOf? C Γ a) (bytesOf? C Γ b)
      return .binop op (← toBytesAt? C Γ n a a') (← toBytesAt? C Γ n b b')
    pure (.binop op a' b')
  | .unop op a => do
    let lowered ← bytesPure Γ a
    if op == .bnot then
      if let some n := bytesOf? C Γ a then
        -- Keep the ORIGINAL nominal byte width before a literal cast folds.
        -- Complement is mask minus the compact, bounded bytesN value.
        return .binop .subW (.num (2 ^ (8 * n) - 1)) lowered
    pure (.unop op lowered)
  | .ternary c a b => do
    let n := joinBytes (bytesOf? C Γ a) (bytesOf? C Γ b)
    pure (.ternary (← bytesPure Γ c) (← toBytesAt? C Γ n a (← bytesPure Γ a))
      (← toBytesAt? C Γ n b (← bytesPure Γ b)))
  | .incDec op e => do pure (.incDec op (← bytesPure Γ e))
  | .newArr T e => do pure (.newArr T (← bytesPure Γ e))
  | .modular op a b k => do
    pure (.modular op (← bytesPure Γ a) (← bytesPure Γ b) (← bytesPure Γ k))
  | .named f ns as => do pure (.named f ns (← as.mapM (bytesPure Γ)))
  | .tuple as => do pure (.tuple (← as.mapM (bytesPure Γ)))
  | .assign l r => do
    pure (.assign (← bytesPure Γ l) (← toBytesAt? C Γ (bytesOf? C Γ l) r (← bytesPure Γ r)))
  | .opAssign op l r => do
    pure (.opAssign op (← bytesPure Γ l) (← toBytesAt? C Γ (bytesOf? C Γ l) r (← bytesPure Γ r)))
  | e => pure e

/-- `bytesPure` of a statement's expressions, and a value written where a
`bytesN` is expected converted to it: a declaration's initializer, an
assignment's right-hand side, a pushed element. -/
def bytesStmt (Γ : ECtx) (s : RawStmt) : Except String RawStmt := do
  let s' ← s.mapExprsM (bytesPure C Γ)
  match s, s' with
  | .decl (.named T) _ (some o), .decl T' x (some r) =>
    pure (.decl T' x (some (← toBytesAt? C Γ (bytesTy? T) o r)))
  | .assign l o, .assign l' r => pure (.assign l' (← toBytesAt? C Γ (bytesOf? C Γ l) o r))
  | .opAssign op l o, .opAssign _ l' r =>
    pure (.opAssign op l' (← toBytesAt? C Γ (bytesOf? C Γ l) o r))
  | .call (.field b "push") [o], .call f [r] =>
    pure (.call f [← toBytesAt? C Γ (bytesOf? C Γ (.index b (.num 0))) o r])
  | _, s' => pure s'

/-- `e`, an operation that can leave its narrow type — `+ - * **`, and `/` and
unary `-` at `int` (`-128 / -1` at `int8`) — with that type. -/
def checkedNarrow? (Γ : ECtx) (e : RawExpr) : Option (PrimTy × Nat) :=
  match e, intTyOf C Γ e with
  | .binop op _ _, some (p, n) =>
    if n < 256 && ((op matches .add | .sub | .mul | .pow) || (op == .div && p == .int))
    then some (p, n) else none
  | .unop .neg _, some (.int, n) => if n < 256 then some (.int, n) else none
  | _, _ => none

/-- Whether a narrow operation (`checkedNarrow?`) occurs in `e`. -/
def hasNarrow (Γ : ECtx) (e : RawExpr) : Bool :=
  e.any fun n => (checkedNarrow? C Γ n).isSome

/-- `r` may be written where a `p` of `n` bits is expected: a literal fits it,
and a value is not wider (solc converts only to a wider type implicitly). -/
def fitCheck (Γ : ECtx) (p : PrimTy) (n : Nat) (r : RawExpr) : Except String Unit := do
  if 256 ≤ n then return
  match r.litVal?, intTyOf C Γ r with
  | some v, _ =>
    let (lo, hi) := intRange p n
    unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
  | none, some (q, m) =>
    if q != .bool && n < m then
      throw s!"a {tyName q m} where a {tyName p n} is expected: write {tyName p n}(…)"
  | none, none => pure ()

/-- One node at a narrow `uintN`, read as solc reads it: the wrapping
`+% -% *% **%` of `unchecked` and `<<` are taken modulo `2^N` (solc truncates
them to the type), `~a` is `(2^N - 1) -% a`; and a literal operand must fit the
type. -/
def narrowWrapNode (unc : Bool) (Γ : ECtx) (e : RawExpr) : Except String RawExpr := do
  let some (p, n) := intTyOf C Γ e | return e
  -- signed inside `unchecked` (`unc`): `-a` is `0 -% a` on the words; `a / b`
  -- at `intN` is the quotient at `int`, read back at `intN` (`-128 / -1` at
  -- `int8` is `-128`), and at `int` the quotient by `1` where `b` is `-1`,
  -- negated on the words (`type(int).min / -1` is `type(int).min`).  None
  -- of these is narrowed again (`narrowPure` does not revisit its output)
  if unc && p == .int then
    let neg (a : RawExpr) : RawExpr := .call (tyName .int n) [.binop .subW (.num 0) (.call "uint" [a])]
    match e with
    | .unop .neg a => if a.isLit then return e else return neg a
    | .binop .div a b =>
      match b.litVal? with
      | some (-1) => return neg a
      | some _ => return e
      | none =>
        if a.hasIncDec || b.hasIncDec then
          throw s!"{e.toStr} inside `unchecked`: a signed quotient of an operand with an effect"
        if n < 256 then
          return .call (tyName .int n) [.binop .div (.call "int" [a]) (.call "int" [b])]
        let m1 : RawExpr := .unop .neg (.num 1)
        let isM1 : RawExpr := .binop .eqB b m1
        let q : RawExpr := .binop .div a (.ternary isM1 (.unop .neg b) b)
        return .call "int" [.binop .mulW (.call "uint" [q])
          (.ternary isM1 (.num (2 ^ 256 - 1)) (.num 1))]
    | _ => pure ()
  -- signed: the operation on the operands' words, the result read back at
  -- `intN` (`int8(uint(x) +% 1)`, `castCapture`), as solc wraps it; `a **% k`
  -- too, its exponent a `uint` (the words' power is the signed one's, modulo `2^256`)
  if let .binop op a b := e then
    if p == .int && op == .powW then
      if let some v := a.litVal? then
        let (lo, hi) := intRange p n
        unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
      let wa : RawExpr := match a.litVal? with
        | some v => .num (v % ((2 ^ 256 : Nat) : Int)).toNat
        | none => .call "uint" [a]
      return .call (tyName .int n) [.binop .powW wa b]
    if p == .int && (op matches .addW | .subW | .mulW) then
      for l in [a, b] do
        if let some v := l.litVal? then
          let (lo, hi) := intRange p n
          unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
      let word (l : RawExpr) : RawExpr := match l.litVal? with
        | some v => .num (v % ((2 ^ 256 : Nat) : Int)).toNat
        | none => .call "uint" [l]
      -- a negative literal added is subtracted: `x + -1` is `uint(x) -% 1`
      let w := match op, b.litVal? with
        | .addW, some v => if v < 0 then .binop .subW (word a) (.num v.natAbs) else .binop op (word a) (word b)
        | .subW, some v => if v < 0 then .binop .addW (word a) (.num v.natAbs) else .binop op (word a) (word b)
        | _, _ => .binop op (word a) (word b)
      return .call (tyName .int n) [w]
  if p == .int && n < 256 then
    if let .binop .shl a b := e then
      let word : RawExpr := match a.litVal? with
        | some v => .num (v % ((2 ^ 256 : Nat) : Int)).toNat
        | none => .call "uint" [a]
      return .call (tyName .int n) [.binop .shl word b]
  if 256 ≤ n then return e
  match e with
  | .binop op a b =>
    -- `%` too: the modulus this rewrite writes may meet it again
    unless op matches .pow | .powW | .shl | .shr | .mod do
      for l in [a, b] do
        if let some v := l.litVal? then
          let (lo, hi) := intRange p n
          unless lo ≤ v && v ≤ hi do throw s!"{v} does not fit {tyName p n}"
    if op matches .addW | .subW | .mulW | .powW | .shl then
      return .binop .mod e (.num (2 ^ n))
    return e
  | .unop .bnot a => return .binop .subW (.num (2 ^ n - 1)) a
  | _ => return e

/-- `narrowWrapNode` at every node of `e`, bottom up. -/
partial def narrowPure (unc : Bool) (Γ : ECtx) : RawExpr → Except String RawExpr
  | .binop op a b => do narrowWrapNode C unc Γ (.binop op (← narrowPure unc Γ a) (← narrowPure unc Γ b))
  | .unop op a => do narrowWrapNode C unc Γ (.unop op (← narrowPure unc Γ a))
  | .field e f => do pure (.field (← narrowPure unc Γ e) f)
  | .index e k => do
    -- a narrow mapping key: the index converts to it implicitly, so it fits
    -- (`m[300]` at `mapping(uint8 => …)` is solc's compile error)
    if let some (tb, key, .ref (.mapping kp _)) := widthPath? C Γ e then
      if let some n := lookupBy (key ++ "{}") tb then fitCheck C Γ kp n k
    pure (.index (← narrowPure unc Γ e) (← narrowPure unc Γ k))
  | .ternary c a b => do pure (.ternary (← narrowPure unc Γ c) (← narrowPure unc Γ a) (← narrowPure unc Γ b))
  | .incDec op e => do pure (.incDec op (← narrowPure unc Γ e))
  | .newArr T e => do pure (.newArr T (← narrowPure unc Γ e))
  | .call f as => do pure (.call f (← as.mapM (narrowPure unc Γ)))
  | .modular op a b k => do
    pure (.modular op (← narrowPure unc Γ a) (← narrowPure unc Γ b) (← narrowPure unc Γ k))
  | .named f ns as => do pure (.named f ns (← as.mapM (narrowPure unc Γ)))
  | e => pure e

/-- `require(inTy)` of `e` at `p`'s `n` bits, when `n` is narrow. -/
def narrowCheck (p : PrimTy) (n : Nat) (e : RawExpr) : ElabM (SProg C) := do
  if 256 ≤ n then return []
  let Γ ← nctx
  let c ← checkIn C Γ .bool (inTyCond p n e)
  let sc ← read
  let sf := sc.selfFrame || sc.retainFailureData
  pure [.of Γ (match (← read).overflow with
    | some o => o.guardStmt c sf
    -- in a self-call's callee, solc's `Panic(0x11)` data (`Prog.withPanics`)
    | none => if sf then panicStmt 0x11 c else .require c)]

/-- The slot `b.push()` appended: `b[b.length - 1]`. -/
def pushedSlot (b : RawExpr) : RawExpr :=
  .index b (.binop .sub (.field b "length") (.num 1))

/-- What follows a write of `r` to the variable `l`: the check of `r`'s narrow
operation, on `l` (`c = a + b;` at `uint8` is `c = a + b; require(c <= 255);`:
a revert discards the write, so checking after it is checking before it); and,
when `l` is narrow, `r` fitting it (`fitCheck`) and arithmetic on literals
alone checked at `l`'s type (solc folds it at compile time). -/
def narrowPost (l r : RawExpr) : ElabM (SProg C) := do
  let Γ ← ctx
  let tl := intTyOf C Γ l
  if let some (p, n) := tl then ElabM.lift (fitCheck C Γ p n r)
  match checkedNarrow? C Γ r, tl, intTyOf C Γ r, r.litVal? with
  | some (p, n), _, _, _ => narrowCheck C p n l
  | none, some (p, n), none, none => narrowCheck C p n l
  | _, _, _, _ => pure []

/-- A narrow operation inside an expression, its operands' captures made:
held in a fresh local and checked there, before the statement
(`x = a + b > c;` at `uint8` is `uint se1 = a + b; require(se1 <= 255);
x = se1 > c;`). -/
def narrowCapture (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let some (p, n) := checkedNarrow? C (← ctx) e | return ([], e)
  let Γ ← nctx
  let v ← checkIn C Γ p e
  let x ← captureAs C "se" (.val p n)
  let e' : RawExpr := .name (toString x)
  pure (.of Γ (.declLocal p x (some v)) :: (← narrowCheck C p n e'), e')

/-- The low `n` bits of the word `w`: `w % 2^n`, as solc truncates. -/
def lowBits (n : Nat) (w : RawExpr) : RawExpr :=
  if 256 ≤ n then w else .binop .mod w (.num (2 ^ n))

/-- The word `w`'s low `n` bits read as an `intN`, in two's complement: the
bits moved by `2^(n-1)`, cut to `n`, moved back and read as an `int`
(`int((w +% 128) % 256 -% 128)` at `int8`: `200` is `-56`). -/
def signedAt (n : Nat) (w : RawExpr) : RawExpr :=
  if 256 ≤ n then .unop .toInt w
  else
    let h : RawExpr := .num (2 ^ (n - 1))
    .unop .toInt (.binop .subW (.binop .mod (.binop .addW w h) (.num (2 ^ n))) h)

/-- A cast `T(e)`, `e`'s captures made: a fresh local of type `T` holding `e`.
A cast keeps the low bits of `e`'s word (`uint(i)` is `i`'s two's
complement, `UnOp.toUint`): a `uintN` takes them as they are (`e % 2^N`), an
`intN` reads them signed (`signedAt`); widening within a sign is the
identity.  A literal must fit `T`. -/
def castCapture (f : String) (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let some (p, n) := castTy? f | throw s!"{f} is not a type"
  let Γ ← ctx
  let word (q : PrimTy) (e : RawExpr) : RawExpr := if q == .int then .unop .toUint e else e
  let r ← match intTyOf C Γ e, e.litVal? with
    | _, some _ => do ElabM.lift (fitCheck C Γ p n e); pure e
    | some (q, m), none =>
      if q == p && m ≤ n then pure e
      else if p == .int then pure (signedAt n (word q e))
      else pure (lowBits n (word q e))
    | none, none =>
      if 256 ≤ n then pure e
      else if p == .int then
        throw s!"{f}({e.toStr}): a cast of arithmetic on literals alone to a narrow int; write the literal"
      else pure (.binop .mod e (.num (2 ^ n)))
  let Γn ← nctx
  let v ← checkIn C Γn p r
  let x ← captureAs C "se" (.val p n)
  pure ([.of Γn (.declLocal p x (some v))], .name (toString x))

/-- Retain the source address kind in the frontend's shape table while the
intrinsic statement carries its cleaned uint value. -/
def addressCapture (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let context := (← get).1
  if (markOf? C context "#address" e).isSome then return ([], e)
  let Γ ← nctx
  let value ← ElabM.lift (check C Γ .uint (.call "address" [e]))
  -- Contextual kind inference has already read the wrapper before hoisting.
  -- A checked literal needs no extra local or reduction tree.
  if e.litVal?.isSome then return ([], e)
  let x ← captureAs C "se" (.val .uint 256)
  declareShape (toString x) addressRows
  pure ([.of Γ (.declLocal .uint x (some value))], .name (toString x))

/-- A conversion `E(e)` to an enum of `n` members, `e`'s captures made: a
fresh `uint` holding `e`, then a membership check: an ordinary assertion,
or literal `Panic(0x21)` data in a self-call frame. -/
def enumCapture (n : Nat) (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  let Γ ← nctx
  let v ← checkIn C Γ .uint e
  let x ← captureAs C "se" (.val .uint)
  let e' : RawExpr := .name (toString x)
  let Γ' ← nctx
  let c ← checkIn C Γ' .bool (.binop .lt e' (.num n))
  let sc ← read
  let check := if sc.selfFrame || sc.retainFailureData then panicStmt 0x21 c else .assert c
  pure ([.of Γ (.declLocal .uint x (some v)), .of Γ' check], e')

/-- `e`'s value, or the reference it names, held in a fresh local before a
later operand's effect: under the default legacy schedule, `x = i++ + i;`
reads the right `i` first, so it is
`uint se1 = i; uint se2; se2 = i++; x = se2 + se1;`.  A literal needs no
capture, nor does a name bound to a reference (an effect cannot rebind it).
Nor does a capture already made, which holds its value: a fresh name the
elaborator declared as one, or a line's written-out capture.  A fresh name
the inliner gave a callee's local (`ElabScope.inlined`) is a local like any
other, and is captured: in `function f(uint a) … { return a++ + a; }` the
right `a` is read before the `++`. -/
def captureExpr (e : RawExpr) : ElabM (SProg C × RawExpr) := do
  if e.isLit || e matches .bool _ then return ([], e)
  if let .name x := e then
    if let .fresh _ i := Var.ofName x then
      let sc ← read
      unless (C.rootType x).isSome || sc.mutableFreshNames.contains x ||
          sc.inlined.any (fun (k₀, k₁) => k₀ ≤ i && i < k₁) do return ([], e)
  let ⟨Γ, t⟩ ← synthM C e
  match e, t with
  | .name _, .path (.ref _) _ | .name _, .mpath (.ref _) _ => return ([], e)
  | _, .path (.ref R) sp =>
    let x ← captureRef C "sp" (.alias R) e
    return ([.of Γ (.declStorage R x (some (.path sp)))], .name (toString x))
  | _, .mpath (.ref R) mp =>
    let x ← captureRef C "mv" (.mem R) e
    return ([.of Γ (.declMem R x (some (.alias mp)) rfl mp.mapFree)], .name (toString x))
  | _, t =>
    let some ⟨p, v⟩ := t.toVal? | throw s!"{e.toStr}: a value or a reference is expected"
    let ec ← ctx
    -- A scalar capture must retain source-kind markers, not only its bit
    -- width: bytes widening pads on the right, addresses pack at 20 bytes,
    -- and function/enum observations must keep their original kind.
    let mut ws := match widthPath? C ec e with
      | some (tb, key, .prim _) => shapeUnder tb key
      | _ => match e with
        | .name name => localShape ec name
        | _ => exprShape C ec e
    if let some ty := (rawFnTyOfExpr? C ec e).orElse (fun _ => fnTyOfExpr C ec e) then
      ws := ("#" ++ ty, 0) :: ws
    if let some n := bytesOf? C ec e then ws := ("#bytes", n) :: ws
    for marker in ["#address", "#enum"] do
      if let some n := markOf? C ec marker e then ws := (marker, n) :: ws
    let x ← captureAs C "se" (.val p (widthIn C ec e))
    declareShape (toString x) ws
    return ([.of Γ (.declLocal p x (some v))], .name (toString x))

/-- A discarded argument needs no runtime read only when its raw syntax
has no operation or effect and its typed primitive value cannot halt.
In particular `p.x`, `a.length` and named references are not assumed total. -/
def canDiscardArg (e : RawExpr) : ElabM Bool := do
  unless e.isPure do return false
  -- This query also runs before function/byte members are normalized.
  -- A failed synthesis is not an admission error: the ordinary passes may
  -- still lower `this.f.selector`, for example. It simply cannot be omitted.
  match synth C (← nctx) e with
  | .error _ => pure false
  | .ok t =>
    let some ⟨_, v⟩ := t.toVal? | return false
    pure (!v.mayHalt)

/-- Evaluate a residual operand now, including a named reference. The usual
`captureExpr` may leave reference names alone because effects cannot rebind
them; a discarded/error argument must still detect an unset reference. -/
def forceArg (e : RawExpr) (expected : Option PrimTy := none) : ElabM (SProg C × RawExpr) := do
  if e.isLit || e.bytesLit?.isSome || e matches .bool _ then return ([], e)
  let ⟨Γ, t⟩ ← synthM C e
  match t with
  | .path (.ref R) sp =>
    let x ← captureRef C "sp" (.alias R) e
    pure ([.of Γ (.declStorage R x (some (.path sp)))], .name (toString x))
  | .mpath (.ref R) mp =>
    let x ← captureRef C "mv" (.mem R) e
    pure ([.of Γ (.declMem R x (some (.alias mp)) rfl mp.mapFree)], .name (toString x))
  | _ =>
    match expected with
    | none => captureExpr C e
    | some p =>
      -- Literal operations not folded by constRat? still take their
      -- contextual type from the error's parameter (e.g. int(2 ** 3)).
      let v ← checkIn C Γ p e
      let x ← captureAs C "se" (.val p (widthIn C (← ctx) e))
      pure ([.of Γ (.declLocal p x (some v))], .name (toString x))

/-- Finish each argument before starting the next one's hoisting. This
preserves both failure priority and values read before a later effect.
With `discard`, total primitive reads can be omitted because their values
will never be encoded or passed to a callee. -/
def eagerArgsWith (hoist : RawExpr → ElabM (SProg C × RawExpr))
    (args : List RawExpr) (discard : Bool := false)
    (expected : List (Option PrimTy) := []) : ElabM (SProg C × List RawExpr) := do
  let mut P : SProg C := []
  let mut values : List RawExpr := []
  for (a, i) in args.zipIdx do
    let (Q, a) ← hoist a
    let (Q', a) ← if discard && (← canDiscardArg C a) then pure ([], a)
      else forceArg C a ((expected[i]?).getD none)
    P := P ++ Q ++ Q'
    values := values ++ [a]
  pure (P, values)

/-- Hold an earlier read before a later effect or explicit overflow guard.
Even a guard without a state change may panic or assume the run away, so an
earlier failing read must happen first. -/
def captureBefore (e : RawExpr) (later : List RawExpr) : ElabM (SProg C × RawExpr) := do
  let checks := (← read).overflow.isSome && later.any (hasNarrow C (← ctx))
  if later.any (·.hasIncDec) || checks then captureExpr C e else pure ([], e)

/-- A checked unsigned power whose failure bytes are observable. This only
requests the existing guarded lowering; conditional arms stay conditional. -/
def powerDataNeeded (sc : ElabScope) (Γ : ECtx) (e : RawExpr) : Bool :=
  (sc.selfFrame || sc.retainFailureData) && !sc.unchecked && sc.overflow.isNone &&
    e.any (fun | .binop .pow a _ => (intTyOf C Γ a).all (fun (p, _) => p == .uint) | _ => false)

end Elab

end Solidity
