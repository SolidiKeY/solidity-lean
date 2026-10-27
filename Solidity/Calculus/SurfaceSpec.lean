import Solidity.Calculus.Close
import Solidity.Calculus.FilteredMembership
import Solidity.Calculus.NotationResolve
import Solidity.Calculus.RefInputs
import Solidity.Syntax.Elab

/-!
# Specifications, compiled to dynamic logic

solkey's `SpecCompiler` and `SolidityProblemSynthesizer`, ported.  A clause
(`SpecExpr`, `SpecSyntax.lean`) is compiled against a context that names the
storage term its state variables are read from: `storage` in a `requires`,
an `ensures` and an `invariant`, the storage variable `old` inside `\old(…)`.
A state variable `count` is `find(storage, count)`, and `\old(count)` is
`find(old, count)`; `\forall T x; e` stays a quantifier (`Fml.all`).

The obligation of a function `f(x₁, …, xₙ)` is solkey's, a box:

```
R ∧ L ∧ M ∧ I ∧ requires →
  {old := storage ‖ oldNet := net ‖ B} [ T result; result = f(x₁, …, xₙ); ] (I ∧ ensures ∧ A)
```

The call is solkey's synthesized `result = f(x₁, …, xₙ)@C;`, a
`FunctionBodyStatement` with its target: it returns to `result`
(`CallRet.rets`; a void function's `f(x̄)@C;` to no target, `CallRet.rets []`),
so `functionBodyExpand` inlines it, where a call in a body is
`internalCallExpand`'s.  Lean only: `T result;` is a statement of the box,
where solkey declares `result` among the problem's program variables; and a
function with an unnamed return has an obligation (`result`, or
`result__ret0`, … of several), where solkey refuses one
(`SolidityOutline.unsupportedReason`).  A function of several returns returns to
`result_lo`, `result_hi`, … (`SpecCompiler.resultVariable`), and an `ensures`
names a return by its name: `lo` is `result_lo` (`result` for the one return
of a function of one), after the locals and before the state variables, as
`SpecCompiler.visitIdent` resolves it.  `\result` needs a function of one
return.

where `B` books `msg.value`, KeY's
`net := store(net, at(msg.sender), net(msg.sender) + msg.value) ‖ selfBalance := selfBalance + msg.value`.

The parameters are free locals, so `⊨ᶠ` ranges over every argument; `R`
gives each its type's range, since a free local also ranges over values of
other types and over none (solkey's parameters are KeY `int`s, unbounded,
and need no such fact).  `L` is the contract's layout (`layoutFmls`): `⊨ᶠ`
also ranges over storages the contract never has.  `M` is what `msg.value`
is: `>= 0`, or `== 0` for a function that is not `payable`.  `I` is the
contract's invariants, assumed and owed (solkey's `CInv(storage, net)`).
`A` is the frame of an `assignable` clause (`assignableFml`).

The update takes solkey's snapshots only where something reads them: `old`
when an `ensures` reads `\old` or an `assignable` clause is given, `oldNet`
when an `\old(…)` reads `net(a)`.  The booking of `msg.value`, the sender's
ledger entry and the contract's funds credited, is there for a `payable`
function only: `M` makes the other's a booking of `0`.

**A constructor's obligation** (`spec!{constructor}`) is solkey's
deployment, from the empty storage:

```
R ∧ M ∧ requires →
  {storage := mtSt ‖ old := mtSt ‖ oldNet := mtSt ‖
   net := store(mtSt, at(msg.sender), msg.value) ‖ selfBalance := msg.value}
  [ constructor(x₁, …, xₙ); ] (I ∧ ensures ∧ A)
```

It assumes no `I` (solkey's has no `CInv(storage, net)` premise) and no
`L`: both would be of the storage the update discards.  The snapshots are
taken where something reads them, as a function's are; `\old(net(a))` reads
the empty ledger, `0`.  Lean only: a `requires` that reads a state
variable, the ledger or the funds is refused, since solkey reads it before
the update, of a storage the deployment never sees.

The benchmarks' clauses over `net(a)` still leave proof gaps. A spec's
arithmetic over Solidity values is Solidity's, checked at its operands'
type, where solkey's is KeY's unbounded `int`: an overflowing side makes its
equation false rather than true of a larger number.  Every equation compiled
here is KeY's `=`, `Fml.eq`, read in the Theory: a storage read is total
there, a word of its type (an equation of two sides that both overflow
holds, and `!=` of them does not); `==` of two conditions is `<->`.  `net(a)` is a ledger entry, a KeY `int`
(`Srt.kint`, solkey's `netHeader.key`), unbounded; beside one a `uint`
(`msg.value`, solkey's `msgValue`, also a KeY `int`) is widened
(`Op1.toInt`, total, printed bare where the other side shows the sort), and
`\old(net(a)) + msg.value` is KeY's unbounded arithmetic (`Op2.zbin`), its
equation the comparison `==` on KeY `int`s (`NRead.eqK`).
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- Where a clause is read: the storage its state variables are read from,
whether `\old` and `\result` mean something (an `ensures`), the locals in
scope (the parameters and the quantified variables), and `\result`'s type. -/
structure SpecCtx (C : Contract) where
  storage : NSTerm C
  ensures : Bool
  locals : List (String × PrimTy)
  /-- Reference parameters retain their storage or memory location. -/
  refs : List (String × LocalTy) := []
  /-- `\old` does not currently snapshot the heap. -/
  memory : Option (NMTerm C) := some .memory
  result : Option PrimTy
  /-- The ledger `net(a)` reads: the current one, or the snapshot bound at
  the variable (`oldNet` under `\old`). -/
  ledger : Option Var := none
  /-- The function's returns an `ensures` names: each name, the local the
  obligation returns it to, and its type. -/
  rets : List (String × String × PrimTy) := []

/-- The storage variable `\old` reads, solkey's `old`. -/
def oldVar : Var := .ofName "old"

/-- The ledger variable `\old(net(a))` reads, solkey's `oldNet`. -/
def oldNetVar : Var := .ofName "oldNet"

/-- The local `\result` names, solkey's `result`. -/
def resultVar : Var := .ofName "result"

/-- The obligation owns its hidden snapshot and return names. Primitive
logical binders cannot reuse them, including inside another quantifier. -/
def reservedSpecName (x : String) : Bool :=
  x == "old" || x == "oldNet" || x == "result" || x.startsWith "result_"

/-- `\old(e)` is read against `old` and `oldNet`, and not nested. -/
def SpecCtx.old (ctx : SpecCtx C) : SpecCtx C :=
  { ctx with storage := .pv oldVar, ensures := false, ledger := some oldNetVar, memory := none }

/-- The fold every query over a clause is: `here e` where it answers for the
node `e` itself, else `join` over its operands, `leaf` at a leaf. -/
def SpecExpr.foldMap {α : Type} (leaf : α) (join : α → α → α) (here : SpecExpr → Option α) :
    SpecExpr → α
  | e@(.old a) | e@(.net a) | e@(.field a _) | e@(.unop _ a) | e@(.all _ _ a) | e@(.ex _ _ a) =>
    match here e with
    | some r => r
    | none => a.foldMap leaf join here
  | e@(.index a b) | e@(.binop _ a b) | e@(.imp a b) | e@(.iff a b) =>
    match here e with
    | some r => r
    | none => join (a.foldMap leaf join here) (b.foldMap leaf join here)
  | e@(.member _ key items) =>
    match here e with
    | some r => r
    | none => items.foldl (fun acc item => join acc (item.foldMap leaf join here))
        (key.foldMap leaf join here)
  | e@(.memberFilter _ key _ items guard) =>
    match here e with
    | some r => r
    | none => join (items.foldl (fun acc item => join acc (item.foldMap leaf join here))
        (key.foldMap leaf join here)) (guard.foldMap leaf join here)
  | e@(.num _) | e@(.uintLit _) | e@(.bool _) | e@(.name _) | e@.result => (here e).getD leaf

/-- Whether a node `here` picks out occurs, and what it says of it. -/
def SpecExpr.any (here : SpecExpr → Option Bool) : SpecExpr → Bool :=
  SpecExpr.foldMap false (· || ·) here

/-- Whether `net(a)` occurs. -/
def SpecExpr.usesNet : SpecExpr → Bool :=
  SpecExpr.any fun | .net _ => some true | _ => none

/-- Whether an `\old(… net(a) …)` occurs: what reads `oldNet`. -/
def SpecExpr.usesOldNet : SpecExpr → Bool :=
  SpecExpr.any fun | .old e => some e.usesNet | _ => none

/-- Whether an `\old` occurs. -/
def SpecExpr.usesOld : SpecExpr → Bool :=
  SpecExpr.any fun | .old _ => some true | _ => none

/-- A number literal: it takes the type of the other operand. -/
def SpecExpr.isNum : SpecExpr → Bool
  | .num _ => true
  | _ => false

/-- A ledger-integer result shape, used to select an operand context before
compilation. Comparisons and reads through a ledger-valued index do not have
this result shape. The compiler still checks every operand and address. -/
private def SpecExpr.hasLedgerInt : SpecExpr → Bool
  | .net _ => true
  | .old a | .unop .neg a => a.hasLedgerInt
  | .binop op a b => op.zArith && (a.hasLedgerInt || b.hasLedgerInt)
  | _ => false

/-- `t` is a value of its type: `0 <= t <= 2^256 - 1` for a `uint`; every
`bool` is one. -/
def rangeFml (t : NTerm C) : PrimTy → NRead C
  | .uint => .and (NRead.cmp .le (.num 0) t) (NRead.cmp .le t (.num (uintBound - 1)))
  | .int => .and (NRead.cmp .le (.num (-intBound)) t) (NRead.cmp .le t (.num (intBound - 1)))
  | .bool => .tt

/-- **The layout, as premises**: every word the declared state holds is a
value of its type, `0 <= count <= 2^256 - 1`, and so at every key of a
mapping, `∀ uint k1; 0 <= balances[k1] ∧ …` (not inside an array).  Every
storage the contract reaches has them; `⊨ᶠ` ranges over every storage, where
`balances` may be no mapping (`balances[a] == \old(balances[a])` is then
false: a side is undefined) or hold a `bool` (which `delete` resets to
`false`, not `0`).  solkey's reads are total and typed, and need none. -/
partial def layoutAt (T : Ty) (p : NPTerm C) (keys : List (Var × PrimTy)) (k : Nat) : List (NRead C) :=
  match T with
  | .prim q =>
    [keys.foldl (fun φ (x, q) => .all x q φ) (rangeFml (.find .storage p) q)]
  | .ref (.mapping K V) =>
    let x : Var := .ofName s!"k{k}"
    layoutAt V (.at p (.pv x)) ((x, K) :: keys) (k + 1)
  | .ref (.struct s) => (structDef s).flatMap fun (f, T') => layoutAt T' (.field p f) keys k
  | _ => []

/-- The names a clause reads. -/
def SpecExpr.names : SpecExpr → List String
  | .name x => [x]
  | .memberFilter _ key x items guard =>
    key.names ++ items.flatMap SpecExpr.names ++ (guard.names.filter (· != x))
  | .member _ key items => key.names ++ items.flatMap SpecExpr.names
  | .old e | .net e | .field e _ | .unop _ e | .all _ _ e | .ex _ _ e => e.names
  | .index a b | .binop _ a b | .imp a b | .iff a b => a.names ++ b.names
  | .num _ | .uintLit _ | .bool _ | .result => []

/-- A filtered domain is literal-only and intrinsically typed before lowering.
Dynamic values, arithmetic expressions and ledger integers are not domains. -/
def SpecExpr.domainLiteral (p : PrimTy) : SpecExpr → Except String p.Denote
  | .num n => numLit (toString n) n p
  | .uintLit n => do
    unless p = .uint do throw "a fixed uint literal in a non-uint filtered domain"
    numLit s!"uint({n})" n p
  | .unop .neg (.num n) => numLit s!"-{n}" (-(Int.ofNat n)) p
  | .bool b => match p with
    | .bool => pure b
    | _ => throw "a boolean literal in a non-bool filtered domain"
  | _ => throw "a filtered membership domain requires primitive literals"

/-- The layout premises of the state variables among `rs`: those the
clauses read.  What only the body reads needs none: a read the program
makes is guarded by the program, which reverts where it is undefined. -/
def layoutFmls (C : Contract) (rs : List String) : List (NRead C) :=
  (C.vars.filter fun (r, _) => rs.contains r).flatMap fun (r, T) => layoutAt T (.root r) [] 1

/-- A chain fact: `msg.value` is below `2^128` wei, past the total ether
supply, so no transaction carries more (`docs/solc-alignment.md`). -/
def etherBound : Int := 2 ^ 128

/-- Whether the statements read `msg.value`, their blocks included (not the
body of a function they call). -/
partial def readsMsgValue (ss : List RawStmt) : Bool :=
  ss.any fun s => s.exprs.any (RawExpr.any fun | .env .msgValue => true | _ => false) ||
    readsMsgValue s.blocks.flatten

section Compile

variable (C)

mutual

/-- A memory parameter followed through its members and entries. -/
partial def SpecExpr.memPath (ctx : SpecCtx C) :
    SpecExpr → Except String (Option (Ty × (NITerm C ⊕ NMAddr C)))
  | .name x => do
    if (lookupBy x ctx.locals).isSome then
      throw s!"{x} is a primitive local, not a reference path"
    match lookupBy x ctx.refs with
    | some (.mem R) =>
      if ctx.memory.isSome then pure (some (.ref R, .inl (.pv (.ofName x))))
      else throw "\\old of memory contents needs a heap snapshot, which is not supported"
    | _ => pure none
  | .field e f => do
    let some (T, p) ← e.memPath ctx | return none
    let .ref (.struct s) := T | throw s!"member access .{f} on a non-struct"
    let .inl i := p | throw "a memory reference is expected"
    let some T' := C.fieldType s f | throw s!"struct {s} has no member {f}"
    let a := NMAddr.field i f
    pure (some (T', match T' with
      | .prim _ => .inr a
      | .ref _ => .inl (.read (ctx.memory.getD .memory) a)))
  | .index e k => do
    let some (T, p) ← e.memPath ctx | return none
    let .inl i := p | throw "a memory reference is expected"
    let E ← match T with
      | .ref (.array E) | .ref (.fixed E _) => pure E
      | _ => throw "indexing something that is not a memory array"
    let (_, t) ← k.term ctx
    let a := NMAddr.at i t
    pure (some (E, match E with
      | .prim _ => .inr a
      | .ref _ => .inl (.read (ctx.memory.getD .memory) a)))
  | _ => pure none

/-- A path of state variables, members and entries, and the type it names:
`balances[a]` is `balances[a]` at `uint`. -/
partial def SpecExpr.path (ctx : SpecCtx C) : SpecExpr → Except String (Ty × NPTerm C)
  | .name x => do
    if (lookupBy x ctx.locals).isSome then
      throw s!"{x} is a primitive local, not a storage path"
    match lookupBy x ctx.refs with
    | some (.alias R) => pure (.ref R, .pv (.ofName x))
    | some (.mem _) => throw s!"{x} is a memory reference, not a storage path"
    | _ => match C.rootType x with
      | some T => pure (T, .root x)
      | none => throw s!"unknown name {x}"
  | .field e f => do
    let (T, p) ← e.path ctx
    let .ref (.struct s) := T | throw s!"member access .{f} on a non-struct"
    let some T' := C.fieldType s f | throw s!"struct {s} has no member {f}"
    pure (T', .field p f)
  | .index e k => do
    let (T, p) ← e.path ctx
    match T with
    | .ref (.mapping kp V) => do
      let (q, t) ← k.term ctx
      unless q = .prim kp || k.isNum do
        throw s!"a key of type {q.toStr} where a {kp.toStr} is expected"
      pure (V, .at p t)
    | .ref (.array E) | .ref (.fixed E _) => do
      let (_, t) ← k.term ctx
      pure (E, .at p t)
    | _ => throw "indexing something that is not a mapping or an array"
  | _ => throw "not a storage path: a state variable, `e.f` or `e[k]`"

/-- A value, and its sort: a state variable is read from the context's
storage, `find(storage, count)`, or `find(old, count)` under `\old`; a
ledger entry is a KeY `int` (`VSort.kint`), and so is arithmetic over one.
`expectK` permits an unsigned negand to widen in a ledger expression;
primitive arithmetic inside it keeps its own checked type. -/
partial def SpecExpr.term (ctx : SpecCtx C) (e : SpecExpr) (expectK : Bool := false) :
    Except String (NTm.VSort × NTerm C) := match e with
  | .num n => pure (.prim .uint, .num n)
  | .uintLit n => do
    let value ← numLit s!"uint({n})" n .uint
    pure (.prim .uint, .lit value)
  | .bool b => pure (.prim .bool, .bool b)
  | .result => do
    unless ctx.ensures do throw "\\result is only allowed in ensures"
    let some p := ctx.result | throw "\\result needs a function that returns one value"
    pure (.prim p, .pv resultVar)
  | .old e => do
    unless ctx.ensures do throw "\\old is only allowed in ensures, and not nested"
    e.term ctx.old expectK
  | .net e => do
    let (p, t) ← e.term ctx
    unless p = .prim .uint || e.isNum do
      throw s!"net(…) of a {p.toStr}, where an address is expected"
    match ctx.ledger with
    | none => pure (.kint, .net t)
    | some x => pure (.kint, .netOf x t)
  | .name x =>
    match lookupBy x ctx.locals with
    | some p => pure (.prim p, .pv (.ofName x))
    | none =>
      match ctx.ensures, ctx.rets.find? (·.1 == x) with
      | true, some (_, v, p) => pure (.prim p, .pv (.ofName v))
      | _, _ =>
        if x == "this" && (C.rootType x).isNone && (lookupBy x ctx.refs).isNone then
          pure (.prim .uint, .env .selfAddress)
        else do let (p, t) ← SpecExpr.read ctx (.name x); pure (.prim p, t)
  | .field (.name b) m => do
    if (lookupBy b ctx.locals).isNone && (lookupBy b ctx.refs).isNone && (C.rootType b).isNone then
      if let some k := EnvKey.ofParts b m then return (.prim .uint, .env k)
      if b == "this" && m == "balance" then return (.prim .uint, .env .selfBalance)
      let some ms := lookupBy b C.enums | throw s!"unknown name {b}"
      let some i := ms.findIdx? (· == m) | throw s!"enum {b} has no member {m}"
      return (.prim .uint, .num i)
    let (p, t) ← SpecExpr.read ctx (.field (.name b) m)
    pure (.prim p, t)
  | e@(.field ..) | e@(.index ..) => do let (p, t) ← SpecExpr.read ctx e; pure (.prim p, t)
  | .unop .neg (.num n) =>
    if expectK then pure (.kint, NTm.app0 (.zlit (-(n : Int))) s!"-{n}")
    else pure (.prim .int, .num (-(n : Int)))
  | .unop op a => do
    let (p, t) ← a.term ctx expectK
    if op == .neg && (p == .kint || expectK && p == .prim .uint) then
      return (.kint, NTm.app2 (.zbin .sub rfl) (NTerm.num 0) t s!"-({t.text})")
    let .prim p := p | throw s!"operator {UnOp.sym op} does not take a KeY `int`"
    unless op.accepts p do throw s!"operator {UnOp.sym op} does not take {p.toStr}"
    pure (.prim (op.ret p), .unop op t)
  | .binop op a b => do
    let ((pa, ta), (pb, tb)) ← SpecExpr.termPair ctx a b expectK
    -- beside a KeY `int` (a ledger entry), a `uint` is widened and the
    -- arithmetic is KeY's, unbounded (`NTm.resolvePairV`)
    if pa = .kint || pb = .kint then
      unless (pa = .kint || pa = .prim .uint || a.isNum) &&
          (pb = .kint || pb = .prim .uint || b.isNum) do
        throw s!"operands of {BinOp.sym op} of types {pa.toStr} and {pb.toStr}"
      if op.zArith then return (.kint, .binop op ta tb)
      if op.zCmp then return (.prim .bool, .binop op ta tb)
      throw s!"operator {BinOp.sym op} does not take a KeY `int`"
    let (.prim pa', .prim pb') := (pa, pb) | throw "internal: a KeY `int` operand"
    let p := if a.isNum then pb' else pa'
    unless a.isNum || b.isNum || pa' = pb' do
      throw s!"operands of {BinOp.sym op} of types {pa'.toStr} and {pb'.toStr}"
    unless op.accepts p do throw s!"operator {BinOp.sym op} does not take {p.toStr}"
    pure (.prim (op.ret p), .binop op ta tb)
  | .imp .. | .iff .. | .all .. | .ex .. | .member .. | .memberFilter .. =>
    throw "a formula where a value is expected"

/-- Select the ledger context from the operands' result shapes, then compile
each operand once. A ledger read resets its address operand's context without
causing retries of malformed nested expressions. -/
partial def SpecExpr.termPair (ctx : SpecCtx C) (a b : SpecExpr) (expectK : Bool := false) :
    Except String ((NTm.VSort × NTerm C) × (NTm.VSort × NTerm C)) := do
  let ledger := expectK || a.hasLedgerInt || b.hasLedgerInt
  let left ← a.term ctx ledger
  let right ← b.term ctx ledger
  pure (left, right)

/-- A read: `.length` of an array, or the word at a path. -/
partial def SpecExpr.read (ctx : SpecCtx C) : SpecExpr → Except String (PrimTy × NTerm C)
  | .field e "length" => do
    if let some (T, p) ← e.memPath ctx then
      match T, p with
      | .ref (.array _), .inl i => return (.uint, .mlen (ctx.memory.getD .memory) i)
      | .ref (.fixed _ n), .inl _ => return (.uint, .num n)
      | _, _ => throw "`.length` of something that is not a memory array"
    let (T, p) ← e.path ctx
    match T with
    | .ref (.array _) => pure (.uint, .len ctx.storage p)
    | .ref (.fixed _ n) => pure (.uint, .num n)
    | _ => throw "`.length` of something that is not an array"
  | e => do
    if let some (T, p) ← e.memPath ctx then
      match T, p with
      | .prim q, .inr a => return (q, .read (ctx.memory.getD .memory) a)
      | _, _ => throw "a memory reference where a value is expected"
    let (T, p) ← e.path ctx
    let .prim q := T | throw "a storage reference where a value is expected"
    pure (q, .find ctx.storage p)

end

/-- A clause as a formula: the connectives are the logic's, `\forall` is
`Fml.all`, a comparison is `a ⊕ b = true`, and `==` between conditions is
`<->`, as solkey writes it. -/
partial def SpecExpr.fml (ctx : SpecCtx C) : SpecExpr → Except String (NRead C)
  | .bool true => pure .tt
  | .bool false => pure .ff
  | .unop .not a => do pure (.not (← a.fml ctx))
  | .binop .and a b => do pure (.and (← a.fml ctx) (← b.fml ctx))
  | .binop .or a b => do pure (.not (.and (.not (← a.fml ctx)) (.not (← b.fml ctx))))
  | .imp a b => do pure (.imp (← a.fml ctx) (← b.fml ctx))
  | .iff a b => iff a b
  | .all p x e => do
    if reservedSpecName x then throw s!"reserved specification binder name {x}"
    pure (.all (.ofName x) p (← e.fml { ctx with locals := (x, p) :: ctx.locals }))
  | .ex p x e => do
    if reservedSpecName x then throw s!"reserved specification binder name {x}"
    pure (.not (.all (.ofName x) p (.not (← e.fml { ctx with locals := (x, p) :: ctx.locals }))))
  | .member p key items => do
    let (_, keyTerm) ← key.term C ctx
    let terms : List (NTerm C) ← items.mapM fun item => do
      let (_, t) ← item.term C ctx
      pure t
    pure fun Γ => do
      -- Check every term at one fixed sort before folding. The key is checked
      -- even for an empty collection; no erased operand can hide an error.
      let value : Tm C Γ.ctx (.val p) ← keyTerm.check (.val p) Γ
      let values : List (Tm C Γ.ctx (.val p)) ← terms.mapM fun t => t.check (.val p) Γ
      pure (Fml.finiteMember value values)
  | .memberFilter p key x items guard => do
    if reservedSpecName x then throw s!"reserved specification binder name {x}"
    let (_, keyTerm) ← key.term C ctx
    let values : List p.Denote ← items.mapM (SpecExpr.domainLiteral p)
    let guardFml ← guard.fml { ctx with locals := (x, p) :: ctx.locals }
    pure fun Γ => do
      -- Check the key before extending its scope, even when the domain is empty.
      let value : Tm C Γ.ctx (.val p) ← keyTerm.check (.val p) Γ
      let predicate ← guardFml ((.ofName x, .val p) :: Γ)
      pure (Fml.filteredMember (.ofName x) value values predicate)
  | .old e => do
    unless ctx.ensures do throw "\\old is only allowed in ensures, and not nested"
    e.fml ctx.old
  | .binop op a b => do
    if op = .eqB || op = .neB then
      let ((pa, ta), (pb, tb)) ← SpecExpr.termPair (C := C) ctx a b
      let eq ← if pa = .prim .bool && pb = .prim .bool then iff a b else pure (NRead.eq ta tb)
      return if op = .eqB then eq else .not eq
    cond (.binop op a b)
  | e => cond e
where
  /-- `a <-> b`, and `==` between conditions. -/
  iff (a b : SpecExpr) : Except String (NRead C) := do
    let φ ← a.fml ctx
    let ψ ← b.fml ctx
    pure (.and (.imp φ ψ) (.imp ψ φ))
  /-- A `bool` value as a condition, `t = true`. -/
  cond (e : SpecExpr) : Except String (NRead C) := do
    let (p, t) ← e.term C ctx
    unless p = .prim .bool do throw s!"a {p.toStr} where a condition is expected"
    pure (NRead.bool t)

/-! ### `assignable`: the words a function may change -/

/-- A step of an `assignable` location, below its state variable: a member,
the entry at a key (read in the pre-state), or every entry. -/
inductive SpecStep (C : Contract) where
  | field (f : String)
  | key (t : NTerm C)
  | all

/-- A location, checked against the contract: its state variable, the type
it names, and the steps to it.  A key is read in the pre-state, against
`old` and `oldNet` (`ctx`), as JML reads it. -/
def SpecLoc.compile (ctx : SpecCtx C) : SpecLoc → Except String (String × Ty × List (SpecStep C))
  | .root r =>
    match C.rootType r with
    | some T => pure (r, T, [])
    | none => throw s!"assignable: unknown state variable {r}"
  | .field l f => do
    let (r, T, ss) ← l.compile ctx
    let .ref (.struct s) := T | throw s!"assignable: member access .{f} on a non-struct"
    let some T' := C.fieldType s f | throw s!"assignable: struct {s} has no member {f}"
    pure (r, T', ss ++ [.field f])
  | .index l e => do
    let (r, T, ss) ← l.compile ctx
    let (q, t) ← e.term C ctx
    match T with
    | .ref (.mapping kp V) =>
      unless q = .prim kp || e.isNum do
        throw s!"assignable: a key of type {q.toStr} where a {kp.toStr} is expected"
      pure (r, V, ss ++ [.key t])
    | .ref (.array E) | .ref (.fixed E _) => pure (r, E, ss ++ [.key t])
    | _ => throw "assignable: indexing something that is not a mapping or an array"
  | .all l => do
    let (r, T, ss) ← l.compile ctx
    match T with
    | .ref (.mapping _ V) | .ref (.array V) | .ref (.fixed V _) => pure (r, V, ss ++ [.all])
    | _ => throw "assignable: `[*]` of something that is not a mapping or an array"

/-- The names a location's keys read. -/
def SpecLoc.names : SpecLoc → List String
  | .root _ => []
  | .field l _ | .all l => l.names
  | .index l e => l.names ++ e.names

/-- Whether a key reads `net(a)`, which it reads in the pre-state, `oldNet`. -/
def SpecLoc.usesNet : SpecLoc → Bool
  | .root _ => false
  | .field l _ | .all l => l.usesNet
  | .index l e => l.usesNet || e.usesNet

/-- `∀ keys. h₁ → … → φ`. -/
def closeFml (keys : List (Var × PrimTy)) (hyps : List (NRead C)) (φ : NRead C) : NRead C :=
  keys.foldl (fun φ (x, q) => .all x q φ) (hyps.foldr .imp φ)

/-- The locations below a node, entered at the key `x`: an entry `m[t]` goes
on under the condition `x = t`, `m[*]` unconditionally. -/
def enterKey (x : Var) (ls : List (List (NRead C) × List (SpecStep C))) :
    List (List (NRead C) × List (SpecStep C)) :=
  ls.filterMap fun
    | (cs, .key t :: rest) => some (cs ++ [.eq (.pv x) t], rest)
    | (cs, .all :: rest) => some (cs, rest)
    | _ => none

/-- **The frame of `assignable`**, at the node `p` of type `T`: every word
below it that no location covers is where it was, `find(storage, p) =
find(old, p)`, and so is an array's length.  `ls` are the locations still
going down, each with the conditions on the keys it was entered at; a word
one of them covers under conditions `c` is owed only where `¬c`
(`k ≠ e` for `m[e]`).  A mapping entry is every key, `∀ k`; an array's
element every index below its length. -/
partial def frameAt (T : Ty) (p : NPTerm C) (keys : List (Var × PrimTy)) (hyps : List (NRead C))
    (ls : List (List (NRead C) × List (SpecStep C))) (k : Nat) : List (NRead C) :=
  let here := ls.filter (·.2.isEmpty)
  if here.any (·.1.isEmpty) then [] else
  let hyps := hyps ++ here.map fun (cs, _) => NRead.not (NRead.conj cs)
  let ls := ls.filter (!·.2.isEmpty)
  let owe (a b : NTerm C) : NRead C := closeFml C keys hyps (.eq a b)
  match T with
  | .prim _ => [owe (.find .storage p) (.find (.pv oldVar) p)]
  | .ref (.mapping K V) =>
    let x : Var := .ofName s!"k{k}"
    frameAt V (.at p (.pv x)) ((x, K) :: keys) hyps (enterKey C x ls) (k + 1)
  | .ref (.struct s) => (structDef s).flatMap fun (f, T') =>
    frameAt T' (.field p f) keys hyps
      (ls.filterMap fun
        | (cs, .field g :: rest) => if g == f then some (cs, rest) else none
        | _ => none) k
  | .ref (.array E) =>
    let i : Var := .ofName s!"k{k}"
    owe (.len .storage p) (.len (.pv oldVar) p) ::
      frameAt E (.at p (.pv i)) ((i, .uint) :: keys)
        (hyps ++ [NRead.cmp .lt (.pv i) (.len .storage p)]) (enterKey C i ls) (k + 1)
  | .ref (.fixed E n) =>
    let i : Var := .ofName s!"k{k}"
    frameAt E (.at p (.pv i)) ((i, .uint) :: keys)
      (hyps ++ [NRead.cmp .lt (.pv i) (.num n)]) (enterKey C i ls) (k + 1)

/-- The frame of an `assignable` clause over every state variable of the
contract. -/
def assignableFml (ctx : SpecCtx C) (locs : List SpecLoc) : Except String (List (NRead C)) := do
  let cs ← locs.mapM (SpecLoc.compile C ctx)
  pure <| C.vars.flatMap fun (r, T) =>
    frameAt C T (.root r) [] [] (cs.filterMap fun (r', _, ss) => if r' == r then some ([], ss) else none) 1

variable [FreshNames]

/-- **The pieces of the obligation of `f`**, solkey's `specifiedProblemText`:
the premises every run meets by construction (`R`, `L` and what `msg.value`
is, `M`), the premises the specification states (`I ∧ requires`), the
update `{old := storage ‖ oldNet := net ‖ B}` (`B` the booking of
`msg.value`), the call
`T result; result = f(x₁, …, xₙ);`, and what is owed after it, `I`, `ensures` and
`A` one by one (a counterexample search names the one that fails).  For
`constructor`, the deployment's (the module docstring).  The call is
elaborated scoped, from the parameters in scope (newest first), each
statement typed where it is read (`SProg`): the scoped obligation places it
past the locals the update declares (`SProg.chain`, `Calculus/Spec.lean`). -/
def specPieces (f : String) :
    Except String (List (NRead C) × List (NRead C) × List (NUpdElem C) × SProg C × List (NRead C)) := do
  -- `constructor` names the contract's constructor (`Contract.ctor`)
  let ctor := f == "constructor"
  let some d := if ctor then C.ctor else lookupBy f C.funs
    | throw (if ctor then "the contract declares no constructor: an implicit one has no obligation"
      else s!"{f} is not a function of the contract")
  if d.spec.skip then throw s!"{f} is marked `skip`: it has no obligation"
  let Γ ← d.paramCtx
  let ps := d.params.filterMap fun (n, T) => match T with
    | .prim p => some (n, p)
    | _ => none
  for (n, _) in d.params do
    if reservedSpecName n then
      throw s!"{f}: a parameter named {n}, which the obligation names"
    -- `k1`, `k2`, …: the keys the layout and the frame quantify over
    if n.startsWith "k" && n.length > 1 && (n.drop 1).all Char.isDigit then
      throw s!"{f}: a parameter named {n}, which the obligation's quantifiers name"
  -- the returns, each to `result` (one) or `result_<name>` (several)
  let rets ← d.rets.mapM fun (n, T) => match T with
    | .prim p => pure (n, if d.rets.length == 1 then "result" else s!"result_{n}", p)
    | T => throw (refReturnMsg f T)
  let res := match rets with
    | [(_, _, p)] => some p
    | _ => none
  -- a deployment discards the state a `requires` would read (Lean only:
  -- solkey reads it before `storage := mtSt`, of a storage the run never sees)
  if ctor then
    for r in d.spec.requires do
      if let some x := r.names.find? fun x => (C.rootType x).isSome && !d.params.any (·.1 == x) then
        throw s!"constructor: a `requires` reads the state variable {x}, which a deployment discards"
      if r.usesNet || r.any (fun | .field (.name "this") "balance" => some true | _ => none) then
        throw "constructor: a `requires` reads the ledger or the funds, which a deployment sets"
  let pre : SpecCtx C := {
    storage := .storage
    ensures := false
    locals := ps
    refs := Γ.filter (fun (_, t) => t matches .alias _ | .mem _)
    result := none }
  let post : SpecCtx C := { pre with ensures := true, result := res, rets := rets }
  let inv ← C.inv.mapM (SpecExpr.fml C { pre with locals := [], refs := [] })
  let reqs ← d.spec.requires.mapM (SpecExpr.fml C pre)
  let enss ← d.spec.ensures.mapM (SpecExpr.fml C post)
  let frame ← match d.spec.assignable with
    | some locs =>
      assignableFml C { post with storage := .pv oldVar, ledger := some oldNetVar, result := none } locs
    | none => pure []
  let args := d.params.map fun (n, _) => RawExpr.name n
  -- `T result; result = f(x̄)@C;`: the call returns to its targets (none
  -- for a void function, `f(x̄)@C;`, still a `FunctionBodyStatement`)
  let call : List RawStmt := if ctor then [.call (.name f) args] else
    rets.map (fun (_, v, p) => RawStmt.decl (.named (p.toStr)) v none) ++
      [.tupleAssign (rets.map fun (_, v, _) => some (.name v)) (.call f args)]
  let P ← (elabStmtsP C call).runFrom' { funs := C.funs } (Γ, 1)
  -- the snapshots `\old` reads, taken where something reads them
  -- (a deployment's `old` and `oldNet` are solkey's `old := mtSt ‖
  -- oldNet := mtSt`: the update is parallel, so `old := storage` would bind
  -- the storage it discards)
  let start : NSTerm C := if ctor then .mtSt else .storage
  let snap : List (NUpdElem C) :=
    (if d.spec.ensures.any SpecExpr.usesOld || d.spec.assignable.isSome then [.store oldVar start]
      else []) ++
    if d.spec.ensures.any SpecExpr.usesOldNet || (d.spec.assignable.getD []).any SpecLoc.usesNet
    then [if ctor then .saveNetMt oldNetVar else .saveNet oldNetVar] else []
  -- the payment booked, KeY's `{net := store(net, at(msgSender),
  -- net(msgSender) + msgValue) ‖ selfBalance := selfBalance + msgValue}`; a
  -- function that is not `payable` is called with `msg.value == 0`, so its
  -- booking is left out: it changes nothing.  A deployment's is solkey's
  -- `{storage := mtSt ‖ old := mtSt ‖ oldNet := mtSt ‖ net := storeSt(mtSt,
  -- at(msgSender), msgValue) ‖ selfBalance := msgValue}`, payable or not
  let U := if ctor then
    [.storage (.mtSt)] ++ snap ++ [.netMt (.env .msgSender) (.env .msgValue), .setBalance (.env .msgValue)]
  else snap ++ if d.payable then
    [.net (.env .msgSender) .add (.env .msgValue), .selfBalance .add (.env .msgValue)] else []
  -- a payable function's `msg.value` is below the ether supply where its
  -- body's 256-bit arithmetic reads it (`Problem.callPre`, chain facts)
  let msgValue : NRead C := if d.payable then
      if readsMsgValue d.body then
        .and (NRead.cmp .ge (.env .msgValue) (.num 0))
          (NRead.cmp .lt (.env .msgValue) (.num etherBound))
      else NRead.cmp .ge (.env .msgValue) (.num 0)
    else .eq (.env .msgValue) (.num 0)
  let read := (C.inv ++ d.spec.requires ++ d.spec.ensures).flatMap SpecExpr.names ++
    (d.spec.assignable.getD []).flatMap SpecLoc.names
  -- a deployment assumes no invariant and no layout: both are of the
  -- storage it discards (solkey's has no `CInv(storage, net)` premise)
  pure ((if Γ.any (fun (_, t) => t matches .alias _ | .mem _) then
        [NRead.refInputs (ECtx.toNCtx Γ)] else []) ++
      ps.map (fun (n, p) => rangeFml (.pv (.ofName n)) p) ++
      (if ctor then [] else layoutFmls C read) ++ [msgValue],
    (if ctor then [] else inv) ++ reqs, U, P, inv ++ enss ++ frame)

end Compile

/-- `spec[C]{f}`: the obligation of the function `f` of the contract `C`,
from its `requires`/`ensures` clauses and `C`'s invariants, a scoped
formula (`Calculus/Spec.lean`'s `cspec[C]{f}`). -/
syntax "spec[" term "]{ " ident " }" : term

/-- `spec!{f}`: `spec[C]{f}` for the file's `InContract` contract. -/
syntax "spec!{ " ident " }" : term

macro_rules
  | `(spec!{ $f:ident }) => `(spec[InContract.contract]{ $f })

/-- What `sol_spec_close` does before its last step: `sol_close`'s
evaluation and reads, the landed states opened to binders. -/
macro "sol_spec_prep" : tactic => `(tactic|
  (sol_close_unwrap
   intro σ
   sol_close_eval
   all_goals try sol_close_facts
   all_goals try sol_close_reads
   -- the states an update lands on (`CloseS.LandedAll`), opened to binders
   all_goals (try simp only [CloseS.landedAll_def])
   all_goals try (intros; sol_close_reads_all)
   all_goals try (subst_vars; sol_close_reads_all)
   all_goals (try intros)
   all_goals (try simp only [Close.exists_unit, Close.forall_unit, Close.exists_const_type,
      Close.forall_const_type] at *)
   -- a premise `Nonempty (Landed …)` where the rest no longer reads a landed
   -- state: every premise introduced, every conjunct its own goal
   all_goals (repeat' (first | intro _ | apply And.intro))))

/-- Arithmetic, then the existing bounded KeY `allLeft` fallback or bounded
`grind`. Every chosen universal instance is a checked proof application. -/
macro "sol_spec_finish" : tactic => `(tactic|
  first | omega | (sol_close_all; first | omega | grind (gen := 3)) | grind (gen := 3))

/-- The closing half of `sol_spec`: `sol_spec_prep`, then `sol_spec_finish`
on every goal. -/
macro "sol_spec_close" : tactic => `(tactic|
  all_goals
   (sol_spec_prep
    all_goals sol_spec_finish))

/-- `sol_spec`: prove an obligation `spec[C]{f}` by symbolic execution and
`sol_spec_close`. -/
macro "sol_spec" : tactic => `(tactic| (sol_symex; sol_spec_close))

/-- `sol_spec` that does not fail: what `omega` and `grind` do not close is
left as goals, one per path and conjunct, for a caller to show or to work
on. -/
macro "sol_spec_try" : tactic => `(tactic|
  (sol_symex
   all_goals
    (sol_spec_prep
     all_goals try sol_spec_finish)))

end Solidity
