import Solidity.Calculus.Close

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
  {old := storage ‖ oldNet := net ‖ B} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures ∧ A)
```

where `B` books `msg.value`, KeY's
`net := store(net, at(msg.sender), net(msg.sender) + msg.value) ‖ selfBalance := selfBalance + msg.value`.

The parameters are free locals, so `⊨` ranges over every argument; `R`
gives each its type's range, since a free local also ranges over values of
other types and over none (solkey's parameters are KeY `int`s, unbounded,
and need no such fact).  `L` is the contract's layout (`layoutFmls`): `⊨`
also ranges over storages the contract never has.  `M` is what `msg.value`
is: `>= 0`, or `== 0` for a function that is not `payable`.  `I` is the
contract's invariants, assumed and owed (solkey's `CInv(storage, net)`).
`A` is the frame of an `assignable` clause (`assignableFml`).

The update takes solkey's snapshots only where something reads them: `old`
when an `ensures` reads `\old` or an `assignable` clause is given, `oldNet`
when an `\old(…)` reads `net(a)`.  The booking of `msg.value`, the sender's
ledger entry and the contract's funds credited, is there for a `payable`
function only: `M` makes the other's a booking of `0`.

Not ported: the benchmarks' clauses over `net(a)` are not tried.  A spec's
arithmetic is Solidity's, checked at its operands' type, where solkey's is
KeY's unbounded `int`: an overflowing side makes its equation false rather
than true of a larger number.  Every equation compiled here is the
interpreter's, `Fml.eqD` (both sides return, with one value), not the total
`Fml.eq`.  `net(a)` is read as a `uint`, as `msg.value`
is, so `\old(net(a)) + msg.value` is checked too.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- Where a clause is read: the storage its state variables are read from,
whether `\old` and `\result` mean something (an `ensures`), the locals in
scope (the parameters and the quantified variables), and `\result`'s type. -/
structure SpecCtx (C : Contract) where
  storage : STerm C
  ensures : Bool
  locals : List (String × PrimTy)
  result : Option PrimTy
  /-- The ledger `net(a)` reads: the current one, or the snapshot bound at
  the variable (`oldNet` under `\old`). -/
  ledger : Option Var := none

/-- The storage variable `\old` reads, solkey's `old`. -/
def oldVar : Var := .ofName "old"

/-- The ledger variable `\old(net(a))` reads, solkey's `oldNet`. -/
def oldNetVar : Var := .ofName "oldNet"

/-- The local `\result` names, solkey's `result`. -/
def resultVar : Var := .ofName "result"

/-- `\old(e)` is read against `old` and `oldNet`, and not nested. -/
def SpecCtx.old (ctx : SpecCtx C) : SpecCtx C :=
  { ctx with storage := .pv oldVar, ensures := false, ledger := some oldNetVar }

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
  | e@(.num _) | e@(.bool _) | e@(.name _) | e@.result => (here e).getD leaf

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

/-- The conjunction of the clauses, `true` for none. -/
def Fml.conj : List (Fml C) → Fml C
  | [] => .tt
  | [φ] => φ
  | φ :: ψs => .and φ (Fml.conj ψs)

/-- `t` is a value of its type: `0 <= t <= 2^256 - 1` for a `uint`, `!t`
defined for a `bool`. -/
def rangeFml (t : Term C) : PrimTy → Fml C
  | .uint => .and (cmpFml .le .uint (.lit (.int 0)) t) (cmpFml .le .uint t (.lit (.int (uintBound - 1))))
  | .int => .and (cmpFml .le .int (.lit (.int (-intBound))) t) (cmpFml .le .int t (.lit (.int (intBound - 1))))
  | .bool => .eqD (.unop .not .bool t) (.unop .not .bool t)

/-- **The layout, as premises**: every word the declared state holds is a
value of its type, `0 <= count <= 2^256 - 1`, and so at every key of a
mapping, `∀ uint k1; 0 <= balances[k1] ∧ …` (not inside an array).  Every
storage the contract reaches has them; `⊨` ranges over every storage, where
`balances` may be no mapping (`balances[a] == \old(balances[a])` is then
false: a side is undefined) or hold a `bool` (which `delete` resets to
`false`, not `0`).  solkey's reads are total and typed, and need none. -/
partial def layoutAt (T : Ty) (p : PTerm C) (keys : List (Var × PrimTy)) (k : Nat) : List (Fml C) :=
  match T with
  | .prim q =>
    [keys.foldl (fun φ (x, q) => .all x q φ) (rangeFml (.find .storage p) q)]
  | .ref (.mapping (.prim K) V) =>
    let x : Var := .ofName s!"k{k}"
    layoutAt V (.at p (.pv x)) ((x, K) :: keys) (k + 1)
  | .ref (.struct s) => (structDef s).flatMap fun (f, T') => layoutAt T' (.field p f) keys k
  | _ => []

/-- The names a clause reads. -/
def SpecExpr.names : SpecExpr → List String :=
  SpecExpr.foldMap [] (· ++ ·) fun | .name x => some [x] | _ => none

/-- The layout premises of the state variables among `rs`: those the
clauses read.  What only the body reads needs none: a read the program
makes is guarded by the program, which reverts where it is undefined. -/
def layoutFmls (C : Contract) (rs : List String) : List (Fml C) :=
  (C.vars.filter fun (r, _) => rs.contains r).flatMap fun (r, T) => layoutAt T (.root r) [] 1

section Compile

variable (C)

mutual

/-- A path of state variables, members and entries, and the type it names:
`balances[a]` is `balances[a]` at `uint`. -/
partial def SpecExpr.path (ctx : SpecCtx C) : SpecExpr → Except String (Ty × PTerm C)
  | .name x =>
    match C.rootType x with
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
    | .ref (.mapping (.prim kp) V) => do
      let (q, t) ← k.term ctx
      unless q = kp || k.isNum do throw s!"a key of type {primName q} where a {primName kp} is expected"
      pure (V, .at p t)
    | .ref (.array E) | .ref (.fixed E _) => do
      let (_, t) ← k.term ctx
      pure (E, .at p t)
    | _ => throw "indexing something that is not a mapping or an array"
  | _ => throw "not a storage path: a state variable, `e.f` or `e[k]`"

/-- A value, and its type: a state variable is read from the context's
storage, `find(storage, count)`, or `find(old, count)` under `\old`. -/
partial def SpecExpr.term (ctx : SpecCtx C) : SpecExpr → Except String (PrimTy × Term C)
  | .num n => pure (.uint, .lit (.int n))
  | .bool b => pure (.bool, .lit (.bool b))
  | .result => do
    unless ctx.ensures do throw "\\result is only allowed in ensures"
    let some p := ctx.result | throw "\\result needs a function that returns a value"
    pure (p, .pv resultVar)
  | .old e => do
    unless ctx.ensures do throw "\\old is only allowed in ensures, and not nested"
    e.term ctx.old
  | .net e => do
    let (p, t) ← e.term ctx
    unless p = .uint || e.isNum do throw s!"net(…) of a {primName p}, where an address is expected"
    match ctx.ledger with
    | none => pure (.uint, .net t)
    | some x => pure (.uint, .netOf x t)
  | .name x =>
    match lookupBy x ctx.locals with
    | some p => pure (p, .pv (.ofName x))
    | none => SpecExpr.read ctx (.name x)
  | .field (.name b) m => do
    if (lookupBy b ctx.locals).isNone && (C.rootType b).isNone then
      if let some k := EnvKey.ofParts b m then return (.uint, .env k)
      if b == "this" && m == "balance" then return (.uint, .env .selfBalance)
      let some ms := lookupBy b C.enums | throw s!"unknown name {b}"
      let some i := ms.findIdx? (· == m) | throw s!"enum {b} has no member {m}"
      return (.uint, .lit (.int i))
    SpecExpr.read ctx (.field (.name b) m)
  | e@(.field ..) | e@(.index ..) => SpecExpr.read ctx e
  | .unop .neg (.num n) => pure (.int, .lit (.int (-(n : Int))))
  | .unop op a => do
    let (p, t) ← a.term ctx
    unless op.accepts p do throw s!"operator {UnOp.sym op} does not take {primName p}"
    pure (op.ret p, .unop op p t)
  | .binop op a b => do
    let (pa, ta) ← a.term ctx
    let (pb, tb) ← b.term ctx
    let p := if a.isNum then pb else pa
    unless a.isNum || b.isNum || pa = pb do
      throw s!"operands of {BinOp.sym op} of types {primName pa} and {primName pb}"
    unless op.accepts p do throw s!"operator {BinOp.sym op} does not take {primName p}"
    pure (op.ret p, .binop op p ta tb)
  | .imp .. | .iff .. | .all .. | .ex .. => throw "a formula where a value is expected"

/-- A read: `.length` of an array, or the word at a path. -/
partial def SpecExpr.read (ctx : SpecCtx C) : SpecExpr → Except String (PrimTy × Term C)
  | .field e "length" => do
    let (T, p) ← e.path ctx
    match T with
    | .ref (.array _) => pure (.uint, .len ctx.storage p)
    | .ref (.fixed _ n) => pure (.uint, .lit (.int n))
    | _ => throw "`.length` of something that is not an array"
  | e => do
    let (T, p) ← e.path ctx
    let .prim q := T | throw "a storage reference where a value is expected"
    pure (q, .find ctx.storage p)

end

/-- A clause as a formula: the connectives are the logic's, `\forall` is
`Fml.all`, a comparison is `a ⊕ b = true`, and `==` between conditions is
`<->`, as solkey writes it. -/
partial def SpecExpr.fml (ctx : SpecCtx C) : SpecExpr → Except String (Fml C)
  | .bool true => pure .tt
  | .bool false => pure .ff
  | .unop .not a => do pure (.not (← a.fml ctx))
  | .binop .and a b => do pure (.and (← a.fml ctx) (← b.fml ctx))
  | .binop .or a b => do pure (.not (.and (.not (← a.fml ctx)) (.not (← b.fml ctx))))
  | .imp a b => do pure (.imp (← a.fml ctx) (← b.fml ctx))
  | .iff a b => iff a b
  | .all p x e => do pure (.all (.ofName x) p (← e.fml { ctx with locals := (x, p) :: ctx.locals }))
  | .ex p x e => do
    pure (.not (.all (.ofName x) p (.not (← e.fml { ctx with locals := (x, p) :: ctx.locals }))))
  | .old e => do
    unless ctx.ensures do throw "\\old is only allowed in ensures, and not nested"
    e.fml ctx.old
  | .binop op a b => do
    if op = .eqB || op = .neB then
      let (pa, ta) ← a.term C ctx
      let (pb, tb) ← b.term C ctx
      let eq ← if pa = .bool && pb = .bool then iff a b else pure (Fml.eqD ta tb)
      return if op = .eqB then eq else .not eq
    cond (.binop op a b)
  | e => cond e
where
  /-- `a <-> b`, and `==` between conditions. -/
  iff (a b : SpecExpr) : Except String (Fml C) := do
    let φ ← a.fml ctx
    let ψ ← b.fml ctx
    pure (.and (.imp φ ψ) (.imp ψ φ))
  /-- A `bool` value as a condition, `t = true`. -/
  cond (e : SpecExpr) : Except String (Fml C) := do
    let (p, t) ← e.term C ctx
    unless p = .bool do throw s!"a {primName p} where a condition is expected"
    pure (boolFml t)

/-! ### `assignable`: the words a function may change -/

/-- A step of an `assignable` location, below its state variable: a member,
the entry at a key (read in the pre-state), or every entry. -/
inductive SpecStep (C : Contract) where
  | field (f : String)
  | key (t : Term C)
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
    | .ref (.mapping (.prim kp) V) =>
      unless q = kp || e.isNum do
        throw s!"assignable: a key of type {primName q} where a {primName kp} is expected"
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
def closeFml (keys : List (Var × PrimTy)) (hyps : List (Fml C)) (φ : Fml C) : Fml C :=
  keys.foldl (fun φ (x, q) => .all x q φ) (hyps.foldr .imp φ)

/-- The locations below a node, entered at the key `x`: an entry `m[t]` goes
on under the condition `x = t`, `m[*]` unconditionally. -/
def enterKey (x : Var) (ls : List (List (Fml C) × List (SpecStep C))) :
    List (List (Fml C) × List (SpecStep C)) :=
  ls.filterMap fun
    | (cs, .key t :: rest) => some (cs ++ [.eqD (.pv x) t], rest)
    | (cs, .all :: rest) => some (cs, rest)
    | _ => none

/-- **The frame of `assignable`**, at the node `p` of type `T`: every word
below it that no location covers is where it was, `find(storage, p) =
find(old, p)`, and so is an array's length.  `ls` are the locations still
going down, each with the conditions on the keys it was entered at; a word
one of them covers under conditions `c` is owed only where `¬c`
(`k ≠ e` for `m[e]`).  A mapping entry is every key, `∀ k`; an array's
element every index below its length. -/
partial def frameAt (T : Ty) (p : PTerm C) (keys : List (Var × PrimTy)) (hyps : List (Fml C))
    (ls : List (List (Fml C) × List (SpecStep C))) (k : Nat) : List (Fml C) :=
  let here := ls.filter (·.2.isEmpty)
  if here.any (·.1.isEmpty) then [] else
  let hyps := hyps ++ here.map fun (cs, _) => Fml.not (Fml.conj cs)
  let ls := ls.filter (!·.2.isEmpty)
  -- owed where the word was there to begin with: `⊨` also ranges over
  -- storages without it, where both sides halt
  let owe (a b : Term C) : Fml C := closeFml C keys hyps (.imp (.eqD b b) (.eqD a b))
  match T with
  | .prim _ => [owe (.find .storage p) (.find (.pv oldVar) p)]
  | .ref (.mapping (.prim K) V) =>
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
        (hyps ++ [cmpFml .lt .uint (.pv i) (.len .storage p)]) (enterKey C i ls) (k + 1)
  | .ref (.fixed E n) =>
    let i : Var := .ofName s!"k{k}"
    frameAt E (.at p (.pv i)) ((i, .uint) :: keys)
      (hyps ++ [cmpFml .lt .uint (.pv i) (.lit (.int n))]) (enterKey C i ls) (k + 1)
  | _ => []

/-- The frame of an `assignable` clause over every state variable of the
contract. -/
def assignableFml (ctx : SpecCtx C) (locs : List SpecLoc) : Except String (List (Fml C)) := do
  let cs ← locs.mapM (SpecLoc.compile C ctx)
  pure <| C.vars.flatMap fun (r, T) =>
    frameAt C T (.root r) [] [] (cs.filterMap fun (r', _, ss) => if r' == r then some ([], ss) else none) 1

variable [FreshNames]

/-- **The pieces of the obligation of `f`**, solkey's `specifiedProblemText`:
the premises every run meets by construction (`R`, `L` and what `msg.value`
is, `M`), the premises the specification states (`I ∧ requires`), the
update `{old := storage ‖ oldNet := net ‖ B}` (`B` the booking of
`msg.value`), the call
`T result = f(x₁, …, xₙ);`, and what is owed after it, `I`, `ensures` and
`A` one by one (a counterexample search names the one that fails). -/
def specPieces (f : String) :
    Except String (List (Fml C) × List (Fml C) × Upd C × Prog C × List (Fml C)) := do
  let some d := lookupBy f C.funs | throw s!"{f} is not a function of the contract"
  if d.spec.skip then throw s!"{f} is marked `skip`: it has no obligation"
  let ps ← d.params.mapM fun (n, T) => match T with
    | .prim p => pure (n, p)
    | _ => throw s!"{f}: the parameter {n} has a reference type"
  for (n, _) in ps do
    if n == "old" || n == "oldNet" || n == "result" then
      throw s!"{f}: a parameter named {n}, which the obligation names"
    -- `k1`, `k2`, …: the keys the layout and the frame quantify over
    if n.startsWith "k" && n.length > 1 && (n.drop 1).all Char.isDigit then
      throw s!"{f}: a parameter named {n}, which the obligation's quantifiers name"
  let res ← match d.ret with
    | none => pure none
    | some (_, .prim p) => pure (some p)
    | some (_, T) => throw (refReturnMsg f T)
  let pre : SpecCtx C := { storage := .storage, ensures := false, locals := ps, result := none }
  let post : SpecCtx C := { pre with ensures := true, result := res }
  let inv ← C.inv.mapM (SpecExpr.fml C { pre with locals := [] })
  let reqs ← d.spec.requires.mapM (SpecExpr.fml C pre)
  let enss ← d.spec.ensures.mapM (SpecExpr.fml C post)
  let frame ← match d.spec.assignable with
    | some locs =>
      assignableFml C { post with storage := .pv oldVar, ledger := some oldNetVar, result := none } locs
    | none => pure []
  let args := ps.map fun (n, _) => RawExpr.name n
  let call : RawStmt := match res with
    | some p => .decl (.named (primName p)) "result" (some (.call f args))
    | none => .call (.name f) args
  let P ← ((elabStmts C [call]).run C.funs).run' (ps.map fun (n, p) => (n, LocalTy.val p), 1)
  -- the snapshots `\old` reads, taken where something reads them
  let snap : Upd C :=
    (if d.spec.ensures.any SpecExpr.usesOld || d.spec.assignable.isSome then [.store oldVar .storage]
      else []) ++
    if d.spec.ensures.any SpecExpr.usesOldNet || (d.spec.assignable.getD []).any SpecLoc.usesNet
    then [.saveNet oldNetVar] else []
  -- the payment booked, KeY's `{net := store(net, at(msgSender),
  -- net(msgSender) + msgValue) ‖ selfBalance := selfBalance + msgValue}`; a
  -- function that is not `payable` is called with `msg.value == 0`, so its
  -- booking is left out: it changes nothing
  let U := snap ++ if d.payable then
    [.net (.env .msgSender) .add (.env .msgValue), .selfBalance .add (.env .msgValue)] else []
  let msgValue : Fml C := if d.payable then cmpFml .ge .uint (.env .msgValue) (.lit (.int 0))
    else .eqD (.env .msgValue) (.lit (.int 0))
  let read := (C.inv ++ d.spec.requires ++ d.spec.ensures).flatMap SpecExpr.names ++
    (d.spec.assignable.getD []).flatMap SpecLoc.names
  pure (ps.map (fun (n, p) => rangeFml (.pv (.ofName n)) p) ++ layoutFmls C read ++ [msgValue],
    inv ++ reqs, U, P, inv ++ enss ++ frame)

/-- The conclusion `{U} [ P ] (φ₁ ∧ … ∧ φₙ)`, the update left out when it
is empty. -/
def specBody (U : Upd C) (P : Prog C) (posts : List (Fml C)) : Fml C :=
  let body : Fml C := .modal .box P (Fml.conj posts)
  if U.isEmpty then body else .upd .box U body

/-- **The parts of the obligation of `f`**: the premises met by
construction, the premises stated, and the conclusion
`{old := storage ‖ oldNet := net ‖ B} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures ∧ A)`. -/
def specParts (f : String) : Except String (List (Fml C) × List (Fml C) × Fml C) := do
  let (a, b, U, P, posts) ← specPieces C f
  pure (a, b, specBody C U P posts)

/-- **The obligation of `f`**: `R ∧ L ∧ M ∧ I ∧ requires → {old := storage ‖
oldNet := net ‖ B} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures ∧ A)`,
the parts of `specParts` put together. -/
def specObligation (f : String) : Except String (Fml C) := do
  let (a, b, body) ← specParts C f
  pure (.imp (Fml.conj (a ++ b)) body)

end Compile

/-- `spec[C]{f}`: the obligation of the function `f` of the contract `C`,
from its `requires`/`ensures` clauses and `C`'s invariants. -/
syntax "spec[" term "]{ " ident " }" : term

/-- `spec!{f}`: `spec[C]{f}` for the file's `InContract` contract. -/
syntax "spec!{ " ident " }" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(spec[ $c ]{ $f:ident }) =>
    elabAgainst c fun q => `((specObligation $c $(quote f.getId.toString)).map (Fml.quote $q))

macro_rules
  | `(spec!{ $f:ident }) => `(spec[InContract.contract]{ $f })

/-! ## Closing: the quantifier's range -/

namespace Close

/-- A `uint` quantifier ranges over `[0, 2^256)`. -/
theorem forall_admits_uint (P : Value → Prop) :
    (∀ v, PrimTy.uint.admits v → P v) ↔ ∀ n : Int, 0 ≤ n → n < uintBound → P (.int n) := by
  constructor
  · intro h n h₀ h₁; exact h (.int n) ⟨h₀, h₁⟩
  · intro h v hv; cases v with
    | int n => exact h n hv.1 hv.2
    | bool _ => exact hv.elim

/-- An `int` quantifier ranges over `[-2^255, 2^255)`. -/
theorem forall_admits_int (P : Value → Prop) :
    (∀ v, PrimTy.int.admits v → P v) ↔ ∀ n : Int, -intBound ≤ n → n < intBound → P (.int n) := by
  constructor
  · intro h n h₀ h₁; exact h (.int n) ⟨h₀, h₁⟩
  · intro h v hv; cases v with
    | int n => exact h n hv.1 hv.2
    | bool _ => exact hv.elim

/-- A `bool` quantifier ranges over `true` and `false`. -/
theorem forall_admits_bool (P : Value → Prop) :
    (∀ v, PrimTy.bool.admits v → P v) ↔ ∀ b : Bool, P (.bool b) := by
  constructor
  · intro h b; exact h (.bool b) trivial
  · intro h v hv; cases v with
    | bool b => exact h b
    | int _ => exact hv.elim

end Close

attribute [close_rw] Close.forall_admits_uint Close.forall_admits_int Close.forall_admits_bool

/-- What `sol_spec_close` does before its last step: `sol_close`'s
evaluation and reads, knowing also that a word read is a word
(`Close.asValue_eq_ok`), which the layout premises of a specification say of
every key (a `delete` then leaves its type's default). -/
macro "sol_spec_prep" : tactic => `(tactic|
  (sol_close_unwrap
   intro σ
   sol_close_eval
   all_goals try sol_close_facts
   all_goals try sol_close_reads
   all_goals try (intros; sol_close_reads_all)
   all_goals try (subst_vars; sol_close_reads_all)
   all_goals (try intros)
   all_goals (try simp only [Close.exists_unit, Close.forall_unit, exists_const, forall_const] at *)
   all_goals (try simp only [Close.asValue_eq_ok] at *)))

/-- The last step of `sol_spec_close`: `omega` or `grind`, `grind`'s
instantiation bounded, since the layout premises are quantified. -/
macro "sol_spec_finish" : tactic => `(tactic|
  first | omega | grind (gen := 3) [Close.defaultOf_int, Close.defaultOf_bool])

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
