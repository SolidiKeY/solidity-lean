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
R ∧ L ∧ I ∧ requires → {old := storage} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures)
```

The parameters are free locals, so `⊨` ranges over every argument; `R`
gives each its type's range, since a free local also ranges over values of
other types and over none (solkey's parameters are KeY `int`s, unbounded,
and need no such fact).  `L` is the contract's layout (`layoutFmls`): `⊨`
also ranges over storages the contract never has.  `I` is the contract's invariants, assumed and owed
(solkey's `CInv(storage, net)`).  The update `{old := storage}` is there only
when an `ensures` reads `\old`, as solkey's is.

Not ported: `net(a)` (no term reads the ledger) and so `oldNet`, and the
booking of `msg.value` in front of the call (`net := … + msgValue ‖
selfBalance := … + msgValue`): the precondition is solkey's without
`msgValue ≥ 0`/`msgValue = 0`.  A spec's arithmetic is Solidity's, checked at
its operands' type, where solkey's is KeY's unbounded `int`: an overflowing
side makes its equation false rather than true of a larger number.
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

/-- The storage variable `\old` reads, solkey's `old`. -/
def oldVar : Var := .ofName "old"

/-- The local `\result` names, solkey's `result`. -/
def resultVar : Var := .ofName "result"

/-- `\old(e)` is read against `old`, and not nested. -/
def SpecCtx.old (ctx : SpecCtx C) : SpecCtx C :=
  { ctx with storage := .pv oldVar, ensures := false }

/-- Whether an `\old` occurs. -/
def SpecExpr.usesOld : SpecExpr → Bool
  | .old _ => true
  | .net e | .field e _ | .unop _ e | .all _ _ e | .ex _ _ e => e.usesOld
  | .index a b | .binop _ a b | .imp a b | .iff a b => a.usesOld || b.usesOld
  | .num _ | .bool _ | .name _ | .result => false

/-- A number literal: it takes the type of the other operand. -/
def SpecExpr.isNum : SpecExpr → Bool
  | .num _ => true
  | _ => false

/-- `a ⊕ b = true`: a comparison as a formula. -/
def cmpFml (op : BinOp) (p : PrimTy) (a b : Term C) : Fml C :=
  .eq (.binop op p a b) (.lit (.bool true))

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
  | .bool => .eq (.unop .not .bool t) (.unop .not .bool t)

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
def SpecExpr.names : SpecExpr → List String
  | .name x => [x]
  | .old e | .net e | .field e _ | .unop _ e | .all _ _ e | .ex _ _ e => e.names
  | .index a b | .binop _ a b | .imp a b | .iff a b => a.names ++ b.names
  | .num _ | .bool _ | .result => []

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
  | .net _ => throw "net(…): no term reads the ledger"
  | .name x =>
    match lookupBy x ctx.locals with
    | some p => pure (p, .pv (.ofName x))
    | none => SpecExpr.read ctx (.name x)
  | .field (.name b) m => do
    if (lookupBy b ctx.locals).isNone && (C.rootType b).isNone then
      match b, m with
      | "msg", "sender" => return (.uint, .env .msgSender)
      | "msg", "value" => return (.uint, .env .msgValue)
      | "block", "timestamp" => return (.uint, .env .timestamp)
      | "this", "balance" => return (.uint, .env .selfBalance)
      | _, _ =>
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
  | .iff a b => do
    let φ ← a.fml ctx
    let ψ ← b.fml ctx
    pure (.and (.imp φ ψ) (.imp ψ φ))
  | .all p x e => do pure (.all (.ofName x) p (← e.fml { ctx with locals := (x, p) :: ctx.locals }))
  | .ex p x e => do
    pure (.not (.all (.ofName x) p (.not (← e.fml { ctx with locals := (x, p) :: ctx.locals }))))
  | .old e => do
    unless ctx.ensures do throw "\\old is only allowed in ensures, and not nested"
    e.fml ctx.old
  | e@(.binop op a b) => do
    if op = .eqB || op = .neB then
      let (pa, ta) ← a.term C ctx
      let (pb, tb) ← b.term C ctx
      let eq ← if pa = .bool && pb = .bool then do
          let φ ← a.fml ctx
          let ψ ← b.fml ctx
          pure (Fml.and (.imp φ ψ) (.imp ψ φ))
        else pure (Fml.eq ta tb)
      return if op = .eqB then eq else .not eq
    let (p, t) ← e.term C ctx
    unless p = .bool do throw s!"a {primName p} where a condition is expected"
    pure (.eq t (.lit (.bool true)))
  | e => do
    let (p, t) ← e.term C ctx
    unless p = .bool do throw s!"a {primName p} where a condition is expected"
    pure (.eq t (.lit (.bool true)))

variable [FreshNames]

/-- **The obligation of `f`**, solkey's `specifiedProblemText`:
`R ∧ L ∧ I ∧ requires → {old := storage} [ T result = f(x₁, …, xₙ); ] (I ∧ ensures)`. -/
def specObligation (f : String) : Except String (Fml C) := do
  let some d := lookupBy f C.funs | throw s!"{f} is not a function of the contract"
  if d.spec.skip then throw s!"{f} is marked `skip`: it has no obligation"
  let ps ← d.params.mapM fun (n, T) => match T with
    | .prim p => pure (n, p)
    | _ => throw s!"{f}: the parameter {n} has a reference type"
  for (n, _) in ps do
    if n == "old" || n == "result" then throw s!"{f}: a parameter named {n}, which the obligation names"
  let res ← match d.ret with
    | none => pure none
    | some (_, .prim p) => pure (some p)
    | some _ => throw s!"{f} returns a reference type"
  let pre : SpecCtx C := { storage := .storage, ensures := false, locals := ps, result := none }
  let post : SpecCtx C := { pre with ensures := true, result := res }
  let inv ← C.inv.mapM (SpecExpr.fml C { pre with locals := [] })
  let reqs ← d.spec.requires.mapM (SpecExpr.fml C pre)
  let enss ← d.spec.ensures.mapM (SpecExpr.fml C post)
  let args := ps.map fun (n, _) => RawExpr.name n
  let call : RawStmt := match res with
    | some p => .decl (.named (primName p)) "result" (some (.call f args))
    | none => .call (.name f) args
  let P ← ((elabStmts C [call]).run C.funs).run' (ps.map fun (n, p) => (n, LocalTy.val p), 1)
  let body : Fml C := .modal .box P (Fml.conj (inv ++ enss))
  let body := if d.spec.ensures.any SpecExpr.usesOld then .upd .box [.store oldVar .storage] body
    else body
  let read := (C.inv ++ d.spec.requires ++ d.spec.ensures).flatMap SpecExpr.names
  pure (.imp (Fml.conj (ps.map (fun (n, p) => rangeFml (.pv (.ofName n)) p) ++ layoutFmls C read ++
      inv ++ reqs))
    body)

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

/-- The closing half of `sol_spec`: `sol_close`, knowing also that a word
read is a word (`Close.asValue_eq_ok`), which the layout premises of a
specification say of every key (a `delete` then leaves its type's default),
and with `grind`'s instantiation bounded, since those premises are
quantified. -/
macro "sol_spec_close" : tactic => `(tactic|
  all_goals
   (sol_close_unwrap
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    all_goals (try simp only [Close.exists_unit, Close.forall_unit, exists_const, forall_const] at *)
    all_goals (try simp only [Close.asValue_eq_ok] at *)
    all_goals first | omega | grind (gen := 3) [Close.defaultOf_int, Close.defaultOf_bool]))

/-- `sol_spec`: prove an obligation `spec[C]{f}` by symbolic execution and
`sol_spec_close`. -/
macro "sol_spec" : tactic => `(tactic| (sol_symex; sol_spec_close))

end Solidity
