import Solidity.Calculus.Decide
import Solidity.Calculus.Delab
import Solidity.Calculus.Quote
import Solidity.Calculus.ProofTree
import Solidity.Calculus.Surface
import Solidity.Tools.ProofTree
import Solidity.Tools.Taclet

/-!
# `#wp`, `#step`: looking inside the calculus

```
#wp cdl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }
#step cdl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }
```

* `#wp φ` runs the scoped strategy to the end (`symex 200`, what
  `sol_symex` does) and prints what is left, the first-order formula whose
  validity is `φ`'s.  When its erasure (`Fml.erase`) is in
  `sol_decide`'s fragment (`NFml.inL`) it also prints its reduction
  (`NFml.reduce`): the updates pushed in and every read of a write
  eliminated, a formula over the initial state alone, printed by `LFml.fmt`
  in KeY's spelling (`find(storage, alice.age)`, `save(s, p, w)`,
  `delAt(s, p)`, `if(i = j) then a else b`, `write(m, idC(idp0, nil), at(i),
  v)`, `=`, `∧`, `→`, `¬`, `∀ uint x; φ`).
* `#step φ` takes one step and names the rule the scoped strategy fires
  (`ruleAtC?`, `ruleOf?`), as a line of `#derivation`.

`φ` is a closed scoped formula of a named contract, `φ : Fml C Γ`
(`cdl!{ … }`, or `dl!{ … }` under `open scoped Solidity.Scoped`): the
strategy runs as compiled code (`unsafe evalExpr`), its result is quoted
(`Fml.quote`) against the contract's name and printed by `Delab`'s
printer (`elabCoreFormula?`, `Tools/ProofTree.lean`).

A file that inspects the calculus imports this module alone: it brings the
proof tree's commands (`#proof_tree`, `#proof_node`, `#proof_tree_json`,
`Tools/ProofTree.lean`) and `#taclet` (`Tools/Taclet.lean`) with it.
-/

namespace Solidity.Tools

open Semantics Decide

/-! ## The reduced formula, printed -/

/-- A key shape as its test is named. -/
def KShape.fmt : KShape → String
  | .map => "isMap"
  | .fixed => "isFixed"

/-- A path whose keys are integer literals. -/
def LPath.total : LPath → Bool
  | .root _ => true
  | .field q _ => LPath.total q
  | .at q (.lit (.int _)) => LPath.total q
  | .at _ _ => false

/-- A guard that always returns, and is not printed: a literal, or the keys
of a path with literal keys (`ok(alice.age)`). -/
def LTerm.total : LTerm → Bool
  | .lit _ | .env _ => true
  | .pok q => LPath.total q
  | _ => false

/-- The guards of a sequence and the value it returns: `seq d a` returns
`a` where `d` returns, and a guard that is itself a sequence contributes its
guards and its value. -/
def LTerm.guards : LTerm → List LTerm × LTerm
  | .seq d a =>
    let (gd, vd) := LTerm.guards d
    let (ga, va) := LTerm.guards a
    (gd ++ [vd] ++ ga, va)
  | t => ([], t)

/-- The allocation ordinal `k` as KeY's Skolem identity: `idp0`. -/
def idpFmt (k : Nat) : String := s!"idp{k}"

/-- A memory name as KeY writes it, `idC(idp, flds)`: `idC(idp0, nil)`,
`idC(idp0, [account, at(2)])`. -/
def LId.fmt (i : LId) : String :=
  let seg : Seg → String
    | .field f => f
    | .at k => s!"at({k})"
  let flds := if i.path.isEmpty then "nil" else "[" ++ ", ".intercalate (i.path.map seg) ++ "]"
  s!"idC({idpFmt i.root}, {flds})"

/-- An array operation, as `ppKey` writes it: `push`, `slot(T)`, `pop(keep)`. -/
def AOp.fmt : AOp → String
  | .push => "push"
  | .slot E => s!"slot({E.toStr})"
  | .pop b => s!"pop({b})"

mutual
/-- A term of the target language, in KeY's spelling where KeY has the
symbol (`find`, `delValue`, `if(…) then … else …`); the guards only Lean has
keep Lean's names (`has`, `isMap`, `isFixed`, `ok`, `copyOk`, `orElse`,
`err`), and `(d; a)` is `a` where `d` returns. -/
partial def LTerm.fmt [FreshNames] : LTerm → String
  | .lit v => Value.fmt v
  | .var x => toString x
  | .binop op _ a b => s!"{LTerm.fmtArg a} {BinOp.sym op} {LTerm.fmtArg b}"
  | .unop op _ a => s!"{UnOp.sym op}{LTerm.fmtArg a}"
  | .ite c a b => s!"if({LTerm.fmt c}) then {LTerm.fmtArg a} else {LTerm.fmt b}"
  | .find s q => s!"find({LStor.fmt s}, {LPath.fmt q})"
  | .has s q => s!"has({LStor.fmt s}, {LPath.fmt q})"
  | .kmap sh s q => s!"{KShape.fmt sh}({LStor.fmt s}, {LPath.fmt q})"
  | .len s q => s!"find({LStor.fmt s}, {LPath.fmt q}.length)"
  | .sok s => s!"ok({LStor.fmt s})"
  | .pok q => s!"ok({LPath.fmt q})"
  | t@(.seq ..) =>
    let (gs, v) := LTerm.guards t
    let guard : LTerm → String
      | g@(.ite ..) | g@(.kite ..) => s!"({LTerm.fmt g})"
      | g => LTerm.fmt g
    let gs := (gs.filter (!LTerm.total ·)).map guard |>.eraseDups
    if gs.isEmpty then LTerm.fmt v else s!"({", ".intercalate gs}; {LTerm.fmt v})"
  | .orElse a b => s!"orElse({LTerm.fmt a}, {LTerm.fmt b})"
  | .kite a b t e =>
    s!"if({LTerm.fmt a} = {LTerm.fmt b}) then {LTerm.fmtArg t} else {LTerm.fmt e}"
  | .zero a => s!"delValue({LTerm.fmt a})"
  | .err => "err"
  | .env k => k.toStr
  | .findP s q => s!"findP({LStor.fmt s}, {LPath.fmt q})"
  | .cpok s q => s!"copyOk({LStor.fmt s}, {LPath.fmt q})"

/-- A term as an operand: parenthesised unless it is atomic. -/
partial def LTerm.fmtArg [FreshNames] : LTerm → String
  | t@(.binop ..) | t@(.ite ..) | t@(.kite ..) => s!"({LTerm.fmt t})"
  | t => LTerm.fmt t

/-- A path, the root first: `alice.account.balance`, `balances[k]`. -/
partial def LPath.fmt [FreshNames] : LPath → String
  | .root r => r
  | .field q f => s!"{LPath.fmt q}.{f}"
  | .at q k => s!"{LPath.fmt q}[{LTerm.fmt k}]"

/-- A storage: `storage`, and the writes on top of it, as `ppKey` writes
them (`Calculus/KeyNotation.lean`).  A read written is `select(s, q)`, since
`find` there is a copy, KeY's `save(s, q, find(src, sq))`; a copy of memory
is `save(s, q, copyMem(mtSt, m, i))`; an array operation `arr(op, s, q, w)`
(`push(s, q, w)` for a push); a write through a stale alias `staleSave` or
`stale(op, s, q, w)`, nodes only Lean has (`Calculus/DecideLang.lean`). -/
partial def LStor.fmt [FreshNames] : LStor → String
  | .init => "storage"
  | .save s q w =>
    let w := match w with
      | .find s' q' => s!"select({LStor.fmt s'}, {LPath.fmt q'})"
      | .len s' q' => s!"select({LStor.fmt s'}, {LPath.fmt q'}.length)"
      | w => LTerm.fmt w
    s!"save({LStor.fmt s}, {LPath.fmt q}, {w})"
  | .delAt s q => s!"delAt({LStor.fmt s}, {LPath.fmt q})"
  | .arr .push s q w => s!"push({LStor.fmt s}, {LPath.fmt q}, {LTerm.fmt w})"
  | .arr op s q w => s!"arr({AOp.fmt op}, {LStor.fmt s}, {LPath.fmt q}, {LTerm.fmt w})"
  | .stale none s q w => s!"staleSave({LStor.fmt s}, {LPath.fmt q}, {LTerm.fmt w})"
  | .stale (some op) s q w =>
    s!"stale({AOp.fmt op}, {LStor.fmt s}, {LPath.fmt q}, {LTerm.fmt w})"
  | .copy s q src@(.view ..) (.root r) =>
    if r = viewRoot then s!"save({LStor.fmt s}, {LPath.fmt q}, {LStor.fmt src})"
    else s!"save({LStor.fmt s}, {LPath.fmt q}, find({LStor.fmt src}, {r}))"
  | .copy s q src sq =>
    s!"save({LStor.fmt s}, {LPath.fmt q}, find({LStor.fmt src}, {LPath.fmt sq}))"
  | .view m i => s!"copyMem(mtSt, {LMem.fmt m}, {LId.fmt i})"

/-- A memory: `memory`, and the allocations and writes on top of it, as KeY
writes them.  The `k`-th allocation is `shaped(idpk, T)`, its type in place
of KeY's `#shapeOf`; a `new T[](n)` is the allocation and the write of its
`size`. -/
partial def LMem.fmt [FreshNames] : LMem → String
  | .init => "memory"
  | .addM m k R => s!"addM({LMem.fmt m}, shaped({idpFmt k}, {(Ty.ref R).toStr}))"
  | .newArr m k R n =>
    s!"write(addM({LMem.fmt m}, shaped({idpFmt k}, {(Ty.ref R).toStr})), \
      {LId.fmt ⟨k, []⟩}, size, {LTerm.fmt n})"
  | .copySt m k s q => s!"copySt({LMem.fmt m}, {idpFmt k}, find({LStor.fmt s}, {LPath.fmt q}))"
  | .write m i a v =>
    -- a write of `size` would read as an allocation: `ppKey` escapes it
    let a := match a with | .size => "‹LSel.size›" | a => LSel.fmt a
    s!"write({LMem.fmt m}, {LId.fmt i}, {a}, {LMV.fmt v})"

/-- A selector, as KeY's: a member `f`, an element `at(t)`, the length `size`. -/
partial def LSel.fmt [FreshNames] : LSel → String
  | .fld f => f
  | .idx t => s!"at({LTerm.fmt t})"
  | .size => "size"

/-- A memory value: a word, or a name. -/
partial def LMV.fmt [FreshNames] : LMV → String
  | .word t => LTerm.fmt t
  | .ref i => LId.fmt i
end

/-- A reduced formula: `∧` binds tighter than `→`, which associates to the
right; `=` is KeY's equality, and `∀ uint x; φ` its quantifier. -/
partial def LFml.fmt [FreshNames] : LFml → String
  | .tt => "true"
  | .eq a b => s!"{LTerm.fmtArg a} = {LTerm.fmtArg b}"
  | .not φ => s!"¬{atom φ}"
  | .and φ ψ => s!"{conj φ} ∧ {conj ψ}"
  | .imp φ ψ => s!"{atom' φ} → {LFml.fmt ψ}"
  | .all x p φ => s!"∀ {p.toStr} {x}; {LFml.fmt φ}"
where
  atom : LFml → String
    | φ@(.tt) | φ@(.not _) => LFml.fmt φ
    | φ => s!"({LFml.fmt φ})"
  conj : LFml → String
    | φ@(.imp ..) | φ@(.all ..) => s!"({LFml.fmt φ})"
    | φ => LFml.fmt φ
  atom' : LFml → String
    | φ@(.imp ..) | φ@(.all ..) => s!"({LFml.fmt φ})"
    | φ => LFml.fmt φ


/-! ## The commands -/

variable {C : Contract}

open Lean Elab Command Term Meta

/-- `#wp φ`: what symbolic execution leaves of `φ`, and, in `sol_decide`'s
fragment, its reduction to the initial state. -/
syntax "#wp " term : command

/-- `#step φ`: one step of the strategy on `φ`, and the rule it fires. -/
syntax "#step " term : command

/-- What `#wp` shows of a scoped `φ`: the formula the scoped strategy leaves,
quoted, and the reduction of its erasure when it is in the fragment. -/
def wpQuotedC [FreshNames] (c : Lean.Expr) {Γ : Ctx} (φ : Fml C Γ) :
    Lean.Expr × Option String :=
  let ψ := symex 200 φ
  let ψ' := ψ.erase []
  -- a modality left has no erasure the closer reads (`Fml.erase`)
  (ψ.quote c, if !ψ.active && ψ'.inL Sym.empty then some (LFml.fmt ψ'.reduce) else none)

/-- What `#step` shows of a scoped `φ`: the formula one step leaves, quoted. -/
def stepQuotedC (c : Lean.Expr) {Γ : Ctx} (φ : Fml C Γ) : Option Lean.Expr :=
  φ.step.map (·.quote c)


/-- The rule one step fires on the scoped formula `φ`, by name: at the first
statement with a rule, looking through updates, a precondition, binders and
a conjunction's left goal first, as `Fml.stepAt` looks (`ruleOf?`);
`emptyModality` where the first modality's program is done. -/
partial def ruleAtC? (φ : Lean.Expr) : MetaM (Option Lean.Name) := do
  let k ← mkAppM ``Fml.fresh #[φ]
  let rec go (e : Lean.Expr) : MetaM (Option Lean.Name) := do
    let e ← whnf e
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``Fml.and =>
      match ← go args[2]! with
      | some n => return some n
      | none => go args[3]!
    | some ``Fml.imp => go args[3]!
    | some ``Fml.upd => go args[5]!
    | some ``Fml.havoc => go args[2]!
    | some ``Fml.all => go args[4]!
    | some ``Fml.bind => go args[5]!
    | some ``Fml.anon => go args[3]!
    | some ``Fml.modal =>
      let P ← whnf args[5]!
      if P.isAppOf ``Prog.nil then return some `emptyModality
      unless P.isAppOf ``Prog.cons do return none
      let s := P.getArg! (P.getAppNumArgs - 2)
      let some (c, _) ← ruleOf? k args[4]! s | return none
      return some (← ProofTree.keyName c s)
    | _ => return none
  go φ

/-- `#wp φ`. -/
@[command_elab Solidity.Tools.«command#wp_»]
def elabWpCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | notScoped "#wp"
  let e ← mkAppM ``wpQuotedC #[c, φ]
  let (ψ, red) ← unsafe evalExpr (Lean.Expr × Option String) (← inferType e) e
  let tail := match red with
    | some r => m!"\nupdate-free:\n    {r}"
    | none => m!"\noutside `sol_decide`'s fragment (`NFml.inL`): no reduction"
  logInfo (m!"symbolic execution leaves:\n    {ψ}" ++ tail)

/-- `#step φ`. -/
@[command_elab Solidity.Tools.«command#step_»]
def elabStepCore : CommandElab := fun stx => liftTermElabM do
  let some (φ, c) ← elabCoreFormula? ⟨stx[1]⟩ | notScoped "#step"
  let e ← mkAppM ``stepQuotedC #[c, φ]
  let ψ? ← unsafe evalExpr (Option Lean.Expr) (← inferType e) e
  match ψ? with
  | none => logInfo "no modality left: `close`"
  | some ψ =>
    let r := match ← ruleAtC? φ with
      | some n => toString n
      | none => "?"
    logInfo m!"  ~[{r}]~>\n    {ψ}"

end Solidity.Tools
