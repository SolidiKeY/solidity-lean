import CaseStudies.Velvet.Std

/-!
# Solidity contracts in Velvet

`contract C { … }` reads a Solidity contract, its storage and its functions,
and states each function as a Velvet `method` named `C.f`; `prove_correct
C.f by loom_solve` then proves it, as for a method written by hand. A whole
contract is one page, in Solidity's notation, with its specification beside
it:

```
contract Bank {
  mapping(address => uint) balanceOf;

  function withdraw(uint amount) public
    ensures balanceOf[msg.sender] + amount == old(balanceOf[msg.sender])
  {
    require(amount <= balanceOf[msg.sender]);
    balanceOf[msg.sender] -= amount;
  }
}
```

The reading:

- **Types.** `uint` and `address` are `Nat`, `bool` is `Bool`, `T[]` an
  `Array`, and `mapping(K => V)` a `Mapping K V`: a finite map whose
  unwritten keys read `V`'s default, as Solidity's zero.
- **Storage.** A function takes the storage variables it mentions, as
  Velvet's `mut` parameters when it writes them (`xOld` is the value on
  entry, `old(x)` in a spec), then `msg.sender` (`msgSender`) when it reads
  it, then its own parameters.
- **Reverts.** Solidity ≥ 0.8 reverts on overflow, underflow, a division by
  zero and an index past an array's length, and `require(c)` reverts unless
  `c`. Each becomes Loom's `assume` before the statement that would revert:
  under Velvet's partial correctness a reverting run has no outcome, so an
  `ensures` is about the calls that do not revert, as solc-verify reads it.
- **Specs.** `ensures e` after the signature, `invariant e` after a loop's
  header, over Solidity expressions with `old(e)`, `forall (T x) e` and
  `a ==> b`; any other call `f(a, b)` is the Lean function `f a b`.

Statements are Solidity's: local declarations, `=`, `+=`, `-=`, `*=`,
`x++`, `a.push(v)`, `require`, `if`/`else`, `while`, `for` and `return`
last. A decrement is `x -= 1` (`--` opens a Lean comment).
-/

open Lean Elab Command Term

/-! ## Mappings -/

/-- A Solidity `mapping(K => V)`: the keys written, newest first, each once. -/
structure Mapping (κ α : Type) where
  entries : List (κ × α)

namespace Mapping

variable {κ α : Type}

instance : Inhabited (Mapping κ α) := ⟨⟨[]⟩⟩

/-- The value at `k`, `default` when it was never written. -/
def lookup [DecidableEq κ] [Inhabited α] : List (κ × α) → κ → α
  | [], _ => default
  | (k', v) :: r, k => if k' = k then v else lookup r k

def get [DecidableEq κ] [Inhabited α] (m : Mapping κ α) (k : κ) : α := lookup m.entries k

/-- The entries without key `k`. -/
def erase [DecidableEq κ] : List (κ × α) → κ → List (κ × α)
  | [], _ => []
  | (k', v) :: r, k => if k' = k then erase r k else (k', v) :: erase r k

def set [DecidableEq κ] (m : Mapping κ α) (k : κ) (v : α) : Mapping κ α :=
  ⟨(k, v) :: erase m.entries k⟩

def ofList [DecidableEq κ] (l : List (κ × α)) : Mapping κ α :=
  l.foldr (fun (k, v) m => m.set k v) default

theorem lookup_erase [DecidableEq κ] [Inhabited α] (l : List (κ × α)) {k k' : κ}
    (h : k' ≠ k) : lookup (erase l k) k' = lookup l k' := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨a, v⟩ := p
    by_cases ha : a = k
    · subst ha
      have : a ≠ k' := fun e => h e.symm
      simp only [erase, lookup, if_pos, if_neg this, ih]
    · simp only [erase, lookup, if_neg ha, ih]

@[simp, grind =] theorem get_set [DecidableEq κ] [Inhabited α] (m : Mapping κ α) (k k' : κ)
    (v : α) : (m.set k v).get k' = if k' = k then v else m.get k' := by
  by_cases h : k' = k
  · subst h; simp only [get, set, lookup, if_pos]
  · have : k ≠ k' := fun e => h e.symm
    simp only [get, set, lookup, if_neg h, if_neg this, lookup_erase _ h]

instance [Repr κ] [Repr α] : Repr (Mapping κ α) where
  reprPrec m _ := "Mapping.ofList " ++ repr m.entries

end Mapping

/-! ## The grammar -/

declare_syntax_cat solTy
declare_syntax_cat solExpr
declare_syntax_cat solStmt
declare_syntax_cat solStep
declare_syntax_cat solParam
declare_syntax_cat solInv
declare_syntax_cat solSpec
declare_syntax_cat solMember
declare_syntax_cat solMod

syntax ident : solTy
syntax "mapping" "(" solTy " => " solTy ")" : solTy
syntax solTy noWs "[" "]" : solTy

syntax num : solExpr
syntax ident : solExpr
syntax "(" solExpr ")" : solExpr
syntax:max solExpr noWs "[" solExpr "]" : solExpr
syntax:max ident noWs "(" solExpr,* ")" : solExpr
syntax:max solExpr noWs "." ident : solExpr
syntax:80 "!" solExpr:80 : solExpr
syntax:75 solExpr:76 " ** " solExpr:75 : solExpr
syntax:70 solExpr:70 " * " solExpr:71 : solExpr
syntax:70 solExpr:70 " / " solExpr:71 : solExpr
syntax:70 solExpr:70 " % " solExpr:71 : solExpr
syntax:65 solExpr:65 " + " solExpr:66 : solExpr
syntax:65 solExpr:65 " - " solExpr:66 : solExpr
syntax:50 solExpr:51 " < " solExpr:51 : solExpr
syntax:50 solExpr:51 " <= " solExpr:51 : solExpr
syntax:50 solExpr:51 " > " solExpr:51 : solExpr
syntax:50 solExpr:51 " >= " solExpr:51 : solExpr
syntax:45 solExpr:46 " == " solExpr:46 : solExpr
syntax:45 solExpr:46 " != " solExpr:46 : solExpr
syntax:35 solExpr:35 " && " solExpr:36 : solExpr
syntax:30 solExpr:30 " || " solExpr:31 : solExpr
syntax:25 solExpr:26 " ==> " solExpr:25 : solExpr
syntax:20 "forall" "(" solTy ident ")" solExpr:20 : solExpr

syntax "invariant " solExpr : solInv
syntax "ensures " solExpr : solSpec

syntax solExpr "++" : solStep
syntax solExpr " += " solExpr : solStep
syntax solExpr " = " solExpr : solStep

syntax "{" solStmt* "}" : solStmt
syntax solTy ident (" = " solExpr)? ";" : solStmt
syntax solExpr " = " solExpr ";" : solStmt
syntax solExpr " += " solExpr ";" : solStmt
syntax solExpr " -= " solExpr ";" : solStmt
syntax solExpr " *= " solExpr ";" : solStmt
syntax solExpr "++" ";" : solStmt
syntax solExpr ";" : solStmt
syntax "require" "(" solExpr ")" ";" : solStmt
syntax "if " "(" solExpr ")" solStmt (" else " solStmt)? : solStmt
syntax "while " "(" solExpr ")" solInv* solStmt : solStmt
syntax "for " "(" solStmt solExpr ";" solStep ")" solInv* solStmt : solStmt
syntax "return" (solExpr)? ";" : solStmt

syntax solTy (ident)? : solParam

syntax ident : solMod
syntax "public" : solMod
syntax "private" : solMod

syntax solTy ident ";" : solMember
syntax "function " ident "(" solParam,* ")" solMod*
  (" returns " "(" solParam ")")? solSpec* "{" solStmt* "}" : solMember

/-- `contract C { storage and functions }`: one Velvet `method` `C.f` for
each function `f`, proved by `prove_correct C.f by loom_solve`. -/
syntax "contract " ident "{" solMember* "}" : command

/-! ## The reading -/

namespace SolidityVelvet

inductive SolTy where
  | uint | address | bool
  | array (t : SolTy)
  | mapping (k v : SolTy)
  deriving Inhabited, BEq

partial def SolTy.ofSyntax : TSyntax `solTy → CommandElabM SolTy
  | `(solTy| $id:ident) => match id.getId with
    | `uint | `uint256 => pure .uint
    | `address => pure .address
    | `bool => pure .bool
    | _ => throwErrorAt id "unsupported Solidity type {id}"
  | `(solTy| mapping($k => $v)) => return .mapping (← ofSyntax k) (← ofSyntax v)
  | `(solTy| $t[]) => return .array (← ofSyntax t)
  | stx => throwErrorAt stx "unsupported Solidity type"

partial def SolTy.toTerm : SolTy → CommandElabM Term
  | .uint | .address => `(Nat)
  | .bool => `(Bool)
  | .array t => do `(Array $(← t.toTerm))
  | .mapping k v => do `(Mapping $(← k.toTerm) $(← v.toTerm))

/-- What an expression is read in: the variables' types, the storage the
function writes, and whether the reading is inside `old(…)`. -/
structure Ctx where
  vars : List (Name × SolTy)
  muts : List Name
  inOld : Bool := false

def Ctx.push (c : Ctx) (x : Name) (t : SolTy) : Ctx := { c with vars := (x, t) :: c.vars }

def Ctx.lookup (c : Ctx) (x : Name) : Option SolTy := c.vars.lookup x

/-- The Lean name a Solidity variable is read at, placed at `ref`. -/
def Ctx.ident (c : Ctx) (ref : Syntax) (x : Name) : Ident :=
  if x == `msg.sender then mkIdentFrom ref `msgSender (canonical := true)
  else if c.inOld && c.muts.contains x then mkIdentFrom ref (x.appendAfter "Old") (canonical := true)
  else mkIdentFrom ref x (canonical := true)

/-- The container type of an indexed or named expression. -/
partial def tyOf (c : Ctx) : TSyntax `solExpr → Option SolTy
  | `(solExpr| $x:ident) => c.lookup x.getId
  | `(solExpr| ($e)) => tyOf c e
  | `(solExpr| $a[$_]) => match tyOf c a with
    | some (.array t) => some t
    | some (.mapping _ v) => some v
    | _ => none
  | _ => none

/-- The conditions under which an expression's evaluation reverts, as the
guards it does not revert under. -/
abbrev TrM := StateT (Array Term) CommandElabM

/-- Record a guard, once. -/
def guard (g : Term) : TrM Unit :=
  modify fun gs => if gs.any (·.raw.structEq g) then gs else gs.push g

/-- Translate `e`, keeping its guards apart; `k` weakens each one. -/
def guarded (m : TrM Term) (k : Term → CommandElabM Term) : TrM Term := do
  let (t, gs) ← (m.run #[] : CommandElabM _)
  for g in gs do guard (← k g)
  return t

/-- A guard that the left operand of `&&` already implies, as the bound
`i < a.length` of `i < a.length && a[i] != x`, is dropped. -/
def guardedBy (a : Term) (m : TrM Term) (k : Term → CommandElabM Term) : TrM Term := do
  let (t, gs) ← (m.run #[] : CommandElabM _)
  for g in gs do
    unless g.raw.structEq a do guard (← k g)
  return t

mutual

partial def trExpr (c : Ctx) (e : TSyntax `solExpr) : TrM Term := do
  match e with
  | `(solExpr| $n:num) => `($n:num)
  | `(solExpr| $x:ident) =>
    let n := x.getId
    match n with
    | .str p "length" =>
      if let some (.array _) := c.lookup p then
        let a := c.ident x p
        return ← `(Array.size $a)
      else return c.ident x n
    | _ => return c.ident x n
  | `(solExpr| ($e)) => do `(($(← trExpr c e)))
  | `(solExpr| $a[$i]) => do
    let ta ← trExpr c a
    let ti ← trExpr c i
    match tyOf c a with
    | some (.array _) =>
      guard (← `($ti < Array.size $ta))
      `($ta[$ti]!)
    | some (.mapping _ _) => `(Mapping.get $ta $ti)
    | _ => throwErrorAt a "cannot index this expression: its type is not an array or mapping"
  | `(solExpr| $f:ident($args,*)) => do
    if f.getId == `old then
      let #[a] := args.getElems | throwErrorAt e "`old` takes one argument"
      return ← trExpr { c with inOld := true } a
    let targs ← args.getElems.mapM (trExpr c)
    return Syntax.mkApp f targs
  | `(solExpr| $a.$f:ident) => do
    unless f.getId == `length do throwErrorAt f "unsupported member {f}"
    `(Array.size $(← trExpr c a))
  | `(solExpr| !$a) => do `(¬ $(← trExpr c a))
  | `(solExpr| $a ** $b) => do arith (← `($(← trExpr c a) ^ $(← trExpr c b)))
  | `(solExpr| $a * $b) => do arith (← `($(← trExpr c a) * $(← trExpr c b)))
  | `(solExpr| $a + $b) => do arith (← `($(← trExpr c a) + $(← trExpr c b)))
  | `(solExpr| $a - $b) => do
    let ta ← trExpr c a
    let tb ← trExpr c b
    guard (← `($tb ≤ $ta))
    `($ta - $tb)
  | `(solExpr| $a / $b) => do
    let ta ← trExpr c a
    let tb ← trExpr c b
    guard (← `($tb ≠ 0))
    `($ta / $tb)
  | `(solExpr| $a % $b) => do
    let ta ← trExpr c a
    let tb ← trExpr c b
    guard (← `($tb ≠ 0))
    `($ta % $tb)
  | `(solExpr| $a < $b) => do `($(← trExpr c a) < $(← trExpr c b))
  | `(solExpr| $a <= $b) => do `($(← trExpr c a) ≤ $(← trExpr c b))
  | `(solExpr| $a > $b) => do `($(← trExpr c a) > $(← trExpr c b))
  | `(solExpr| $a >= $b) => do `($(← trExpr c a) ≥ $(← trExpr c b))
  | `(solExpr| $a == $b) => do `($(← trExpr c a) = $(← trExpr c b))
  | `(solExpr| $a != $b) => do `($(← trExpr c a) ≠ $(← trExpr c b))
  | `(solExpr| $a && $b) => do
    let ta ← trExpr c a
    let tb ← guardedBy ta (trExpr c b) fun g => `($ta → $g)
    `($ta ∧ $tb)
  | `(solExpr| $a || $b) => do
    let ta ← trExpr c a
    let tb ← guarded (trExpr c b) fun g => `(¬ $ta → $g)
    `($ta ∨ $tb)
  | `(solExpr| $a ==> $b) => do
    let ta ← trExpr c a
    let tb ← guarded (trExpr c b) fun g => `($ta → $g)
    `($ta → $tb)
  | `(solExpr| forall ($t $x) $b) => do
    let ty ← SolTy.ofSyntax t
    let tb ← trExpr (c.push x.getId ty) b
    -- Canonical, as the reads of it are, so the linter sees them use it.
    let x := mkIdentFrom x x.getId (canonical := true)
    `(∀ $x:ident : $(← ty.toTerm), $tb)
  | _ => throwErrorAt e "unsupported Solidity expression"

/-- A `uint` result past `2^256 - 1` reverts (checked arithmetic). -/
partial def arith (t : Term) : TrM Term := do
  guard (← `($t < 2 ^ 256))
  return t

end

/-- A specification: an expression whose guards are dropped (`a[i]` reads
`a[i]!`). -/
def trSpec (c : Ctx) (e : TSyntax `solExpr) : CommandElabM Term :=
  Prod.fst <$> (trExpr c e).run #[]

abbrev Item := TSyntax ``Lean.Parser.Term.doSeqItem

def assumes (gs : Array Term) : CommandElabM (Array Item) :=
  gs.mapM fun g => `(Lean.Parser.Term.doSeqItem| MonadNonDet.assume ($g))

/-- An expression and the `assume`s that its evaluation does not revert. -/
def trCode (c : Ctx) (e : TSyntax `solExpr) : CommandElabM (Term × Array Item) := do
  let (t, gs) ← (trExpr c e).run #[]
  return (t, ← assumes gs)

/-- `lhs := v`, writing through indices: `a[i] = v` is `a := a.set i v`. -/
partial def assign (c : Ctx) (lhs : TSyntax `solExpr) (v : Term) : TrM (Array Item) := do
  match lhs with
  | `(solExpr| $x:ident) =>
    return #[← `(Lean.Parser.Term.doSeqItem| $(mkIdent x.getId):ident := $v)]
  | `(solExpr| ($e)) => assign c e v
  | `(solExpr| $a[$i]) =>
    let ta ← trExpr c a
    let ti ← trExpr c i
    match tyOf c a with
    | some (.array _) =>
      guard (← `($ti < Array.size $ta))
      assign c a (← `(Array.set! $ta $ti $v))
    | some (.mapping _ _) => assign c a (← `(Mapping.set $ta $ti $v))
    | _ => throwErrorAt a "cannot index this expression: its type is not an array or mapping"
  | _ => throwErrorAt lhs "not an assignable expression"

/-- `lhs = rhs`, after the guards of both sides. -/
def trAssign (c : Ctx) (lhs rhs : TSyntax `solExpr) : CommandElabM (Array Item) := do
  let ((items, _), gs) ← (do
    let v ← trExpr c rhs
    let items ← assign c lhs v
    return (items, ())).run #[]
  return (← assumes gs) ++ items

/-- The right operand of a compound assignment, in parentheses unless atomic. -/
def operand (r : TSyntax `solExpr) : CommandElabM (TSyntax `solExpr) :=
  match r with
  | `(solExpr| $_:ident) | `(solExpr| $_:num) | `(solExpr| ($_)) | `(solExpr| $_[$_]) => pure r
  | _ => `(solExpr| ($r))

def pureUnit : CommandElabM Item := `(Lean.Parser.Term.doSeqItem| pure ())

mutual

partial def trStmt (c : Ctx) (s : TSyntax `solStmt) : CommandElabM (Ctx × Array Item) := do
  match s with
  | `(solStmt| { $ss* }) => do
    let (_, items) ← trStmts c ss
    return (c, items)
  | `(solStmt| $t:solTy $x:ident $[= $e]? ;) => do
    let ty ← SolTy.ofSyntax t
    let lt ← ty.toTerm
    let (v, gs) ← match e with
      | some e => trCode c e
      | none => do pure (← `((default : $lt)), #[])
    let item ← `(Lean.Parser.Term.doSeqItem| let mut $(mkIdent x.getId):ident : $lt := $v)
    return (c.push x.getId ty, gs.push item)
  | `(solStmt| $l:solExpr = $r:solExpr ;) => return (c, ← trAssign c l r)
  | `(solStmt| $l:solExpr += $r:solExpr ;) => return (c, ← trAssign c l (← `(solExpr| $l + $(← operand r))))
  | `(solStmt| $l:solExpr -= $r:solExpr ;) => return (c, ← trAssign c l (← `(solExpr| $l - $(← operand r))))
  | `(solStmt| $l:solExpr *= $r:solExpr ;) => return (c, ← trAssign c l (← `(solExpr| $l * $(← operand r))))
  | `(solStmt| $l:solExpr ++ ;) => return (c, ← trAssign c l (← `(solExpr| $l + 1)))
  | `(solStmt| $f:ident($args,*) ;) => do
    let .str p "push" := f.getId | throwErrorAt f "unsupported call statement"
    let #[a] := args.getElems | throwErrorAt s "`push` takes one argument"
    let some (.array _) := c.lookup p | throwErrorAt f "`push` on a non-array"
    let (v, gs) ← trCode c a
    let x := mkIdent p
    return (c, gs.push (← `(Lean.Parser.Term.doSeqItem| $x:ident := Array.push $x $v)))
  | `(solStmt| require($e);) => do
    let (t, gs) ← trCode c e
    return (c, gs ++ (← assumes #[t]))
  | `(solStmt| if ($e) $thn:solStmt $[else $els:solStmt]?) => do
    let (t, gs) ← trCode c e
    let (_, ti) ← trStmt c thn
    let ti ← if ti.isEmpty then pure #[← pureUnit] else pure ti
    let ei ← match els with
      | some els => do
        let (_, ei) ← trStmt c els
        if ei.isEmpty then pure #[← pureUnit] else pure ei
      | none => pure #[← pureUnit]
    return (c, gs.push (← `(Lean.Parser.Term.doSeqItem| if $t then $ti* else $ei*)))
  | `(solStmt| while ($e) $invs:solInv* $body:solStmt) => do
    let (_, items) ← trLoop c e invs body #[]
    return (c, items)
  | `(solStmt| for ($init:solStmt $e:solExpr; $step:solStep) $invs:solInv* $body:solStmt) => do
    let (c', ii) ← trStmt c init
    let si ← match step with
      | `(solStep| $l:solExpr ++) => trAssign c' l (← `(solExpr| $l + 1))
      | `(solStep| $l:solExpr += $r:solExpr) => trAssign c' l (← `(solExpr| $l + $(← operand r)))
      | `(solStep| $l:solExpr = $r:solExpr) => trAssign c' l r
      | _ => throwErrorAt step "unsupported loop step"
    let (_, items) ← trLoop c' e invs body si
    return (c', ii ++ items)
  | `(solStmt| return $[$e:solExpr]? ;) => do
    match e with
    | some e => do
      let (t, gs) ← trCode c e
      return (c, gs.push (← `(Lean.Parser.Term.doSeqItem| return $t)))
    | none => return (c, #[← `(Lean.Parser.Term.doSeqItem| return)])
  | _ => throwErrorAt s "unsupported Solidity statement"

/-- `while (e) inv* body`, then `step`: the guards of `e` before the loop and
after each iteration, where `e` is evaluated again. -/
partial def trLoop (c : Ctx) (e : TSyntax `solExpr) (invs : Array (TSyntax `solInv))
    (body : TSyntax `solStmt) (step : Array Item) : CommandElabM (Ctx × Array Item) := do
  let (t, gs) ← trCode c e
  let invs ← invs.mapM fun
    | `(solInv| invariant $i) => trSpec c i
    | i => throwErrorAt i "unsupported invariant"
  let (_, bi) ← trStmt c body
  let bi := bi ++ step ++ gs
  let bi ← if bi.isEmpty then pure #[← pureUnit] else pure bi
  let loop ← `(Lean.Parser.Term.doSeqItem| while $t $[invariant $invs]* do $bi*)
  return (c, gs.push loop)

partial def trStmts (c : Ctx) (ss : Array (TSyntax `solStmt)) : CommandElabM (Ctx × Array Item) := do
  let mut c := c
  let mut items := #[]
  for s in ss do
    let (c', is) ← trStmt c s
    c := c'
    items := items ++ is
  return (c, items)

end

/-- Every identifier's first component, `msg.sender` whole. -/
partial def roots (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => if n == `msg.sender then #[n] else #[n.getRoot]
  | .node _ _ args => args.flatMap roots
  | _ => #[]

/-- The variables a statement writes: the roots of its left-hand sides and
of its `push`es. -/
partial def written (s : TSyntax `solStmt) : Array Name :=
  let lhsRoot (l : Syntax) : Array Name := (roots l).extract 0 1
  match s with
  | `(solStmt| { $ss* }) => ss.flatMap written
  | `(solStmt| $l:solExpr = $_:solExpr ;) | `(solStmt| $l:solExpr += $_:solExpr ;) | `(solStmt| $l:solExpr -= $_:solExpr ;)
  | `(solStmt| $l:solExpr *= $_:solExpr ;) | `(solStmt| $l:solExpr ++ ;) => lhsRoot l
  | `(solStmt| $f:ident($_,*) ;) => #[f.getId.getRoot]
  | `(solStmt| if ($_) $thn:solStmt $[else $els:solStmt]?) => written thn ++ (els.map written).getD #[]
  | `(solStmt| while ($_) $_:solInv* $body:solStmt) => written body
  | `(solStmt| for ($init:solStmt $_:solExpr; $step:solStep) $_:solInv* $body:solStmt) =>
    written init ++ written body ++ (match step with
      | `(solStep| $l:solExpr ++) | `(solStep| $l:solExpr += $_:solExpr) | `(solStep| $l:solExpr = $_:solExpr) => lhsRoot l
      | _ => #[])
  | _ => #[]

def param (p : TSyntax `solParam) : CommandElabM (Option Name × SolTy) := do
  match p with
  | `(solParam| $t:solTy $[$x]?) => return (x.map (·.getId), ← SolTy.ofSyntax t)
  | _ => throwErrorAt p "unsupported parameter"

/-- One function, as the `method` command that states it. -/
def trFunction (cname : Name) (storage : List (Name × SolTy)) (f : Ident)
    (params : Array (TSyntax `solParam)) (mods : Array (TSyntax `solMod)) (ret? : Option (TSyntax `solParam))
    (specs : Array (TSyntax `solSpec)) (body : Array (TSyntax `solStmt)) : CommandElabM Syntax := do
  let all := roots (mkNullNode (body.map (·.raw) ++ specs.map (·.raw)))
  let wrote := body.flatMap written
  let used := storage.filter fun (x, _) => all.contains x
  let muts := used.filter (wrote.contains ·.1) |>.map (·.1)
  let isView := mods.any fun
    | `(solMod| $m:ident) => m.getId == `view || m.getId == `pure
    | _ => false
  if isView && !muts.isEmpty then
    throwErrorAt f "a `view` function writes storage: {muts}"
  let ps ← params.mapM fun p => do
    let (some x, t) ← param p | throwErrorAt p "a parameter needs a name"
    pure (x, t)
  let (retName, retTy) ← match ret? with
    | some r => do
      let (x?, t) ← param r
      pure (x?.getD `result, some t)
    | none => pure (`u, none)
  let mut binders : Array (TSyntax `leafny_binder) := #[]
  for (x, t) in used do
    let lt ← t.toTerm
    binders := binders.push <| ←
      if muts.contains x then `(leafny_binder| (mut $(mkIdent x):ident : $lt))
      else `(leafny_binder| ($(mkIdent x):ident : $lt))
  if all.contains `msg.sender then
    binders := binders.push (← `(leafny_binder| ($(mkIdent `msgSender):ident : Nat)))
  for (x, t) in ps do
    binders := binders.push (← `(leafny_binder| ($(mkIdent x):ident : $(← t.toTerm))))
  let mut c : Ctx := { vars := ps.toList.reverse ++ used, muts }
  if let some t := retTy then c := c.push retName t
  let specTerms ← specs.mapM fun
    | `(solSpec| ensures $e) => trSpec c e
    | s => throwErrorAt s "unsupported specification"
  -- Parameters a body assigns are locals of their own; a named return starts at its zero.
  let mut prelude : Array Item := #[]
  for (x, _) in ps do
    if wrote.contains x then
      prelude := prelude.push (← `(Lean.Parser.Term.doSeqItem| let mut $(mkIdent x):ident := $(mkIdent x)))
  let retLean ← match retTy with
    | some t => t.toTerm
    | none => `(Unit)
  if let some t := retTy then
    if ret?.any (fun r => match r with | `(solParam| $_:solTy $_:ident) => true | _ => false) then
      prelude := prelude.push (← `(Lean.Parser.Term.doSeqItem|
        let mut $(mkIdent retName):ident : $(← t.toTerm) := default))
  let (_, items) ← trStmts c body
  let endsInReturn := match body.back? with
    | some s => match s with | `(solStmt| return $[$_:solExpr]? ;) => true | _ => false
    | none => false
  let tail ← if endsInReturn then pure #[]
    else if retTy.isSome then pure #[← `(Lean.Parser.Term.doSeqItem| return $(mkIdent retName):ident)]
    else pure #[← `(Lean.Parser.Term.doSeqItem| return)]
  let items := prelude ++ items ++ tail
  let name := mkIdent (cname ++ f.getId)
  `(command| method $name $binders* return ($(mkIdent retName) : $retLean) $[ensures $specTerms]*
      do $items*)

elab_rules : command
  | `(command| contract $c:ident { $members* }) => do
    let mut storage : List (Name × SolTy) := []
    for m in members do
      match m with
      | `(solMember| $t:solTy $x:ident ;) => storage := storage ++ [(x.getId, ← SolTy.ofSyntax t)]
      | `(solMember| function $f:ident ($ps,*) $mods:solMod* $[returns ($r)]? $specs:solSpec* { $body* }) =>
        let cmd ← withRef m <| trFunction c.getId storage f ps.getElems mods r specs body
        withRef m <| elabCommand cmd
      | _ => throwErrorAt m "unsupported contract member"

end SolidityVelvet
