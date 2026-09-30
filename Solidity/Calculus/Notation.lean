import Solidity.Calculus.Symex

/-!
# Reading concrete formulas: `dl[C]{ φ }`

`dl{ φ }` (`RuleSyntax.lean`) reads a *schema*: every name is a Lean
variable, and its spelling says what it stands for.  A formula about one
contract needs the other reading, mini-solkey's `dl[C]{ φ }`: `alice` is a
state variable because `C` declares it, `x` is a local because a program
declared it, and a program inside the formula elaborates as `sol[C]{ … }`
would, with the locals the formula has bound so far.  The two readings
cannot share a spelling — `dl{ φ }` already means the schema, and the taclet
table is written in it — so the formula of the file's `InContract` is
`dl!{ φ }`, as `sol_raw!{ … }` sits beside `sol{ … }`.

The printers do not change: a formula prints as `dl{ φ }`, and the `φ` it
shows reads back through `dl[C]{ φ }` (or `dl!{ φ }`) as the formula it is —
at its modality, `dl![m]{ φ }`, when it has `⟨[ ]⟩` or is a box's: an update
prints `{U} ψ` whatever the modality it is judged at.  The reading is
mini-solkey's: the macros build a raw formula, `elabDl` resolves its names
at compile time (`elabAgainst`, as `sol[C]{ … }` does), and `Fml.quote`
(`Quote.lean`) splices the result.

**Lean terms in a formula.**  `dl![m]{ φ }` (`dl[C, m]{ φ }`) reads `φ` at
the modality `m`, a Lean term — a variable, `.box`, `.diamond`: `⟨[ P ]⟩ ψ`
is `P` under `m`, and an update with no modality under
it is judged at `m`, so the last line of a box derivation is
`dl![.box]{ { x := 1 } x == 1 }`.  In `dl!{ φ }` such an update is judged at
the diamond, and `⟨[ ]⟩` is refused.  A name where a formula stands, or
`‹t›`, is a Lean formula: the postcondition `φ` (a `Post C`,
`Chains.lean`), which prints back as its name.  The reader runs as compiled
code, which no Lean variable can enter, so each of these stands in for
something closed while the formula is read, and one walk (`fillSlots`) puts
the Lean terms back: a formula is read as a slot (`Fml.slot`), and the
modality as the difference between two readings, one at the diamond and one
at the box — the reading never looks at a modality, so they differ exactly
where `m` goes.

**Two equations.**  `a = b` here is the interpreter's equation, `Fml.eqD`:
both sides return, with one value — what `==` means, and what `a = b`
meant before `holds` read an equation in the Theory.  `a ≐ b` is the total
one, `Fml.eq` (KeY's `=`, which a taclet writes as `=` in `dl{ … }`): it
compares what the sides denote, and may hold of sides that halt.
`defined(t)` says `t` returns.  The printer follows: `Fml.eqD` prints as `=`
(a comparison `a < b` as itself), `Fml.eq` as `≐`.

What a name is:

* a program reads and writes it as `sol[C]{ … }` does; `==` and `!=`
  compare program expressions, typed like the operands of Solidity's `==`
  and lowered with `Val.lower`;
* in a term (either side of `=`, an update) the position decides the sort,
  since terms are untyped: a state variable is a root, anything else a
  program variable (`pv`); a bare state variable in a value position is
  `select(storage, r)`, a bare path `find(storage, p)`;
* a name no program in the formula declares is a **parameter**, in scope
  everywhere: a `uint` local (mini-solkey's reading of a free name), or an
  alias when a program binds it to a storage path (`p = alice;`, which is
  what symbolic execution leaves of `Person storage p = alice;`).  A name
  some program declares is no parameter anywhere in the formula: outside
  that declaration's scope it is unknown (`checkFresh` would refuse the
  declaration of a parameter), so a free name and a declared one differ;
* `x := p` in an update, for a path `p` of reference type, binds `x` as an
  alias of that type for the formula under it; `sp1`, `mv1` (`FreshNames`)
  are an alias and a memory local wherever nothing else says otherwise.

What does not read back: `‹…›` in a term or an update (a Lean term, which is also how a
conditional and an operator other than `+`, `-` print), the operator schema variables
`⊕ ⊖ ± ⊕⊕` (taclets only), and the terms whose printing drops a type —
`freshId(addM(m))`, `addM(m)`, `newArr(n)`, `defVal(T)` for a non-primitive `T`.  A
concrete `defVal(uint)` reads as the default value itself.
-/

namespace Solidity

open Semantics

/-! ## Raw formulas -/

/-- A term as written: names are strings, the head of `f(…)` too. -/
inductive RawTerm where
  | num (n : Nat)
  | name (x : String)
  | field (t : RawTerm) (f : String)
  | at (t i : RawTerm)
  | add (a b : RawTerm)
  | sub (a b : RawTerm)
  | app (f : String) (args : List RawTerm)
  /-- `msg.sender`, `address(this).balance`, …: KeY's program variables
  `msgSender`, `selfBalance`, …. -/
  | env (k : EnvKey)
  deriving Repr, Inhabited

/-- One elementary update as written. -/
inductive RawUpdElem where
  | assign (x : String) (t : RawTerm)
  /-- `selfBalance := selfBalance ± a` -/
  | selfBalance (op : IntOp) (a : RawTerm)
  /-- `net := store(net, at(r), net(r) ± a)` -/
  | net (r : RawTerm) (op : IntOp) (a : RawTerm)
  deriving Repr, Inhabited

/-- A formula as written.  `peq`/`pne` compare program expressions (`==`, `!=`). -/
inductive RawFml where
  | tt
  /-- `a = b`: both sides return, with one value (`Fml.eqD`). -/
  | eq (a b : RawTerm)
  /-- `a ≐ b`: the total equation (`Fml.eq`). -/
  | teq (a b : RawTerm)
  /-- `defined(t)` -/
  | defined (t : RawTerm)
  | peq (a b : RawExpr)
  | pne (a b : RawExpr)
  /-- `a < b`, `a <= b`, `a > b`, `a >= b`: terms, compared as `uint`s
  (as `+` and `-` add them). -/
  | cmp (op : BinOp) (a b : RawTerm)
  /-- `∀ uint x; φ` -/
  | all (p : PrimTy) (x : String) (φ : RawFml)
  | not (φ : RawFml)
  | and (φ ψ : RawFml)
  | imp (φ ψ : RawFml)
  /-- `{U} φ`, under the modality of the goal it came from (`fmlModality?`),
  else the formula's. -/
  | upd (m : Modality) (U : List RawUpdElem) (φ : RawFml)
  | modal (m : Modality) (P : List RawStmt) (φ : RawFml)
  /-- `φ` or `‹t›` where a formula stands: the formula's `i`th Lean formula,
  read as `Fml.slot i` and put back after (`fillSlots`). -/
  | lean (i : Nat)
  deriving Repr, Inhabited

/-! ## Chain-only spellings

Three spellings that the schema reading (`dl{ … }`) has no use
for, so they are `dl[C]{ … }`'s alone:

* a sequent line `Γ ⟹ φ`, the formula `a₁ → … → φ`: at the top of a line
  (`dl!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ φ }`) or in parentheses, so
  that the two goals of a split are `(c ⟹ ψ₁) ∧ (¬c ⟹ ψ₂)`.  A goal of a
  `⊢` derivation (`dl{ Γ ⟹ φ }`, a `Proves`) is the other reading of the
  arrow, with its context apart; a line is one formula, and prints with `→`;
* `a <= b <= c`, as in `0 ≤ se ≤ selfBalance`: `a <= b ∧ b <= c`;
* `select(net, at(r))`, the read of the ledger: `net(r)`, KeY's
  (`netHeader.key`), which is how it prints. -/

/-- A sequent where a formula stands: `(Γ ⟹ φ)`, the formula `a₁ → … → φ`. -/
syntax:max "(" sepBy1(dl_fml, ", ") " ⟹ " dl_fml ")" : dl_fml

/-- `a <= b <= c`: `a <= b ∧ b <= c`. -/
syntax:55 dl_term:56 " <= " dl_term:56 " <= " dl_term:56 : dl_fml

section Expand
open Lean

def noEscape (stx : Syntax) : MacroM α :=
  Macro.throwErrorAt stx "`‹…›` is a Lean term: `dl[C]{ … }` reads a formula written out"

def schemaOnly (stx : Syntax) : MacroM α :=
  Macro.throwErrorAt stx "an operator schema variable (`⊕`, `⊖`, `±`, `⊕⊕`) belongs to a taclet"

/-- `address(this).balance`, which reads as the application `address(this)`
and a member. -/
def isSelfBalance (t : TSyntax `dl_term) (f : Ident) : Bool :=
  match t with
  | `(dl_term| $h:ident($as,*)) =>
    h.getId.toString == "address" && f.getId.toString == "balance" &&
      match as.getElems.toList with
      | [a] => match a with
        | `(dl_term| $x:ident) => x.getId.toString == "this"
        | _ => false
      | _ => false
  | _ => false

partial def expandTerm : TSyntax `dl_term → MacroM Lean.Term
  | `(dl_term| $n:num) => `(RawTerm.num $n)
  | `(dl_term| $x:ident) => do
      let root :: flds := nameParts x.getId | Macro.throwError "empty identifier"
      let (base, flds) ← match flds with
        | f :: flds' => match EnvKey.ofParts root f with
          | some k => pure (← `(RawTerm.env $(k.ident)), flds')
          | none => pure (← `(RawTerm.name $(quote root)), flds)
        | [] =>
          if root == "selfBalance" then pure (← `(RawTerm.env EnvKey.selfBalance), flds)
          else pure (← `(RawTerm.name $(quote root)), flds)
      flds.foldlM (init := base) fun acc f =>
        `(RawTerm.field $acc $(quote f))
  | `(dl_term| $t:dl_term . $f:ident) => do
      if isSelfBalance t f then return ← `(RawTerm.env EnvKey.selfBalance)
      (nameParts f.getId).foldlM (init := ← expandTerm t) fun acc c =>
        `(RawTerm.field $acc $(quote c))
  | `(dl_term| $t:dl_term [ $i:dl_term ]) => do `(RawTerm.at $(← expandTerm t) $(← expandTerm i))
  | `(dl_term| $a:dl_term + $b:dl_term) => do `(RawTerm.add $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| $a:dl_term - $b:dl_term) => do `(RawTerm.sub $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| ( $t:dl_term )) => expandTerm t
  | `(dl_term| ! $t:dl_term) => do `(RawTerm.app "!" [$(← expandTerm t)])
  | `(dl_term| select(net, at($a))) => do `(RawTerm.app "net" [$(← expandTerm a)])
  | `(dl_term| $f:ident($args,*)) => do
      `(RawTerm.app $(quote f.getId.toString) [$(← args.getElems.mapM expandTerm),*])
  | stx@`(dl_term| ‹ $_:term ›) => noEscape stx
  | stx@`(dl_term| $_:dl_term ⊕ $_:dl_term) | stx@`(dl_term| ⊖ $_:dl_term)
  | stx@`(dl_term| $_:dl_term ± $_:dl_term) | stx@`(dl_term| $_:dl_term ⊕⊕) => schemaOnly stx
  | _ => Macro.throwUnsupported

/-- An operand of `==`: a program expression. -/
partial def expandOperand : TSyntax `dl_term → MacroM Lean.Term
  | `(dl_term| $n:num) => `(RawExpr.num $n)
  | `(dl_term| $x:ident) => expandIdent x
  | `(dl_term| $t:dl_term . $f:ident) => do
      if isSelfBalance t f then return ← `(RawExpr.env EnvKey.selfBalance)
      (nameParts f.getId).foldlM (init := ← expandOperand t) fun acc c =>
        `(RawExpr.field $acc $(quote c))
  | `(dl_term| $t:dl_term [ $i:dl_term ]) => do
      `(RawExpr.index $(← expandOperand t) $(← expandOperand i))
  | `(dl_term| $a:dl_term + $b:dl_term) => do
      `(RawExpr.binop .add $(← expandOperand a) $(← expandOperand b))
  | `(dl_term| $a:dl_term - $b:dl_term) => do
      `(RawExpr.binop .sub $(← expandOperand a) $(← expandOperand b))
  | `(dl_term| ( $t:dl_term )) => expandOperand t
  | stx => Macro.throwErrorAt stx
      "`==` compares program expressions: names, `e.f`, `e[e]`, `a + b`, `a - b`, numbers"

def expandUpd (U : TSyntax `dl_upd) : MacroM Lean.Term := do
  if let `(dl_upd| ‹ $_:term ›) := U then noEscape U
  -- the elements, read off the `sepBy1` node: `‖` does not splice in a pattern
  let elems ← U.raw[1].getSepArgs.mapM fun e => do
    match (⟨e⟩ : TSyntax `dl_upd_elem) with
    | `(dl_upd_elem| $l:dl_term := $r:dl_term) =>
      let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
      let [n] := nameParts x.getId | Macro.throwErrorAt l "an update assigns a variable"
      if n == "selfBalance" then
        return ← match r with
          | `(dl_term| selfBalance - $a) => do `(RawUpdElem.selfBalance IntOp.sub $(← expandTerm a))
          | `(dl_term| selfBalance + $a) => do `(RawUpdElem.selfBalance IntOp.add $(← expandTerm a))
          | _ => Macro.throwErrorAt r "`selfBalance - a` or `selfBalance + a`"
      if n == "net" then
        let net (a a' v : TSyntax `dl_term) (op : Lean.Term) : MacroM Lean.Term := do
          unless a.raw.structEq a'.raw do Macro.throwErrorAt a' "the entry read is the one written"
          `(RawUpdElem.net $(← expandTerm a) $op $(← expandTerm v))
        match r with
        | `(dl_term| store(net, at($a), net($a') - $v)) => return ← net a a' v (← `(IntOp.sub))
        | `(dl_term| store(net, at($a), net($a') + $v)) => return ← net a a' v (← `(IntOp.add))
        | `(dl_term| store(net, at($a), select(net, at($a')) - $v)) =>
          return ← net a a' v (← `(IntOp.sub))
        | `(dl_term| store(net, at($a), select(net, at($a')) + $v)) =>
          return ← net a a' v (← `(IntOp.add))
        | _ => pure ()
      `(RawUpdElem.assign $(quote n) $(← expandTerm r))
    | _ => Macro.throwUnsupported
  `([$elems,*])

/-- The Lean term of a formula that is one: a name `φ`, or `‹t›`. -/
def fmlHole? (stx : Syntax) : Option Lean.Term :=
  match (⟨stx⟩ : TSyntax `dl_fml) with
  | `(dl_fml| $x:ident) => some x
  | `(dl_fml| ‹ $t:term ›) => some t
  | _ => none

/-- The Lean formulas of a formula, each once, in order. -/
partial def fmlHoles (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  if (fmlHole? stx).isSome then
    if acc.any (·.structEq stx) then acc else acc.push stx
  else stx.getArgs.foldl (fun acc s => fmlHoles s acc) acc

/-- How a formula is read: what `⟨[ ]⟩` stands for (none in `dl[C]{ … }`,
which refuses it), and its Lean formulas (`fmlHoles`), numbered. -/
structure Reading where
  either : Option Lean.Term := none
  holes : Array Syntax := #[]

partial def expandFml (r : Reading) : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| true) => `(RawFml.tt)
  | `(dl_fml| false) => `(RawFml.not RawFml.tt)
  | `(dl_fml| $a:dl_term = $b:dl_term) => do `(RawFml.eq $(← expandTerm a) $(← expandTerm b))
  | `(dl_fml| $a:dl_term ≐ $b:dl_term) => do `(RawFml.teq $(← expandTerm a) $(← expandTerm b))
  | `(dl_fml| defined( $t:dl_term )) => do `(RawFml.defined $(← expandTerm t))
  | `(dl_fml| $a:dl_term == $b:dl_term) => do
      `(RawFml.peq $(← expandOperand a) $(← expandOperand b))
  | `(dl_fml| $a:dl_term != $b:dl_term) => do
      `(RawFml.pne $(← expandOperand a) $(← expandOperand b))
  | `(dl_fml| $a:dl_term < $b:dl_term) => cmp ``BinOp.lt a b
  | `(dl_fml| $a:dl_term <= $b:dl_term) => cmp ``BinOp.le a b
  | `(dl_fml| $a:dl_term <= $b:dl_term <= $c:dl_term) => do
      `(RawFml.and $(← cmp ``BinOp.le a b) $(← cmp ``BinOp.le b c))
  | `(dl_fml| $a:dl_term > $b:dl_term) => cmp ``BinOp.gt a b
  | `(dl_fml| $a:dl_term >= $b:dl_term) => cmp ``BinOp.ge a b
  | `(dl_fml| ∀ $T:ident $x:ident; $φ:dl_fml) => do
      `(RawFml.all $(← specSort T) $(quote x.getId.toString) $(← expandFml r φ))
  | `(dl_fml| ∃ $T:ident $x:ident; $φ:dl_fml) => do
      `(RawFml.not (RawFml.all $(← specSort T) $(quote x.getId.toString)
        (RawFml.not $(← expandFml r φ))))
  | `(dl_fml| ¬ $φ:dl_fml) => do `(RawFml.not $(← expandFml r φ))
  | `(dl_fml| $φ:dl_fml ∧ $ψ:dl_fml) | `(dl_fml| $φ:dl_fml && $ψ:dl_fml) => do
      `(RawFml.and $(← expandFml r φ) $(← expandFml r ψ))
  | `(dl_fml| $φ:dl_fml ∨ $ψ:dl_fml) => do
      `(RawFml.not (RawFml.and (RawFml.not $(← expandFml r φ)) (RawFml.not $(← expandFml r ψ))))
  | `(dl_fml| $φ:dl_fml → $ψ:dl_fml) => do `(RawFml.imp $(← expandFml r φ) $(← expandFml r ψ))
  | `(dl_fml| $φ:dl_fml ↔ $ψ:dl_fml) => do
      let φ ← expandFml r φ
      let ψ ← expandFml r ψ
      `(RawFml.and (RawFml.imp $φ $ψ) (RawFml.imp $ψ $φ))
  | stx@`(dl_fml| { havoc } $_:dl_fml) =>
      Macro.throwErrorAt stx "`{ havoc }` is what a callback rule leaves, not a formula to write: \
        `dl[C]{ … }` reads formulas of `Stmt.run`"
  | `(dl_fml| $U:dl_upd $φ:dl_fml) => do
      -- judged as the modality under it, else as the formula's (the diamond in `dl!{ … }`)
      let dflt ← match r.either with
        | some m => pure m
        | none => `(Modality.diamond)
      let m := (← fmlModality? dflt φ).getD dflt
      `(RawFml.upd $m $(← expandUpd U) $(← expandFml r φ))
  | `(dl_fml| ⟨ $[$ss:sol_stmt;]* ⟩ $φ:dl_fml) => do
      `(RawFml.modal .diamond [$(← ss.mapM expandStmt),*] $(← expandFml r φ))
  | `(dl_fml| [ $[$ss:sol_stmt;]* ] $φ:dl_fml) => do
      `(RawFml.modal .box [$(← ss.mapM expandStmt),*] $(← expandFml r φ))
  | stx@`(dl_fml| ⟨[ $[$ss:sol_stmt;]* ]⟩ $φ:dl_fml) => do
      let some m := r.either | Macro.throwErrorAt stx ("`⟨[ … ]⟩` is either modality: " ++
        "read the formula at one, `dl![m]{ … }`, or write `⟨ … ⟩` or `[ … ]`")
      `(RawFml.modal $m [$(← ss.mapM expandStmt),*] $(← expandFml r φ))
  | stx@`(dl_fml| ⟨ $_:sol_block ⟩ $_:dl_fml) | stx@`(dl_fml| [ $_:sol_block ] $_:dl_fml) =>
      Macro.throwErrorAt stx "a program that is a schema variable belongs to `dl{ … }`"
  | `(dl_fml| ( $φ:dl_fml )) => expandFml r φ
  | `(dl_fml| ( $[$as:dl_fml],* ⟹ $φ:dl_fml )) => do
      as.foldrM (init := ← expandFml r φ) fun a acc => do `(RawFml.imp $(← expandFml r a) $acc)
  | stx@`(dl_fml| $_:ident) | stx@`(dl_fml| ‹ $_:term ›) => do
      let some i := r.holes.findIdx? (·.structEq stx) | Macro.throwUnsupported
      `(RawFml.lean $(quote i))
  | _ => Macro.throwUnsupported
where
  cmp (op : Lean.Name) (a b : TSyntax `dl_term) : MacroM Lean.Term := do
    `(RawFml.cmp $(mkIdent op) $(← expandTerm a) $(← expandTerm b))

end Expand

/-! ## Names

Those of the program syntax (`RawExpr.names`, `RawStmt.names`,
`RawStmt.decls`) are `Syntax.lean`'s. -/

mutual

/-- The names a raw term reads (not the heads of `f(…)`, not a type). -/
def RawTerm.names : RawTerm → List String
  | .name x => if ["storage", "memory", "true", "false"].contains x then [] else [x]
  | .field t _ => t.names
  | .at a b | .add a b | .sub a b => a.names ++ b.names
  | .app "defVal" _ => []
  | .app "copyMem" (_ :: ts) => RawTerm.namesList ts
  | .app _ ts => RawTerm.namesList ts
  | .num _ | .env _ => []

def RawTerm.namesList : List RawTerm → List String
  | [] => []
  | t :: ts => t.names ++ RawTerm.namesList ts

end

def RawUpdElem.names : RawUpdElem → List String
  | .assign x t => if x = "storage" || x = "memory" then t.names else x :: t.names
  | .selfBalance _ a => a.names
  | .net r _ a => r.names ++ a.names

/-- The names a raw formula mentions, and those its programs declare. -/
def RawFml.names : RawFml → List String × List String
  | .tt => ([], [])
  | .eq a b | .teq a b => (a.names ++ b.names, [])
  | .defined t => (t.names, [])
  | .peq a b | .pne a b => (a.names ++ b.names, [])
  | .cmp _ a b => (a.names ++ b.names, [])
  | .all _ x φ =>
    let (u, d) := φ.names
    (u.filter (· != x), d)
  | .not φ => φ.names
  | .and φ ψ | .imp φ ψ =>
    let (u, d) := φ.names
    let (u', d') := ψ.names
    (u ++ u', d ++ d')
  | .upd _ U φ =>
    let (u, d) := φ.names
    ((U.map RawUpdElem.names).flatten ++ u, d)
  | .modal _ P φ =>
    let (u, d) := φ.names
    (RawStmt.namesList P ++ u, RawStmt.declsList P ++ d)
  | .lean _ => ([], [])

/-- The statements of every program in a formula. -/
def RawFml.stmts : RawFml → List RawStmt
  | .not φ | .upd _ _ φ | .all _ _ φ => φ.stmts
  | .and φ ψ | .imp φ ψ => φ.stmts ++ ψ.stmts
  | .modal _ P φ => P ++ φ.stmts
  | _ => []

/-- `t = true`, both sides defined: a condition as a formula. -/
def boolFml {C : Contract} (t : Term C) : Fml C := .eqD t (.lit (.bool true))

/-- `a ⊕ b = true`, defined: a comparison as a formula (`a < b` and the like). -/
def cmpFml {C : Contract} (op : BinOp) (p : PrimTy) (a b : Term C) : Fml C :=
  boolFml (.binop op p a b)

/-- The slot of a formula's `i`th Lean formula while it is read:
`defined(⟪i⟫)`, a local no program can name, with index `0` and no modality,
as the formula it stands for (`Post`, `Chains.lean`). -/
def Fml.slot {C : Contract} (i : Nat) : Fml C := .defined (.pv (.user s!"⟪{i}⟫"))

/-- Whether a formula is a slot. -/
def Fml.isSlot {C : Contract} : Fml C → Bool
  | .defined (.pv (.user s)) => s.startsWith "⟪"
  | _ => false

/-! ## Elaboration -/

section Read

variable [FreshNames] (C : Contract)

/-- What a name stands for in a term. -/
inductive NameKind where
  | local | alias | mem | root | store

/-- A local in scope by what it holds, then a state variable, then a fresh
`sp1`/`mv1` by its spelling; anything else is a stack local. -/
def nameKind (Γ : ECtx) (x : String) : NameKind :=
  match lookupBy x Γ with
  | some (.val _) => .local
  | some (.alias _) => .alias
  | some (.mem _) => .mem
  | some .store => .store
  | none =>
    if (C.rootType x).isSome then .root else
    match Var.ofName x with
    | .fresh "sp" _ => .alias
    | .fresh "mv" _ => .mem
    | _ => .local

/-- Whether a term is rooted in memory: a memory local, or a reference read. -/
def isMemTerm (Γ : ECtx) : RawTerm → Bool
  | .name x => (nameKind C Γ x matches .mem)
  | .field t _ | .at t _ => isMemTerm Γ t
  | .app "read" _ | .app "freshId" _ => true
  | _ => false

/-- The type of the storage location a path term names, when the contract
says. -/
def pathTy (Γ : ECtx) : RawTerm → Option Ty
  | .name x => match lookupBy x Γ with
    | some (.alias R) => some (.ref R)
    | some _ => none
    | none => C.rootType x
  | .field t f => do
    let .ref (.struct s) ← pathTy Γ t | none
    C.fieldType s f
  | .at t _ => do
    match ← pathTy Γ t with
    | .ref (.mapping _ V) => some V
    | .ref (.array E) => some E
    | _ => none
  | _ => none

/-- The element type of the array a path term names. -/
def elemTy (Γ : ECtx) (t : RawTerm) : Except String Ty :=
  match pathTy C Γ t with
  | some (.ref (.array E)) => pure E
  | _ => throw "a push or a pop on a path the contract does not type as an array"

mutual

/-- A term at the value sort. -/
partial def tVal (Γ : ECtx) : RawTerm → Except String (Term C)
  | .num n => pure (.lit (.int n))
  | .name "true" => pure (.lit (.bool true))
  | .name "false" => pure (.lit (.bool false))
  | .name x =>
    match nameKind C Γ x with
    | .local => pure (.pv (Var.ofName x))
    | .root => pure (.find .storage (.root x))
    | .alias => throw s!"`{x}` is a storage alias, not a value: read it with `find(storage, …)`"
    | .mem => throw s!"`{x}` is a memory reference, not a value"
    | .store => throw s!"`{x}` is a storage, not a value: read it with `find({x}, …)`"
  | .add a b => do pure (.binop .add .uint (← tVal Γ a) (← tVal Γ b))
  | .sub a b => do pure (.binop .sub .uint (← tVal Γ a) (← tVal Γ b))
  | .field p "length" => do
    if isMemTerm C Γ p then pure (.mlen .memory (← tIdent Γ p))
    else pure (.len .storage (← tPath Γ p))
  | t@(.field ..) | t@(.at ..) => do
    if isMemTerm C Γ t then pure (.read .memory (← tAddr Γ t))
    else pure (.find .storage (← tPath Γ t))
  | .app "select" [s, r] | .app "find" [s, r] => do pure (.find (← tStor Γ s) (← tPath Γ r))
  | .app "read" [m, a] => do pure (.read (← tMem Γ m) (← tAddr Γ a))
  | .app "net" [a] => do pure (.net (← tVal Γ a))
  | .app "net" [.name x, a] => do pure (.netOf (Var.ofName x) (← tVal Γ a))
  | .app "!" [t] => do pure (.unop .not .bool (← tVal Γ t))
  | .app "defVal" [.name "uint"] => pure (.lit (PrimTy.default .uint))
  | .app "defVal" [.name "int"] => pure (.lit (PrimTy.default .int))
  | .app "defVal" [.name "bool"] => pure (.lit (PrimTy.default .bool))
  | .app f _ => throw s!"`{f}(…)` is not a value term"
  | .env k => pure (.env k)

/-- A term at the storage-path sort. -/
partial def tPath (Γ : ECtx) : RawTerm → Except String (PTerm C)
  | .name x =>
    match nameKind C Γ x with
    | .root => pure (.root x)
    | .mem => throw s!"`{x}` is a memory reference, not a storage path"
    | _ => pure (.pv (Var.ofName x))
  | .field t f => do pure (.field (← tPath Γ t) f)
  | .at t i => do
    -- `p[p.length]`, the slot one past the end: no bounds check
    match t, i with
    | .name x, .field (.name y) "length" =>
      if x == y then pure (.next (← tPath Γ t)) else pure (.at (← tPath Γ t) (← tVal Γ i))
    | _, _ => pure (.at (← tPath Γ t) (← tVal Γ i))
  | _ => throw "not a storage path: a name, `p.f` or `p[t]`"

/-- A term at the storage sort; a push and a pop are nested
`save`s over the length. -/
partial def tStor (Γ : ECtx) : RawTerm → Except String (STerm C)
  | .name "storage" => pure .storage
  | .name x =>
    if nameKind C Γ x matches .store then pure (.pv (Var.ofName x))
    else throw s!"`{x}` is not a storage: `storage`, or a variable an update binds to one"
  | .app "store" [s, .name r, v] => do pure (.save (← tStor Γ s) (.root r) (← tSVal Γ v))
  | .app "save" [s, .field b "length", v] => do
    match s, v with
    | .app "save" [s', .at _ _, w], .add _ (.num 1) =>
      pure (.push (← tStor Γ s') (← tPath Γ b) (← tSVal Γ w))
    | .app "delAt" [s', .at _ _], .add _ (.num 1) =>
      pure (.pushSlot (← tStor Γ s') (← tPath Γ b) (← elemTy C Γ b))
    | .app "delAt" [s', .at _ _], .sub _ (.num 1) => pure (.pop (← tStor Γ s') (← tPath Γ b))
    | _, .add _ (.num 1) => pure (.extend (← tStor Γ s) (← tPath Γ b) (← elemTy C Γ b))
    | _, .sub _ (.num 1) => pure (.shrink (← tStor Γ s) (← tPath Γ b))
    | _, _ => throw "the length of an array is written by a push or a pop"
  | .app "save" [s, p, v] => do pure (.save (← tStor Γ s) (← tPath Γ p) (← tSVal Γ v))
  | .app "delAt" [s, p] => do pure (.delAt (← tStor Γ s) (← tPath Γ p))
  | _ => throw "not a storage: `storage`, `store(s, r, v)`, `save(s, p, v)` or `delAt(s, p)`"

/-- What a storage `save` writes. -/
partial def tSVal (Γ : ECtx) : RawTerm → Except String (SValT C)
  | .app "find" [s, p] => do pure (.find (← tStor Γ s) (← tPath Γ p))
  | .app "copyMem" [_, m, i] => do pure (.copyMem (← tMem Γ m) (← tIdent Γ i))
  | .app "newArr" _ => throw "`newArr(n)` does not say what it allocates: write it as a Lean term"
  | t => do pure (.val (← tVal Γ t))

/-- A term at the memory-identity sort. -/
partial def tIdent (Γ : ECtx) : RawTerm → Except String (ITerm C)
  | .name x =>
    match nameKind C Γ x with
    | .root => throw s!"`{x}` is a state variable, not a memory reference"
    | _ => pure (.pv (Var.ofName x))
  | .field t f => do pure (.read .memory (.field (← tIdent Γ t) f))
  | .at t k => do pure (.read .memory (.at (← tIdent Γ t) (← tVal Γ k)))
  | .app "read" [m, a] => do pure (.read (← tMem Γ m) (← tAddr Γ a))
  | .app "freshId" [.app "copySt" [m, v]] => do pure (.copy (← tMem Γ m) (← tSVal Γ v))
  | .app "freshId" _ => throw "`freshId(addM(m))` does not say what it allocates: write it as a Lean term"
  | _ => throw "not a memory reference"

/-- A term at the memory-location sort: a member or an element. -/
partial def tAddr (Γ : ECtx) : RawTerm → Except String (MAddr C)
  | .field t f => do pure (.field (← tIdent Γ t) f)
  | .at t k => do pure (.at (← tIdent Γ t) (← tVal Γ k))
  | _ => throw "not a memory location: `i.f` or `i[k]`"

/-- A term at the memory sort. -/
partial def tMem (Γ : ECtx) : RawTerm → Except String (MTerm C)
  | .name "memory" => pure .memory
  | .app "write" [m, a, v] => do pure (.write (← tMem Γ m) (← tAddr Γ a) (← tMVal Γ v))
  | .app "copySt" [m, v] => do pure (.copySt (← tMem Γ m) (← tSVal Γ v))
  | .app "addM" _ => throw "`addM(m)` does not say what it allocates: write it as a Lean term"
  | _ => throw "not a memory: `memory`, `write(m, a, v)` or `copySt(m, v)`"

/-- What a memory `write` writes: a memory local or a fresh identity is a
reference, anything else a value. -/
partial def tMVal (Γ : ECtx) : RawTerm → Except String (MValT C)
  | t@(.name x) => do
    if nameKind C Γ x matches .mem then pure (.ref (← tIdent Γ t)) else pure (.val (← tVal Γ t))
  | t@(.app "freshId" _) => do pure (.ref (← tIdent Γ t))
  | t => do pure (.val (← tVal Γ t))

end

/-- The type of a storage path expression, from the contract alone. -/
def RawExpr.pathTy : RawExpr → Option Ty
  | .name x => C.rootType x
  | .field e f => do
    let .ref (.struct s) ← e.pathTy | none
    C.fieldType s f
  | .index e _ => do
    match ← e.pathTy with
    | .ref (.mapping _ V) => some V
    | .ref (.array E) => some E
    | _ => none
  | _ => none

/-- A name a statement binds to a storage path without declaring it
(`p = alice;`, `p = people.push();`): what symbolic execution leaves of
`Person storage p = alice;`. -/
def RawStmt.aliasHints : RawStmt → List (String × RefTy)
  | .assign (.name x) r => match r.pathTy C with
    | some (.ref R) => [(x, R)]
    | _ => []
  | .assignPush (.name x) b => match b.pathTy C with
    | some (.ref (.array (.ref R))) => [(x, R)]
    | _ => []
  | .ite _ t e => (t.attach.flatMap fun ⟨s, _⟩ => s.aliasHints) ++
      e.attach.flatMap fun ⟨s, _⟩ => s.aliasHints
  | _ => []

/-- A parallel update, and the scope under it: `x := p` for a path `p` of
reference type binds `x` as an alias of that type.  Every right-hand side is
read in the scope in front of the update. -/
def elabUpd (Γ : ECtx) : List RawUpdElem → Except String (Upd C × ECtx)
  | [] => pure ([], Γ)
  | .selfBalance op a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.selfBalance op (← tVal C Γ a) :: U', Γ')
  | .net r op a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.net (← tVal C Γ r) op (← tVal C Γ a) :: U', Γ')
  | .assign x t :: U => do
    let (U', Γ') ← elabUpd Γ U
    if x = "storage" then return (.storage (← tStor C Γ t) :: U', Γ')
    if x = "memory" then return (.memory (← tMem C Γ t) :: U', Γ')
    -- `oldNet := net`: a ledger variable, which `net(oldNet, a)` reads
    if (t matches .name "net") && (C.rootType "net").isNone then
      return (.saveNet (Var.ofName x) :: U', Γ')
    -- `old := storage`: a storage variable
    if isStorTerm t then return (.store (Var.ofName x) (← tStor C Γ t) :: U', setBy x .store Γ')
    if let some (.ref R) := pathTy C Γ t then
      return (.path (Var.ofName x) (← tPath C Γ t) :: U', setBy x (.alias R) Γ')
    if t matches .app "freshId" _ then return (.mref (Var.ofName x) (← tIdent C Γ t) :: U', Γ')
    match nameKind C Γ x with
    | .alias => return (.path (Var.ofName x) (← tPath C Γ t) :: U', Γ')
    | .mem => return (.mref (Var.ofName x) (← tIdent C Γ t) :: U', Γ')
    | .root => throw s!"`{x}` is a state variable: an update writes it through `storage := …`"
    | .store => throw s!"`{x}` is a storage variable: its right-hand side is a storage"
    | .local => return (.val (Var.ofName x) (← tVal C Γ t) :: U', Γ')
where
  /-- A storage term: `storage`, a storage variable, or a write over one. -/
  isStorTerm : RawTerm → Bool
    | .name "storage" => true
    | .name y => (nameKind C Γ y matches .store)
    | .app "store" _ | .app "save" _ | .app "delAt" _ => true
    | _ => false

/-- `a == b`: the operands typed as Solidity types them (the first that is
not a literal gives the type), then lowered. -/
def elabCompare (Γ : ECtx) (a b : RawExpr) : Except String (Term C × Term C) := do
  let t ← if a.isLit then synth C Γ b else synth C Γ a
  let some ⟨p, _⟩ := t.toVal? | throw "`==` compares values, not storage or memory references"
  pure ((← check C Γ p a).lower, (← check C Γ p b).lower)

/-- Run `x`, then restore the locals in scope (not the capture counter). -/
def inScope (x : ElabM α) : ElabM α := do
  let (Γ, _) ← get
  let r ← x
  modify fun (_, k) => (Γ, k)
  pure r

/-- A formula: a program elaborates in the scope in front of it, and its
declarations are in scope in its postcondition. -/
def elabFml : RawFml → ElabM (Fml C)
  | .tt => pure .tt
  | .eq a b => do
    let (Γ, _) ← get
    pure (.eqD (← tVal C Γ a) (← tVal C Γ b))
  | .teq a b => do
    let (Γ, _) ← get
    pure (.eq (← tVal C Γ a) (← tVal C Γ b))
  | .defined t => do
    let (Γ, _) ← get
    pure (.defined (← tVal C Γ t))
  | .peq a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.eqD a b)
  | .pne a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.not (.eqD a b))
  | .cmp op a b => do
    let (Γ, _) ← get
    pure (cmpFml op .uint (← tVal C Γ a) (← tVal C Γ b))
  | .all p x φ => inScope do
    modify fun (Γ, k) => (setBy x (.val p) Γ, k)
    pure (.all (Var.ofName x) p (← elabFml φ))
  | .not φ => do pure (.not (← inScope (elabFml φ)))
  | .and φ ψ => do pure (.and (← inScope (elabFml φ)) (← inScope (elabFml ψ)))
  | .imp φ ψ => do pure (.imp (← inScope (elabFml φ)) (← inScope (elabFml ψ)))
  | .upd m U φ => inScope do
    let (Γ, k) ← get
    let (U', Γ') ← elabUpd C Γ U
    set (Γ', k)
    pure (.upd m U' (← elabFml φ))
  | .modal m P φ => inScope do
    let P' ← elabStmts C P
    pure (.modal m P' (← elabFml φ))
  | .lean i => pure (Fml.slot i)

/-- Elaborate a formula against `C`.  Its parameters (the names nothing
declares) are in scope from the start: an alias if a program binds one to a
storage path, else a `uint` local.  A capture is numbered past every fresh
variable the formula writes. -/
def elabDl (φ : RawFml) : Except String (Fml C) :=
  let (used, declared) := φ.names
  let hints := φ.stmts.flatMap (RawStmt.aliasHints C)
  -- an enum's name (`State` in `State.Locked`) is no parameter
  let free := (used.filter fun x => !declared.contains x && (C.rootType x).isNone &&
    (lookupBy x C.enums).isNone).eraseDups
  let params := free.filterMap fun x =>
    match lookupBy x hints, Var.ofName x with
    | some R, _ => some (x, LocalTy.alias R)
    | none, .fresh "sp" _ | none, .fresh "mv" _ => none
    | none, _ => some (x, LocalTy.val .uint)
  let k := (used ++ declared).foldl (fun k x => max k (Var.ofName x).idx) 0 + 1
  ((elabFml C φ).run C.funs).run' (params, k)

end Read

/-! ## Putting the Lean terms back -/

section Fill
open Lean (mkApp mkApp2 mkConst mkStrLit)

/-- `Fml.slot i`, quoted, for the contract `c`. -/
def slotExpr (c : Lean.Expr) (i : Nat) : Lean.Expr :=
  mkApp2 (mkConst ``Fml.defined) c
    (mkApp2 (mkConst ``Term.pv) c (mkApp (mkConst ``Var.user) (mkStrLit s!"⟪{i}⟫")))

/-- The `i` of a quoted `Fml.slot i`. -/
def slotIdx? (e : Lean.Expr) : Option Nat := do
  guard (e.isAppOfArity ``Fml.defined 2)
  let t := e.appArg!
  guard (t.isAppOfArity ``Term.pv 2)
  let x := t.appArg!
  guard (x.isAppOfArity ``Var.user 1)
  let .lit (.strVal s) := x.appArg! | none
  guard (s.startsWith "⟪" && s.endsWith "⟫")
  ((s.drop 1).dropRight 1).toNat?

/-- The formula whose readings at the diamond (`d`) and at the box (`b`) are
given, with its Lean terms back: `m` where `d` has the diamond and `b` the
box, the formula `φs[i]` at the slot `i`.  Elsewhere the two agree.  A quoted
formula has no binders, so a term is put back as it is. -/
partial def fillSlots (m? : Option Lean.Expr) (φs : Array Lean.Expr) (d b : Lean.Expr) :
    Except String Lean.Expr := do
  if let some m := m? then
    if d.isConstOf ``Modality.diamond && b.isConstOf ``Modality.box then return m
  if let some i := slotIdx? d then
    if let some φ := φs[i]? then
      if slotIdx? b == some i then return φ
  match d, b with
  | .app f x, .app g y => return .app (← fillSlots m? φs f g) (← fillSlots m? φs x y)
  | _, _ => if d == b then pure d else throw "the readings at the diamond and at the box differ"

end Fill

/-! ## `dl[C]{ … }` and `dl!{ … }` -/

/-- `dl[C]{ φ }`: the formula `φ`, its names resolved against the contract `C`. -/
syntax "dl[" term "]{ " dl_fml " }" : term

/-- `dl[C, m]{ φ }`: `dl[C]{ φ }` at the modality `m`, a Lean term (a
variable, `.box`, `.diamond`): `⟨[ P ]⟩ ψ` is `P` under `m`, and an update with
no modality under it is judged at `m`. -/
syntax "dl[" term ", " term "]{ " dl_fml " }" : term

/-- `dl!{ φ }`: `dl[C]{ φ }` for the file's `InContract` contract.  (`dl{ φ }`
is the schema reading.) -/
syntax "dl!{ " dl_fml " }" : term

/-- `dl![m]{ φ }`: `dl[C, m]{ φ }` for the file's `InContract` contract. -/
syntax "dl![" term "]{ " dl_fml " }" : term

/-- A sequent line, `dl[C]{ Γ ⟹ φ }` (and at a modality, and for the file's
contract): the formula `a₁ → … → φ` (`dl[C]{ (Γ ⟹ φ) }`). -/
syntax (name := dlSeq) "dl[" term "]{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term
@[inherit_doc dlSeq] syntax "dl[" term ", " term "]{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term
@[inherit_doc dlSeq] syntax "dl!{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term
@[inherit_doc dlSeq] syntax "dl![" term "]{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term

open Lean Elab Term Meta in
/-- `dl[C, m]{ φ }`, `m` optional.  A constructor is read as itself, any other
modality twice, at the diamond and at the box, in one evaluation (the two
sides of a conjunction); `fillSlots` then puts `m` and the Lean formulas
back. -/
def elabDlAt (c : Lean.Term) (m? : Option Lean.Term) (φ : TSyntax `dl_fml) :
    TermElabM Lean.Expr := do
  let holes := fmlHoles φ
  let m? ← m?.mapM fun m => do instantiateMVars (← elabTermEnsuringType m (mkConst ``Modality))
  let read (μ : Option Lean.Name) : TermElabM Lean.Term :=
    liftMacroM (expandFml { either := μ.map fun n => (mkCIdent n : Lean.Term), holes } φ)
  let once (μ : Option Lean.Name) : TermElabM Lean.Expr := do
    let raw ← read μ
    elabAgainst c fun q => `((elabDl $c $raw).map (Fml.quote $q))
  let (d, b) ← match m? with
    | none => do let e ← once none; pure (e, e)
    | some m =>
      if m.isConstOf ``Modality.diamond || m.isConstOf ``Modality.box then
        let e ← once m.constName?
        pure (e, e)
      else
        let rd ← read ``Modality.diamond
        let rb ← read ``Modality.box
        let e ← elabAgainst c fun q =>
          `((do pure (Fml.and (← elabDl $c $rd) (← elabDl $c $rb))).map (Fml.quote $q))
        let #[_, d, b] := e.getAppArgs | throwError "dl[C, m]: not two readings{indentExpr e}"
        pure (d, b)
  if holes.isEmpty && d == b then return d
  let ty ← inferType d
  let φs ← holes.mapM fun h => do
    let some t := fmlHole? h | throwError "dl[C]: not a formula hole"
    withRef h do
      -- A misspelt `true` is not a new variable of the signature.
      if let `($x:ident) := t then
        if (← resolveLocalName x.getId).isNone && (← resolveGlobalName x.getId).isEmpty then
          throwError "a name where a formula stands is a Lean formula (φ : Post C): unknown `{x}`"
      withoutAutoBoundImplicit do elabTermEnsuringType t ty
  match fillSlots m? φs d b with
  | .ok e => return e
  | .error msg => throwError "dl[C, m]: {msg}"

open Lean Elab Term Meta in
elab_rules : term
  | `(dl[ $c ]{ $φ:dl_fml }) => elabDlAt c none φ
  | `(dl[ $c, $m ]{ $φ:dl_fml }) => elabDlAt c (some m) φ

macro_rules
  | `(dl!{ $φ:dl_fml }) => `(dl[InContract.contract]{ $φ })
  | `(dl![ $m ]{ $φ:dl_fml }) => `(dl[InContract.contract, $m]{ $φ })
  | `(dl[ $c ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(dl[$c]{ ($[$as],* ⟹ $φ) })
  | `(dl[ $c, $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(dl[$c, $m]{ ($[$as],* ⟹ $φ) })
  | `(dl!{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(dl[InContract.contract]{ ($[$as],* ⟹ $φ) })
  | `(dl![ $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) =>
    `(dl[InContract.contract, $m]{ ($[$as],* ⟹ $φ) })

/-! ## Examples -/

section Examples

local instance : InContract := ⟨StandardExample⟩

/-- A declaration's local is in scope in the postcondition. -/
example : Fml StandardExample := dl[StandardExample]{ ⟨ uint x = 10; ⟩ x == 10 }

/-- A write, then a read of it into a local, under the box. -/
example : Fml StandardExample := dl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 }

/-- `a` and `x` are bound by nothing: parameters, `uint` locals. -/
example : Fml StandardExample := dl!{ a == 1 → ⟨ x = a; ⟩ x == 1 }

/-- `==` on program expressions is `=` on their lowerings. -/
example : dl!{ alice.age == 10 } = dl!{ find(storage, alice.age) = 10 } := rfl

/-- An update: a local and the storage, in parallel. -/
example : Fml StandardExample :=
  dl!{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x }

/-- An alias bound by an update is an alias under it, in a program too. -/
example : Fml StandardExample := dl!{ { p := alice } ⟨ p.age = 3; ⟩ p.age == 3 }

/-- A push, in nested `save`s, reads back as one. -/
example : dl!{ { storage := save(save(storage, values[values.length], 7), values.length,
    values.length + 1) } true } =
    Fml.upd .diamond [.storage (.push .storage (.root "values") (.val (.lit (.int 7))))] .tt := rfl

/-- info: dl{ ⟨ uint x = 10; ⟩ x = 10 } : Fml StandardExample -/
#guard_msgs in #check dl!{ ⟨ uint x = 10; ⟩ x == 10 }

/--
info: dl{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x } : Fml StandardExample
-/
#guard_msgs in
#check dl!{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x }

/-- What a rule leaves prints as a formula that reads back as it. -/
example : (dl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 }).step =
    some dl!{ { storage := save(storage, alice.age, 10) } [ uint y = alice.age; ] y = 10 } := rfl

/-- `p = alice;` is what is left of a declaration: `p` is read as an alias. -/
example : (dl!{ ⟨ Person storage p = alice; p.age = 3; ⟩ p.age == 3 }).step =
    some dl!{ ⟨ p = alice; p.age = 3; ⟩ find(storage, p.age) = 3 } := rfl

/-- A capture is numbered past the fresh variables the formula writes. -/
example : dl!{ ⟨ values[total + 1] += 2; ⟩ ie3 == 0 } =
    dl!{ ⟨ uint ie4 = total + 1; values[ie4] += 2; ⟩ ie3 == 0 } := rfl

/-- `∨`, `↔` and `∃` are the connectives they stand for, and print back. -/
example : dl!{ a == 1 ∨ a == 2 } = dl!{ ¬(¬a == 1 ∧ ¬a == 2) } := rfl
example : dl!{ a == 1 ↔ b == 1 } = dl!{ (a == 1 → b == 1) ∧ (b == 1 → a == 1) } := rfl
example : dl!{ ∃ uint y; y == a } = dl!{ ¬(∀ uint y; ¬y == a) } := rfl

/-- info: dl{ a = 1 ∨ a = 2 ↔ ¬b = 1 } : Fml StandardExample -/
#guard_msgs in #check dl!{ a == 1 ∨ a == 2 ↔ ¬b == 1 }

/-- info: dl{ ∃ uint y; y = a } : Fml StandardExample -/
#guard_msgs in #check dl!{ ∃ uint y; y == a }

/-- `=` is `==`'s equation; `≐` the total one, and `defined` is its own atom. -/
example : dl!{ a = 1 } = Fml.eqD (.pv (.user "a")) (.lit (.int 1)) := rfl
example : dl!{ a ≐ 1 } = Fml.eq (.pv (.user "a")) (.lit (.int 1)) := rfl

/-- info: dl{ (defined(a) ∧ a ≐ 1) → a = 1 } : Fml StandardExample -/
#guard_msgs in #check dl!{ defined(a) ∧ a ≐ 1 → a = 1 }

/-- info: dl{ a = 1 } : Fml StandardExample -/
#guard_msgs in #check (Fml.eqD (.pv (.user "a")) (.lit (.int 1)) : Fml StandardExample)

/-- info: dl{ ¬a = 1 ∧ a < 2 } : Fml StandardExample -/
#guard_msgs in #check dl!{ a != 1 ∧ a < 2 }

/-- error: Solidity elaboration failed: unknown name y -/
#guard_msgs in #check dl!{ ⟨ uint y = 1; ⟩ true ∧ y == 1 }

/-! ### At a modality: `dl![m]{ … }` -/

/-- `⟨[ P ]⟩` at a constructor is its bracket. -/
example : dl![.box]{ ⟨[ alice.age = 10; ]⟩ alice.age == 10 } =
    dl!{ [ alice.age = 10; ] alice.age == 10 } := rfl
example : dl[StandardExample, .diamond]{ ⟨[ x = 1; ]⟩ x == 1 } = dl!{ ⟨ x = 1; ⟩ x == 1 } := rfl

/-- An update with no modality under it is judged at the formula's: the last
line of a box derivation, which `dl!{ … }` reads at the diamond. -/
example : symex 2 dl!{ [ x = 1; ] x == 1 } = dl![.box]{ { x := 1 } x == 1 } := rfl
example : dl![.box]{ { x := 1 } x == 1 } ≠ dl!{ { x := 1 } x == 1 } := by intro h; cases h

/-- A modality under the update still decides. -/
example : dl![.diamond]{ { x := 1 } [ x = 2; ] x == 2 } = dl!{ { x := 1 } [ x = 2; ] x == 2 } := rfl

/-- At a modality `m` the rules reduce: none but a revert looks at it. -/
example (m : Modality) :
    (dl![m]{ ⟨[ x = 1; ]⟩ x == 1 }).step = some dl![m]{ { x := 1 } ⟨[ ]⟩ x == 1 } := rfl
example (m : Modality) : symex 2 dl![m]{ ⟨[ x = 1; ]⟩ x == 1 } = dl![m]{ { x := 1 } x == 1 } := rfl

/-- info: dl{ ⟨[ x = 1; ]⟩ x = 1 } : Fml StandardExample -/
#guard_msgs in
variable (m : Modality) in
#check dl![m]{ ⟨[ x = 1; ]⟩ x == 1 }

/--
error: `⟨[ … ]⟩` is either modality: read the formula at one, `dl![m]{ … }`, or write `⟨ … ⟩` or `[ … ]`
-/
#guard_msgs in #check dl!{ ⟨[ x = 1; ]⟩ x == 1 }

/-! ### A Lean formula where a formula stands -/

/-- A name is a Lean formula: the postcondition `φ`. -/
example (φ : Fml StandardExample) :
    dl!{ { x := 1 } φ } = Fml.upd .diamond [.val (.user "x") (.lit (.int 1))] φ := rfl

/-- So is `‹t›`; `true` stays the keyword. -/
example (φ ψ : Fml StandardExample) : dl!{ ‹φ› ∧ ψ ∧ true } = Fml.and φ (Fml.and ψ .tt) := rfl

-- A name nothing binds is refused, not bound as a new variable of the
-- signature (`autoImplicit`): here a misspelt `true`.
/-- error: a name where a formula stands is a Lean formula (φ : Post C): unknown `ture` -/
#guard_msgs in
example : dl!{ ⟨ x = 1; ⟩ ture } = dl!{ ⟨ x = 1; ⟩ true } := rfl

/-- Both at once: `m` and `φ` are put back by one walk. -/
example (m : Modality) (φ : Fml StandardExample) :
    (dl![m]{ ⟨[ x = 1; ]⟩ φ }).step = some dl![m]{ { x := 1 } ⟨[ ]⟩ φ } := rfl

/-- info: fun m φ => dl{ ⟨[ x = 1; ]⟩ φ } : Modality → Fml StandardExample → Fml StandardExample -/
#guard_msgs in #check fun (m : Modality) (φ : Fml StandardExample) => dl![m]{ ⟨[ x = 1; ]⟩ φ }

-- An inaccessible name prints escaped: bare, it would read back as another.
/--
trace: φ✝ : Fml StandardExample
⊢ dl{ ⟨ x = 1; ⟩ ‹φ✝› } = dl{ ⟨ x = 1; ⟩ ‹φ✝› }
-/
#guard_msgs in
example : ∀ φ : Fml StandardExample, dl!{ ⟨ x = 1; ⟩ φ } = dl!{ ⟨ x = 1; ⟩ φ } := by
  intro
  trace_state
  rfl

-- `⊨` and `⊧` of a name alone are Lean's to print.
/-- info: fun φ => Valid φ ∧ ∀ (σ : State), holds σ φ : Fml StandardExample → Prop -/
#guard_msgs in #check fun (φ : Fml StandardExample) => (⊨ φ) ∧ ∀ σ, holds σ φ

/-! ### Chain-only spellings -/

/-- A sequent line is its formula: its antecedents imply its succedent. -/
example : dl!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true } =
    dl!{ 5 <= selfBalance → ⟨ to.transfer(5); ⟩ true } := rfl
example : dl!{ a == 1, b == 2 ⟹ a == b } = dl!{ a == 1 → b == 2 → a == b } := rfl

/-- The two goals of a split, and a line at a modality. -/
example : dl!{ (a == 1 ⟹ ⟨ x = 1; ⟩ true) ∧ (¬a == 1, b == 1 ⟹ false) } =
    dl!{ (a == 1 → ⟨ x = 1; ⟩ true) ∧ (¬a == 1 → b == 1 → false) } := rfl
example (m : Modality) : dl![m]{ a == 1 ⟹ ⟨[ x = 1; ]⟩ true } =
    dl![m]{ a == 1 → ⟨[ x = 1; ]⟩ true } := rfl

-- It prints as the formula it is.
/-- info: dl{ 5 <= selfBalance → ⟨ to .transfer(5); ⟩ true } : Fml StandardExample -/
#guard_msgs in #check dl!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true }

/-- `0 <= se <= selfBalance`, and the read of the ledger. -/
example : dl!{ 0 <= 5 <= selfBalance } = dl!{ 0 <= 5 ∧ 5 <= selfBalance } := rfl
example : dl!{ { net := store(net, at(to), select(net, at(to)) - 5) } select(net, at(to)) = x } =
    dl!{ { net := store(net, at(to), net(to) - 5) } net(to) = x } := rfl

end Examples

end Solidity
