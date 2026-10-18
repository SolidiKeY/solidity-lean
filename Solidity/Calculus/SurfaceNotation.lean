import Solidity.Calculus.Hyp
import Solidity.Syntax.Quote
import Solidity.Calculus.Lower
import Solidity.Calculus.NamedTerm

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
mini-solkey's: the macros here build a raw formula, which
`Calculus/Notation.lean`'s `elabDlAuto` reads scoped at compile time
(`elabAgainst`, as `sol[C]{ … }` does), a `Fml C []`, with or without a
modality; the examples are there.

**Lean terms in a formula.**  `dl![m]{ φ }` (`dl[C, m]{ φ }`) reads `φ` at
the modality `m`, a Lean term — a variable, `.box`, `.diamond`: `⟨[ P ]⟩ ψ`
is `P` under `m`, and an update with no modality under
it is judged at `m`, so the last line of a box derivation is
`dl![.box]{ { x := 1 } x == 1 }`.  In `dl!{ φ }` such an update is judged at
the diamond, and `⟨[ ]⟩` is refused.  A name where a formula stands, or
`‹t›`, is a Lean formula: the postcondition `φ` (a `Post C Γ`,
`Calculus/NotationResolve.lean`), which prints back as its name.  The reader runs as compiled
code, which no Lean variable can enter, so each of these stands in for
something closed while the formula is read, and one walk (`fillSlotsC`) puts
the Lean terms back: a formula is read as a slot (`Fml.slotC`), and the
modality as the difference between two readings, one at the diamond and one
at the box — the reading never looks at a modality, so they differ exactly
where `m` goes.

**The arrow `⟹` has two readings.**  In `dl!{ Γ ⟹ φ }` (and `dl[C]{ … }`,
`dl![m]{ … }`) it is a line of a chain, one formula `a₁ → … → φ` that prints
with `→` ("Chain-only spellings" below).  In `dl{ Γ ⟹ φ }`, and in the
goals a `⊢` derivation prints, it is a sequent, a `Proves` with its context
apart, which no `dl!{ … }` reads back.

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
  since a term is read by name (`NTm`, resolved where it stands,
  `Calculus/NamedTerm.lean`): a state variable is a root, anything else a
  program variable (`pv`); a bare state variable or path in a value position
  is `find(storage, p)`;
* a name no program in the formula declares is a **parameter**, in scope
  everywhere: a `uint` local (mini-solkey's reading of a free name), a KeY
  `int` one where only KeY `int` arithmetic reads it (`net(to) = x`,
  `RawFml.kintParams`), or an alias when a program binds it to a storage
  path (`p = alice;`, which is what symbolic execution leaves of `Person
  storage p = alice;`).  A name
  some program declares is no parameter anywhere in the formula: outside
  that declaration's scope it is unknown (`checkFresh` would refuse the
  declaration of a parameter), so a free name and a declared one differ;
* `x := p` in an update, for a path `p` of reference type, binds `x` as an
  alias of that type for the formula under it, and `x := i`, for a memory
  object `i` of a type the scope gives (`freshId(addM(memory, Person))`,
  `freshId(addM(memory, uint[]))`, `read(memory, carol.account)`), as a
  memory local of that type, and `x := t`, for a `bool` term `t`
  (`se1 := x <= 255`), as a `bool` local; `x := unset` is the alias of
  `T storage x;` bound to no path (`storageLocalDeclSkip`), `unset` a
  keyword there;
* a program binds the names it assigns without declaring them, at the type
  of the right-hand side, for the program and its postcondition
  (`scopeHints`): what a rule leaves of a declaration it drops.  `x =
  carol.account;` and `x = new uint[](n);` bind a memory local
  (`memoryLocalDeclInitDrop`), `r = q.token;` and `sp = sp1.push();` a
  storage alias, `q` being an alias the program declares or an update binds
  (`storageLocalDeclInitDrop`), and `se1 = x <= 255;` a `bool` local
  (`localValueDeclInitDrop`).  `sp1`, `mv1` (`FreshNames`) are an alias and a
  memory local wherever nothing else says otherwise;
* a capture the reading makes — a call statement carries its callee's body
  with every local renamed fresh — takes the least index that no fresh
  variable the formula writes has, so a line of a derivation, where the
  callee's locals are the gaps between the captures it shows, reads back
  with the same names — past every written index where a Lean formula other
  than a postcondition stands in the formula (`‹…›`), whose fresh variables
  the reading cannot see;
* `φ where Person memory carol` declares `carol` for `φ` (KeY's
  `\programVariables`: a program variable's kind is its declaration's, not
  the program's).  A copy out of storage needs it once its declaration is
  dropped: `carol = alice;` is what `memoryLocalDeclInitDrop` leaves of
  `Person memory carol = alice;` and `storageLocalDeclInitDrop` of `Person
  storage carol = alice;`, and a line is read on its own.  The printer writes
  the clause for such a line; `Account storage p` and `uint v` declare the
  other kinds.

A type where a term stands — what `addM(m, T)` and `newArr(T, n)` allocate —
is written as Solidity writes it: `Person`, `uint[]`, `Token[3]`.

What does not read back: `‹…›` in a term or an update (a Lean term, which is also how a
conditional and an operator other than `+`, `-`, `/` print), the operator schema variables
`⊕ ⊖ ± ⊕⊕` (taclets only), and `defVal(T)` for a non-primitive `T`, whose
printing drops the type.  A concrete `defVal(uint)` reads as the default value
itself.  The gaps a line leaves are filled a statement at a time: a statement
whose captures do not fit in the gap in front of it (an `if` whose branch
writes a capture between two calls) is numbered past every written index,
and does not read back as the derivation's line.
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
  /-- `p[i]@S`: the index checked in the storage `S`. -/
  | atIn (t i S : RawTerm)
  | add (a b : RawTerm)
  | sub (a b : RawTerm)
  /-- `a <= b`, `a < b`, `a == b` as a term: the right-hand side of a
  captured comparison, `x := a <= b`. -/
  | cmp (op : BinOp) (a b : RawTerm)
  /-- `a / b`, `a * b`: an operation on two `uint`s other than `+` and `-`. -/
  | arith (op : BinOp) (a b : RawTerm)
  | app (f : String) (args : List RawTerm)
  /-- `msg.sender`, `address(this).balance`, …: KeY's program variables
  `msgSender`, `selfBalance`, …. -/
  | env (k : EnvKey)
  deriving Repr, Inhabited, BEq

/-- One elementary update as written. -/
inductive RawUpdElem where
  | assign (x : String) (t : RawTerm)
  /-- `selfBalance := selfBalance ± a` -/
  | selfBalance (op : IntOp) (a : RawTerm)
  /-- `net := store(net, at(r), net(r) ± a)` -/
  | net (r : RawTerm) (op : IntOp) (a : RawTerm)
  /-- `net := if(r = this) then net else store(net, at(r), net(r) - a)`, a payment. -/
  | pay (r a : RawTerm)
  /-- `net := store(mtSt, at(r), a)`, a deployment's ledger. -/
  | netMt (r a : RawTerm)
  /-- `selfBalance := a`, a deployment's funds. -/
  | setBalance (a : RawTerm)
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
  read as a slot (`Fml.slotC i`) and put back after (`fillSlotsC`). -/
  | lean (i : Nat)
  /-- `φ where Person memory carol`: the locals declared, in scope in `φ`. -/
  | decl (ds : List RawStmt) (φ : RawFml)
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
          else if root == "this" then pure (← `(RawTerm.env EnvKey.selfAddress), flds)
          else pure (← `(RawTerm.name $(quote root)), flds)
      flds.foldlM (init := base) fun acc f =>
        `(RawTerm.field $acc $(quote f))
  | `(dl_term| $t:dl_term . $f:ident) => do
      if isSelfBalance t f then return ← `(RawTerm.env EnvKey.selfBalance)
      (nameParts f.getId).foldlM (init := ← expandTerm t) fun acc c =>
        `(RawTerm.field $acc $(quote c))
  | `(dl_term| $t:dl_term [ $i:dl_term ]) => do `(RawTerm.at $(← expandTerm t) $(← expandTerm i))
  | `(dl_term| $t:dl_term [ $i:dl_term ] @ $S:dl_term) => do
    `(RawTerm.atIn $(← expandTerm t) $(← expandTerm i) $(← expandTerm S))
  | `(dl_term| $t:dl_term []) => do `(RawTerm.app "[]" [$(← expandTerm t)])
  | `(dl_term| $a:dl_term + $b:dl_term) => do `(RawTerm.add $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| $a:dl_term - $b:dl_term) => do `(RawTerm.sub $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| $a:dl_term / $b:dl_term) => do
    `(RawTerm.arith BinOp.div $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| $a:dl_term * $b:dl_term) => do
    `(RawTerm.arith BinOp.mul $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| $a:dl_term && $b:dl_term) => do
    `(RawTerm.arith BinOp.and $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| $a:dl_term || $b:dl_term) => do
    `(RawTerm.arith BinOp.or $(← expandTerm a) $(← expandTerm b))
  | `(dl_term| ( $a:dl_term == $b:dl_term )) => do
    `(RawTerm.cmp BinOp.eqB $(← expandTerm a) $(← expandTerm b))
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
          | a => do `(RawUpdElem.setBalance $(← expandTerm a))
      if n == "net" then
        let net (a a' v : TSyntax `dl_term) (op : Lean.Term) : MacroM Lean.Term := do
          unless a.raw.structEq a'.raw do Macro.throwErrorAt a' "the entry read is the one written"
          `(RawUpdElem.net $(← expandTerm a) $op $(← expandTerm v))
        match r with
        | `(dl_term| store(mtSt, at($a), $v)) | `(dl_term| storeSt(mtSt, at($a), $v)) =>
          return ← `(RawUpdElem.netMt $(← expandTerm a) $(← expandTerm v))
        | `(dl_term| store(net, at($a), net($a') - $v)) => return ← net a a' v (← `(IntOp.sub))
        | `(dl_term| store(net, at($a), net($a') + $v)) => return ← net a a' v (← `(IntOp.add))
        | `(dl_term| store(net, at($a), select(net, at($a')) - $v)) =>
          return ← net a a' v (← `(IntOp.sub))
        | `(dl_term| store(net, at($a), select(net, at($a')) + $v)) =>
          return ← net a a' v (← `(IntOp.add))
        | `(dl_term| if($a = $t:ident) then $n':ident else store(net, at($a'), net($a'') - $v))
        | `(dl_term| if($a = $t:ident) then $n':ident
              else store(net, at($a'), select(net, at($a'')) - $v)) =>
          unless t.getId.toString == "this" do Macro.throwErrorAt t "a payment compares with `this`"
          unless n'.getId.toString == "net" do Macro.throwErrorAt n' "a payment to `this` leaves `net`"
          unless a.raw.structEq a'.raw && a.raw.structEq a''.raw do
            Macro.throwErrorAt a' "the entry read is the one written, and the one compared"
          return ← `(RawUpdElem.pay $(← expandTerm a) $(← expandTerm v))
        | _ => pure ()
      `(RawUpdElem.assign $(quote n) $(← expandTerm r))
    | `(dl_upd_elem| $l:dl_term := $a:dl_term <= $b:dl_term) => assignCmp l ``BinOp.le a b
    | `(dl_upd_elem| $l:dl_term := $a:dl_term < $b:dl_term) => assignCmp l ``BinOp.lt a b
    | `(dl_upd_elem| $l:dl_term := $a:dl_term > $b:dl_term) => assignCmp l ``BinOp.gt a b
    | `(dl_upd_elem| $l:dl_term := $a:dl_term >= $b:dl_term) => assignCmp l ``BinOp.ge a b
    | `(dl_upd_elem| $l:dl_term := $a:dl_term == $b:dl_term) => assignCmp l ``BinOp.eqB a b
    | `(dl_upd_elem| $l:dl_term := $a:dl_term != $b:dl_term) => assignCmp l ``BinOp.neB a b
    | _ => Macro.throwUnsupported
  `([$elems,*])
where
  /-- `x := a <= b`: the comparison, a term (`RawTerm.cmp`). -/
  assignCmp (l : TSyntax `dl_term) (op : Lean.Name) (a b : TSyntax `dl_term) : MacroM Lean.Term := do
    let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
    let [n] := nameParts x.getId | Macro.throwErrorAt l "an update assigns a variable"
    `(RawUpdElem.assign $(quote n) (RawTerm.cmp $(mkIdent op) $(← expandTerm a) $(← expandTerm b)))

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
        `dl[C]{ … }` is read scoped, over the typed run (`Prog.run`)"
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
  | `(dl_fml| $φ:dl_fml where $ds,*) => do
      `(RawFml.decl [$(← ds.getElems.mapM expandStmt),*] $(← expandFml r φ))
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
  | .name x => if ["storage", "memory", "mtSt", "true", "false"].contains x then [] else [x]
  | .field t _ => t.names
  | .at a b | .add a b | .sub a b | .cmp _ a b | .arith _ a b => a.names ++ b.names
  | .atIn a b s => a.names ++ b.names ++ s.names
  | .app "defVal" _ => []
  | .app "copyMem" (_ :: ts) => RawTerm.namesList ts
  | .app "addM" [m, _] => m.names
  -- a member, not a name read: `select(s, r)`, `store(s, r, v)`; and in the
  -- frame of a `select`, a path's root is a member too
  | .app "select" [s, .name _] => s.names
  | .app "store" [s, .name _, v] => s.names ++ v.names
  | .app "find" [s, p] => s.names ++ (if s.hasSelect then p.frameNames else p.names)
  | .app "save" [s, p, v] => s.names ++ (if s.hasSelect then p.frameNames else p.names) ++ v.names
  | .app "delAt" [s, p] => s.names ++ (if s.hasSelect then p.frameNames else p.names)
  | .app _ ts => RawTerm.namesList ts
  | .num _ | .env _ => []

def RawTerm.namesList : List RawTerm → List String
  | [] => []
  | t :: ts => t.names ++ RawTerm.namesList ts

/-- The names of a path in the frame of a `select`: its root is a member, not
a name. -/
def RawTerm.frameNames : RawTerm → List String
  | .name _ => []
  | .field t _ => t.frameNames
  | .at t i => t.frameNames ++ i.names
  | .atIn t i s => t.frameNames ++ i.names ++ s.names
  | t => t.names

/-- The term reads through a `select`: its paths are in a frame. -/
def RawTerm.hasSelect : RawTerm → Bool
  | .app "select" _ => true
  | .app _ ts => RawTerm.hasSelectList ts
  | .field t _ => t.hasSelect
  | .at a b | .add a b | .sub a b | .cmp _ a b | .arith _ a b => a.hasSelect || b.hasSelect
  | .atIn a b _ => a.hasSelect || b.hasSelect
  | .num _ | .name _ | .env _ => false

def RawTerm.hasSelectList : List RawTerm → Bool
  | [] => false
  | t :: ts => t.hasSelect || RawTerm.hasSelectList ts

end

def RawUpdElem.names : RawUpdElem → List String
  | .assign x t =>
    if x = "storage" || x = "memory" then t.names
    else if t matches .name "unset" then [x] else x :: t.names
  | .selfBalance _ a => a.names
  | .net r _ a => r.names ++ a.names
  | .pay r a | .netMt r a => r.names ++ a.names
  | .setBalance a => a.names

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
  | .decl ds φ =>
    let (u, d) := φ.names
    (u, RawStmt.declsList ds ++ d)

/-- The names a formula's updates bind to no path (`x := unset`): aliases,
so no `uint` parameters. -/
def RawFml.unsets : RawFml → List String
  | .all _ _ φ | .not φ | .modal _ _ φ | .decl _ φ => φ.unsets
  | .and φ ψ | .imp φ ψ => φ.unsets ++ ψ.unsets
  | .upd _ U φ =>
    U.filterMap (fun | .assign x (.name "unset") => some x | _ => none) ++ φ.unsets
  | _ => []

/-- A KeY `int` term by its syntax: a ledger read (`net(a)`, `net(x, a)`),
a name of `ks`, or `+`, `-`, `*` over one. -/
def RawTerm.isKintIn (ks : List String) : RawTerm → Bool
  | .app "net" _ | .app "toInt" _ => true
  | .name y => ks.contains y
  | .add a b | .sub a b | .arith .mul a b => a.isKintIn ks || b.isKintIn ks
  | _ => false

/-- The names a term reads as arithmetic operands: itself, or under `+`,
`-`, `*`. -/
def RawTerm.arithLeaves : RawTerm → List String
  | .name y => [y]
  | .add a b | .sub a b | .arith .mul a b => a.arithLeaves ++ b.arithLeaves
  | _ => []

/-- The names read as arithmetic operands of an equation or a comparison
over a KeY `int` (`isKintIn`). -/
def RawFml.kintLeaves (ks : List String) : RawFml → List String
  | .eq a b | .teq a b | .cmp _ a b =>
    if a.isKintIn ks || b.isKintIn ks then a.arithLeaves ++ b.arithLeaves else []
  | .all _ _ φ | .not φ | .upd _ _ φ | .modal _ _ φ | .decl _ φ => φ.kintLeaves ks
  | .and φ ψ | .imp φ ψ => φ.kintLeaves ks ++ ψ.kintLeaves ks
  | _ => []

/-- **The parameters of KeY's `int`** among `free`: a name read only as an
operand of KeY `int` arithmetic (beside a ledger read, `net(to) = x`), and
nowhere else (no program, update or other term reads it).  Such a parameter
ranges over KeY's unbounded `int`, as solkey's does; a parameter read
elsewhere too is a `uint`, and widened (`toInt`) where it meets a KeY
`int`, its type fixed by that other use. -/
def RawFml.kintParams (φ : RawFml) (free : List String) : List String :=
  let all := φ.names.1
  let step (ks : List String) : List String :=
    let ls := φ.kintLeaves ks
    free.filter fun x => ls.contains x && ls.count x == all.count x
  step (step (step []))

/-- The statements of every program in a formula. -/
def RawFml.stmts : RawFml → List RawStmt
  | .not φ | .upd _ _ φ | .all _ _ φ | .decl _ φ => φ.stmts
  | .and φ ψ | .imp φ ψ => φ.stmts ++ ψ.stmts
  | .modal _ P φ => P ++ φ.stmts
  | _ => []

/-! ## Elaboration -/

section Read

variable [FreshNames] (C : Contract)

/-- What a name stands for in a term. -/
inductive NameKind where
  | local | alias | mem | root | store

def nameKind (Γ : ECtx) (x : String) : NameKind :=
  match lookupBy x Γ with
  | some (.val ..) => .local
  | some (.alias _) => .alias
  | some (.mem _) => .mem
  | some .store => .store
  | some .kint => .local
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
  | .at t _ | .atIn t _ _ => do
    match ← pathTy Γ t with
    | .ref (.mapping _ V) => some V
    | .ref (.array E) => some E
    | _ => none
  | _ => none

/-- A type written as a term: `Person`, `uint[]`, `uint[3]`. -/
def RawTerm.toTy? : RawTerm → Option RawTy
  | .name S => some (.named S)
  | .app "[]" [t] => do pure (.array (← t.toTy?))
  | .at t (.num n) => do pure (.fixed (← t.toTy?) n)
  | _ => none

/-- The type `addM(m, T)` and `newArr(T, n)` allocate: a struct or an array. -/
def allocTy (T : RawTerm) : Except String RefTy := do
  let some T' := T.toTy? | throw "`addM(m, T)`: `T` is a type, `S`, `T[]` or `T[n]`"
  let .ref R ← elabTy C T' | throw "`addM(m, T)`: a value type is not allocated in memory"
  if (Ty.ref R).mapFree then pure R else throw "`addM(m, T)`: a mapping is not allocated in memory"

/-- The type of the memory object a term names, when the scope says: a memory
local, a reference member or element of one, a reference read, a fresh
identity. -/
def memTy (Γ : ECtx) : RawTerm → Option RefTy
  | .name x => match lookupBy x Γ with
    | some (.mem R) => some R
    | _ => none
  | .field t f => do
    let .struct s ← memTy Γ t | none
    let .ref R ← C.fieldType s f | none
    some R
  | .at t _ => do
    match ← memTy Γ t with
    | .array (.ref R) | .fixed (.ref R) _ => some R
    | _ => none
  | .app "read" [_, a] => memTy Γ a
  | .app "freshId" [.app "addM" [_, T]] => (allocTy C T).toOption
  | .app "freshId" [.app "copySt" [_, .app "newArr" [T, _]]] => (allocTy C T).toOption
  | .app "freshId" [.app "copySt" [_, .app "find" [_, p]]] => do
    let .ref R ← pathTy C Γ p | none
    some R
  | _ => none

/-- The struct whose members a storage term reads, if it is a `select`
(or a write over one): `select(storage, alice)` reads `Person`'s, and
`select(select(storage, alice), account)` `Account`'s. -/
partial def selectStruct? : RawTerm → Option Name
  | .app "select" [s, .name r] =>
    match selectStruct? s with
    | some S => match C.fieldType S r with
      | some (.ref (.struct S')) => some S'
      | _ => none
    | none => match C.rootType r with
      | some (.ref (.struct S)) => some S
      | _ => none
  | .app "save" (s :: _) | .app "delAt" (s :: _) | .app "store" (s :: _) => selectStruct? s
  | _ => none

/-- The readers of the eight sorts, each given the others: what a term of
one sort reads through a term of another.  They are one cycle (a value reads
a storage, a storage a path, a path a value index), tied once by `readers`
rather than as a `mutual` block, which the compiler handles badly at this
size.  Each reads a term by name (`NTm`): the scoped term it is where it
stands. -/
structure Readers (C : Contract) where
  val : RawTerm → Except String (NTerm C)
  path : RawTerm → Except String (NPTerm C)
  /-- A path in the frame of a `select` of the struct `S`: its root a member
  (`account.balance` under `select(storage, alice)`), where `path` would
  read a name. -/
  fpath : Name → RawTerm → Except String (NPTerm C)
  stor : RawTerm → Except String (NSTerm C)
  sval : RawTerm → Except String (NSValT C)
  ident : RawTerm → Except String (NITerm C)
  addr : RawTerm → Except String (NMAddr C)
  mem : RawTerm → Except String (NMTerm C)
  mval : RawTerm → Except String (NMValT C)

instance : Inhabited (Readers C) :=
  ⟨⟨fun _ => throw "", fun _ => throw "", fun _ _ => throw "", fun _ => throw "", fun _ => throw "",
    fun _ => throw "", fun _ => throw "", fun _ => throw "", fun _ => throw ""⟩⟩

/-- A path under the storage term `s`: in the frame of its `select`'s
struct, or from a root. -/
def pathIn (R : Readers C) (s p : RawTerm) : Except String (NPTerm C) :=
  match selectStruct? C s with
  | some S => R.fpath S p
  | none => R.path p

/-- A term at the value sort. -/
def rVal (R : Readers C) (Γ : ECtx) : RawTerm → Except String (NTerm C)
  | .num n => pure (.num n)
  | .name "true" => pure (.bool true)
  | .name "false" => pure (.bool false)
  | .name x =>
    match nameKind C Γ x with
    | .local => pure (NTm.pvV (Var.ofName x) (isK := lookupBy x Γ == some .kint))
    | .root => pure (.find .storage (.root x))
    | .alias => throw s!"`{x}` is a storage alias, not a value: read it with `find(storage, …)`"
    | .mem => throw s!"`{x}` is a memory reference, not a value"
    | .store => throw s!"`{x}` is a storage, not a value: read it with `find({x}, …)`"
  | .add a b => do pure (.binop .add (← R.val a) (← R.val b))
  | .sub a b => do pure (.binop .sub (← R.val a) (← R.val b))
  | .cmp op a b | .arith op a b => do pure (.binop op (← R.val a) (← R.val b))
  | .field p "length" => do
    if isMemTerm C Γ p then pure (.mlen .memory (← R.ident p))
    else pure (.len .storage (← R.path p))
  | t@(.field ..) | t@(.at ..) | t@(.atIn ..) => do
    if isMemTerm C Γ t then pure (.read .memory (← R.addr t))
    else pure (.find .storage (← R.path t))
  | .app "find" [s, .field p "length"] => do pure (.len (← R.stor s) (← pathIn C R s p))
  | .app "delValue" [t] => do pure (.delValue (← R.val t))
  | .app "wt" [s] => do pure (.wt (← R.stor s))
  | .app "select" [s, .name r] => do
    pure (.find (← R.stor s) (match selectStruct? C s with
      | some S => .member S r
      | none => .root r))
  | .app "select" [s, r] | .app "find" [s, r] => do pure (.find (← R.stor s) (← pathIn C R s r))
  | .app "read" [m, a] => do pure (.read (← R.mem m) (← R.addr a))
  | .app "net" [a] => do pure (.net (← R.val a))
  | .app "net" [.name x, a] => do pure (.netOf (Var.ofName x) (← R.val a))
  | .app "toInt" [a] => do
    let a ← R.val a
    pure (NTm.app1 .toInt a s!"toInt({a.text})")
  | .app "!" [t] => do pure (.unop .not (← R.val t))
  | .app "defVal" [.name "uint"] => pure (.lit (PrimTy.dflt .uint))
  | .app "defVal" [.name "int"] => pure (.lit (PrimTy.dflt .int))
  | .app "defVal" [.name "bool"] => pure (.lit (PrimTy.dflt .bool))
  | .app f _ => throw s!"`{f}(…)` is not a value term"
  | .env k => pure (.env k)

/-- A term at the storage-path sort. -/
def rPath (R : Readers C) (Γ : ECtx) : RawTerm → Except String (NPTerm C)
  | .name x =>
    match nameKind C Γ x with
    | .root => pure (.root x)
    | .mem => throw s!"`{x}` is a memory reference, not a storage path"
    | _ => pure (.pv (Var.ofName x))
  | .field t f => do pure (.field (← R.path t) f)
  | .at t i => do
    -- `p[p.length]`, the slot one past the end (a push's alias): no bounds check
    match i with
    | .field t' "length" =>
      if t == t' then pure (.next (← R.path t)) else pure (.at (← R.path t) (← R.val i))
    | _ => pure (.at (← R.path t) (← R.val i))
  | .atIn t i S => do
    -- `p[i]@S`, the index checked in `S`; `p[p.length]@S` the slot past the end
    match i with
    | .field t' "length" =>
      if t == t' then pure (.nextIn (← R.stor S) (← R.path t))
      else pure (.atIn (← R.stor S) (← R.path t) (← R.val i))
    | _ => pure (.atIn (← R.stor S) (← R.path t) (← R.val i))
  | _ => throw "not a storage path: a name, `p.f`, `p[t]` or `p[t]@S`"

/-- `rPath` in the frame of a `select`: a name that is no alias is a member, the frame's root. -/
def rPathFrame (R : Readers C) (Γ : ECtx) (S : Name) : RawTerm → Except String (NPTerm C)
  | .name x =>
    match nameKind C Γ x with
    | .mem => throw s!"`{x}` is a memory reference, not a storage path"
    | .alias | .store => pure (.pv (Var.ofName x))
    | _ => pure (.member S x)
  | .field t f => do pure (.field (← R.fpath S t) f)
  | .at t i => do
    -- `p[p.length]`, the slot one past the end (a push's alias): no bounds check
    match i with
    | .field t' "length" =>
      if t == t' then pure (.next (← R.fpath S t)) else pure (.at (← R.fpath S t) (← R.val i))
    | _ => pure (.at (← R.fpath S t) (← R.val i))
  | .atIn t i St => do
    match i with
    | .field t' "length" =>
      if t == t' then pure (.nextIn (← R.stor St) (← R.fpath S t))
      else pure (.atIn (← R.stor St) (← R.fpath S t) (← R.val i))
    | _ => pure (.atIn (← R.stor St) (← R.fpath S t) (← R.val i))
  | _ => throw "not a storage path: a name, `p.f`, `p[t]` or `p[t]@S`"

/-- A term at the storage sort; a push and a pop are nested
`save`s over the length. -/
def rStor (R : Readers C) (Γ : ECtx) : RawTerm → Except String (NSTerm C)
  | .name "storage" => pure .storage
  | .name "mtSt" => pure .mtSt
  | .name x =>
    if nameKind C Γ x matches .store then pure (.pv (Var.ofName x))
    else throw s!"`{x}` is not a storage: `storage`, or a variable an update binds to one"
  | .app "store" [s, .name r, v] => do pure (.save (← R.stor s) (.root r) (← R.sval v))
  | .app "save" [s, .field b "length", v] => do
    match s, v with
    | .app "save" [s', .at _ _, w], .add _ (.num 1) =>
      pure (.push (← R.stor s') (← R.path b) (← R.sval w))
    | .app "delAt" [s', .at _ _], .sub _ (.num 1) => pure (.pop (← R.stor s') (← R.path b))
    | _, .add _ (.num 1) => pure (.pushSlot (← R.stor s) (← R.path b))
    | _, .sub _ (.num 1) => pure (.shrink (← R.stor s) (← R.path b))
    | _, _ => throw "the length of an array is written by a push or a pop"
  | .app "save" [s, p, v] => do pure (.save (← R.stor s) (← pathIn C R s p) (← R.sval v))
  | .app "delAt" [s, p] => do pure (.delAt (← R.stor s) (← pathIn C R s p))
  | .app "select" [s, .name r] => do pure (.select (← R.stor s) r)
  | _ => throw "not a storage: `storage`, `store(s, r, v)`, `save(s, p, v)`, `delAt(s, p)` or \
      `select(s, r)`"

/-- What a storage `save` writes. -/
def rSVal (R : Readers C) (_Γ : ECtx) : RawTerm → Except String (NSValT C)
  | .app "find" [s, p] => do pure (.find (← R.stor s) (← pathIn C R s p))
  | .app "copyMem" [_, m, i] => do pure (.copyMem (← R.mem m) (← R.ident i))
  | .app "newArr" [T, n] => do pure (.newArr (← allocTy C T) (← R.val n))
  | .app "newArr" _ => throw "`newArr(n)` does not say what it allocates: write `newArr(T, n)`"
  | t => do pure (.val (← R.val t))

/-- A term at the memory-identity sort. -/
def rIdent (R : Readers C) (Γ : ECtx) : RawTerm → Except String (NITerm C)
  | .name x =>
    match nameKind C Γ x with
    | .root => throw s!"`{x}` is a state variable, not a memory reference"
    | _ => pure (.pv (Var.ofName x))
  | .field t f => do pure (.read .memory (.field (← R.ident t) f))
  | .at t k => do pure (.read .memory (.at (← R.ident t) (← R.val k)))
  | .app "read" [m, a] => do pure (.read (← R.mem m) (← R.addr a))
  | .app "freshId" [.app "addM" [m, T]] => do pure (.alloc (← R.mem m) (← allocTy C T))
  | .app "freshId" [.app "copySt" [m, v]] => do pure (.copy (← R.mem m) (← R.sval v))
  | .app "freshId" _ =>
    throw "not a fresh identity: `freshId(addM(m, T))` for a type `T`, or `freshId(copySt(m, v))`"
  | _ => throw "not a memory reference"

/-- A term at the memory-location sort: a member or an element. -/
def rAddr (R : Readers C) (_Γ : ECtx) : RawTerm → Except String (NMAddr C)
  | .field t f => do pure (.field (← R.ident t) f)
  | .at t k => do pure (.at (← R.ident t) (← R.val k))
  | _ => throw "not a memory location: `i.f` or `i[k]`"

/-- A term at the memory sort. -/
def rMem (R : Readers C) (_Γ : ECtx) : RawTerm → Except String (NMTerm C)
  | .name "memory" => pure .memory
  | .app "write" [m, a, v] => do pure (.write (← R.mem m) (← R.addr a) (← R.mval v))
  | .app "copySt" [m, v] => do pure (.copySt (← R.mem m) (← R.sval v))
  | .app "addM" [m, T] => do pure (.addM (← R.mem m) (← allocTy C T))
  | .app "addM" _ => throw "`addM(m)` does not say what it allocates: write `addM(m, T)` for a type `T`"
  | _ => throw "not a memory: `memory`, `write(m, a, v)`, `addM(m, T)` or `copySt(m, v)`"

/-- What a memory `write` writes: a memory local, a fresh identity or a read
of a reference (`memTy`) is a reference, anything else a value. -/
def rMVal (R : Readers C) (Γ : ECtx) : RawTerm → Except String (NMValT C)
  | t@(.name x) => do
    if nameKind C Γ x matches .mem then pure (.ref (← R.ident t)) else pure (.val (← R.val t))
  | t@(.app "freshId" _) => do pure (.ref (← R.ident t))
  | t => do
    if (memTy C Γ t).isSome then pure (.ref (← R.ident t)) else pure (.val (← R.val t))


/-- The readers, each calling the others through this record. -/
partial def readers (Γ : ECtx) : Readers C :=
  { val := fun t => rVal C (readers Γ) Γ t, path := fun t => rPath C (readers Γ) Γ t,
    fpath := fun S t => rPathFrame C (readers Γ) Γ S t,
    stor := fun t => rStor C (readers Γ) Γ t, sval := fun t => rSVal C (readers Γ) Γ t,
    ident := fun t => rIdent C (readers Γ) Γ t, addr := fun t => rAddr C (readers Γ) Γ t,
    mem := fun t => rMem C (readers Γ) Γ t, mval := fun t => rMVal C (readers Γ) Γ t }

/-- A term at the value sort. -/
def tVal (Γ : ECtx) (t : RawTerm) : Except String (NTerm C) := (readers C Γ).val t
/-- A term at the storage-path sort. -/
def tPath (Γ : ECtx) (t : RawTerm) : Except String (NPTerm C) := (readers C Γ).path t
/-- A path in the frame of a `select` of the struct `S`, its root a member. -/
def tFPath (Γ : ECtx) (S : Name) (t : RawTerm) : Except String (NPTerm C) := (readers C Γ).fpath S t
/-- A term at the storage sort. -/
def tStor (Γ : ECtx) (t : RawTerm) : Except String (NSTerm C) := (readers C Γ).stor t
/-- A term at the memory-identity sort. -/
def tIdent (Γ : ECtx) (t : RawTerm) : Except String (NITerm C) := (readers C Γ).ident t
/-- A term at the memory sort. -/
def tMem (Γ : ECtx) (t : RawTerm) : Except String (NMTerm C) := (readers C Γ).mem t

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
  | .block b | .unchecked b => b.attach.flatMap fun ⟨s, _⟩ => s.aliasHints
  | .whileLoop _ _ b | .loop _ _ b | .doWhile _ b _ => b.attach.flatMap fun ⟨s, _⟩ => s.aliasHints
  | .forLoop _ i _ u b => (i.attach.flatMap fun ⟨s, _⟩ => s.aliasHints) ++
      (b.attach.flatMap fun ⟨s, _⟩ => s.aliasHints) ++ u.attach.flatMap fun ⟨s, _⟩ => s.aliasHints
  | _ => []

/-- A parallel update, and the scope under it: `x := p` for a path `p` of
reference type binds `x` as an alias of that type, `x := i` for a memory
object `i` whose type the scope gives (`memTy`: `freshId(addM(memory, S))`,
`read(memory, carol.account)`, `carol`) binds it as a memory local of that
type, and `x := t` for a `bool` term `t` (`se1 := x <= 255`) as a `bool`
local, where `x` is a parameter.  Every right-hand side is read in the scope in front of the update. -/
def elabUpd (Γ : ECtx) : List RawUpdElem → Except String (List (NUpdElem C) × ECtx)
  | [] => pure ([], Γ)
  | .selfBalance op a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.selfBalance op (← tVal C Γ a) :: U', Γ')
  | .net r op a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.net (← tVal C Γ r) op (← tVal C Γ a) :: U', Γ')
  | .pay r a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.pay (← tVal C Γ r) (← tVal C Γ a) :: U', Γ')
  | .netMt r a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.netMt (← tVal C Γ r) (← tVal C Γ a) :: U', Γ')
  | .setBalance a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.setBalance (← tVal C Γ a) :: U', Γ')
  | .assign x t :: U => do
    let (U', Γ') ← elabUpd Γ U
    if x = "storage" then return (.storage (← tStor C Γ t) :: U', Γ')
    if x = "memory" then return (.memory (← tMem C Γ t) :: U', Γ')
    -- `oldNet := net`: a ledger variable, which `net(oldNet, a)` reads
    if (t matches .name "net") && (C.rootType "net").isNone then
      return (.saveNet (Var.ofName x) :: U', Γ')
    -- `oldNet := mtSt`: solkey's ledger snapshot of a deployment, the
    -- empty ledger (a storage variable otherwise, `old := mtSt`)
    if x = "oldNet" && (t matches .name "mtSt") then
      return (.saveNetMt (Var.ofName x) :: U', Γ')
    -- `lsv := unset`: an alias declared without a path (`storageLocalDeclSkip`);
    -- `x` is an alias, or a name not yet bound (an alias by its hints)
    if (t matches .name "unset") && (C.rootType "unset").isNone && (lookupBy "unset" Γ).isNone then
      let what? : Option String := match lookupBy x Γ with
        | some (.alias _) => none
        | some (.val ..) => some "a value local"
        | some (.mem _) => some "a memory local"
        | some .store => some "a storage variable"
        | some .kint => some "a KeY `int` local"
        | none => if (C.rootType x).isSome then some "a state variable" else none
      if let some what := what? then
        throw s!"`{x} := unset` binds a storage alias; `{x}` is {what}"
      return (.unset (Var.ofName x) :: U', Γ')
    -- `old := storage`: a storage variable
    if isStorTerm t then return (.store (Var.ofName x) (← tStor C Γ t) :: U', setBy x .store Γ')
    if let some (.ref R) := pathTy C Γ t then
      return (.path (Var.ofName x) (← tPath C Γ t) :: U', setBy x (.alias R) Γ')
    if (C.rootType x).isNone then
      if let some R := memTy C Γ t then
        return (.mref (Var.ofName x) (← tIdent C Γ t) :: U', setBy x (.mem R) Γ')
    if t matches .app "freshId" _ then return (.mref (Var.ofName x) (← tIdent C Γ t) :: U', Γ')
    match nameKind C Γ x with
    | .alias => return (.path (Var.ofName x) (← tPath C Γ t) :: U', Γ')
    | .mem => return (.mref (Var.ofName x) (← tIdent C Γ t) :: U', Γ')
    | .root => throw s!"`{x}` is a state variable: an update writes it through `storage := …`"
    | .store => throw s!"`{x}` is a storage variable: its right-hand side is a storage"
    | .local =>
      -- `se1 := x <= 255`, `se1 := find(storage, flags[a])`: a capture at the type of its
      -- right-hand side, which a program under it reads at that type (a `uint` otherwise)
      let free := lookupBy x Γ' matches none | some (.val .uint 256)
      let Γ' := if t.isKintIn (Γ.filterMap fun (y, u) => if u == .kint then some y else none) then
          if free then setBy x .kint Γ' else Γ'
        else match valTy? t with
        | some p => if p != .uint && free then setBy x (.val p) Γ' else Γ'
        | none => Γ'
      return (.val (Var.ofName x) (← tVal C Γ t) :: U', Γ')
where
  /-- A word's type, where the term shows it: a comparison, a negation, a
  literal, a local, a read of a storage word (`find(s, p)`, or the path
  bare). -/
  valTy? : RawTerm → Option PrimTy
    | .cmp .. | .app "!" _ | .name "true" | .name "false" => some .bool
    | .app "find" [_, q] => match pathTy C Γ q with
      | some (.prim p) => some p
      | _ => none
    | .name y => match lookupBy y Γ with
      | some (.val p _) => some p
      | some _ => none
      | none => match C.rootType y with
        | some (.prim p) => some p
        | _ => none
    | t => match pathTy C Γ t with
      | some (.prim p) => some p
      | _ => none
  /-- A storage term: `storage`, a storage variable, or a write over one. -/
  isStorTerm : RawTerm → Bool
    | .name "storage" | .name "mtSt" => true
    | .name y => (nameKind C Γ y matches .store)
    | .app "store" _ | .app "save" _ | .app "delAt" _ => true
    | _ => false

/-- The locals a program binds without declaring them, at the type their
right-hand side has: what symbolic execution leaves of a declaration once it
is dropped.  `carolAcc = carol.account;` (`memoryLocalDeclInitDrop` of
`Account memory carolAcc = carol.account;`) binds a memory local, `x = new
uint[](n);` one of the type it allocates; `sp1 = sp2.token;`
(`storageLocalDeclInitDrop`) and `sp = sp1.push();` a storage alias, through
another alias as well as from a state variable; `se1 = x <= 255;`
(`localValueDeclInitDrop` of a `bool` capture) a value local of the
expression's type, when that is not `uint`.  A right-hand side is typed in the
scope in front of the program, with the locals the program declares and binds
before it; a statement of either branch of an `if` counts.  A state variable,
a name the program declares, or one in scope as anything but a parameter (a
`uint`), is left alone: `alice = carol;` copies to storage, and `acc =
bob.account;` rebinds the alias `acc`.  (`RawStmt.aliasHints` types a
parameter from the contract alone, for the whole formula.) -/
partial def scopeHints (Γ : ECtx) (P : List RawStmt) : ECtx :=
  (go (RawStmt.declsList P) P (Γ, Γ)).1
where
  /-- What the program binds `x` to, if it may: none for a declared name, a
  state variable, or a local in scope that is no parameter. -/
  free (decls : List String) (Γ : ECtx) (x : String) : Bool :=
    !decls.contains x && (C.rootType x).isNone &&
      (lookupBy x Γ matches none | some (.val .uint 256))
  /-- The type `x = r;` gives `x`, `r` typed in `Δ`. -/
  ofRhs (Δ : ECtx) (r : RawExpr) : Option LocalTy :=
    match r with
    -- `x = new uint[](n);` says its type
    | .newArr T _ => match elabTy C T with
      | .ok (.ref R) => some (.mem R)
      | _ => none
    | _ => match synth C (ECtx.toNCtx Δ) r with
      | .ok (.mpath (.ref R) _) => some (.mem R)
      | .ok (.path (.ref R) _) => some (.alias R)
      | .ok (.val p _) => if p == .uint then none else some (.val p)
      | _ => none
  /-- The scope with the hints so far, and the one a right-hand side is typed in. -/
  go (decls : List String) : List RawStmt → ECtx × ECtx → ECtx × ECtx
    | [], acc => acc
    | s :: ss, (Γ, Δ) =>
      let hint (x : String) (t? : Option LocalTy) : ECtx × ECtx :=
        match t? with
        | some t => if free decls Γ x then (setBy x t Γ, setBy x t Δ) else (Γ, Δ)
        | none => (Γ, Δ)
      let declared (x : String) (T : RawTy) (mk : RefTy → LocalTy) : ECtx × ECtx :=
        match elabTy C T with
        | .ok (.ref R) => (Γ, setBy x (mk R) Δ)
        | _ => (Γ, Δ)
      let acc : ECtx × ECtx := match s with
        | .assign (.name x) r => hint x (ofRhs Δ r)
        -- `sp = sp1.push();`: the slot appended, an element of the array
        | .assignPush (.name x) b => hint x (match synth C (ECtx.toNCtx Δ) b with
          | .ok (.path (.ref (.array (.ref R))) _) => some (.alias R)
          | _ => none)
        | .declMemory T x _ => declared x T .mem
        | .declStorage T x _ | .declStoragePush T x _ => declared x T .alias
        | .decl T x _ | .send (some T) (.name x) _ _ => match elabDeclTy C T with
          | .ok (.prim p, n) => (Γ, setBy x (.val p n) Δ)
          | _ => (Γ, Δ)
        -- `ok = to.send(5);`: what a send returns, a `bool`
        | .send none (.name x) _ _ => hint x (some (.val .bool))
        | .ite _ t e => go decls e (go decls t (Γ, Δ))
        | .block b | .unchecked b => go decls b (Γ, Δ)
        | .whileLoop _ _ b | .loop _ _ b | .doWhile _ b _ => go decls b (Γ, Δ)
        | .forLoop _ i _ u b => go decls u (go decls b (go decls i (Γ, Δ)))
        -- `(uint a, , bool b) = …;`: each variable declared at its type
        | .tupleDecl vs _ => vs.foldl (fun (Γ, Δ) v => match v with
          | some (T, x) => match elabDeclTy C T with
            | .ok (.prim p, n) => (Γ, setBy x (.val p n) Δ)
            | _ => (Γ, Δ)
          | none => (Γ, Δ)) (Γ, Δ)
        | _ => (Γ, Δ)
      go decls ss acc

/-- The least index `k` or above that the formula does not write: what a
capture is numbered while a formula is read (`elabDlCN`). -/
def nextFree (taken : List Nat) (k : Nat) : Nat :=
  go taken.length k
where
  go : Nat → Nat → Nat
    | 0, k => k
    | n + 1, k => if taken.contains k then go n (k + 1) else k

/-- `a == b`: the operands typed as Solidity types them (the first that is
not a literal gives the type), then lowered. -/
def elabCompare (Γ : ECtx) (a b : RawExpr) : Except String (NTerm C × NTerm C) := do
  let Γn := ECtx.toNCtx Γ
  let t ← if a.isLit then synth C Γn b else synth C Γn a
  let some ⟨p, _⟩ := t.toVal? | throw "`==` compares values, not storage or memory references"
  pure (NTm.ofTm Γn.names (← check C Γn p a).lower, NTm.ofTm Γn.names (← check C Γn p b).lower)

/-- Run `x`, then restore the locals in scope (not the capture counter). -/
def inScope (x : ElabM α) : ElabM α := do
  let (Γ, _) ← get
  let r ← x
  modify fun (_, k) => (Γ, k)
  pure r

end Read

/-! ## `dl[C]{ … }` and `dl!{ … }` -/

/-- `dl[C]{ φ }`: the formula `φ`, its names resolved against the contract `C`. -/
syntax (name := dlAt) "dl[" term "]{ " dl_fml " }" : term

/-- `dl[C, m]{ φ }`: `dl[C]{ φ }` at the modality `m`, a Lean term (a
variable, `.box`, `.diamond`): `⟨[ P ]⟩ ψ` is `P` under `m`, and an update with
no modality under it is judged at `m`. -/
syntax (name := dlAtM) "dl[" term ", " term "]{ " dl_fml " }" : term

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

macro_rules
  | `(dl!{ $φ:dl_fml }) => `(dl[InContract.contract]{ $φ })
  | `(dl![ $m ]{ $φ:dl_fml }) => `(dl[InContract.contract, $m]{ $φ })

  | `(dl[ $c ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(dl[$c]{ ($[$as],* ⟹ $φ) })
  | `(dl[ $c, $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(dl[$c, $m]{ ($[$as],* ⟹ $φ) })
  | `(dl!{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(dl[InContract.contract]{ ($[$as],* ⟹ $φ) })
  | `(dl![ $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) =>
    `(dl[InContract.contract, $m]{ ($[$as],* ⟹ $φ) })

end Solidity
