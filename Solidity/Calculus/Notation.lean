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
  since terms are untyped: a state variable is a root, anything else a
  program variable (`pv`); a bare state variable or path in a value position
  is `find(storage, p)`;
* a name no program in the formula declares is a **parameter**, in scope
  everywhere: a `uint` local (mini-solkey's reading of a free name), or an
  alias when a program binds it to a storage path (`p = alice;`, which is
  what symbolic execution leaves of `Person storage p = alice;`).  A name
  some program declares is no parameter anywhere in the formula: outside
  that declaration's scope it is unknown (`checkFresh` would refuse the
  declaration of a parameter), so a free name and a declared one differ;
* `x := p` in an update, for a path `p` of reference type, binds `x` as an
  alias of that type for the formula under it, and `x := i`, for a memory
  object `i` of a type the scope gives (`freshId(addM(memory, Person))`,
  `freshId(addM(memory, uint[]))`, `read(memory, carol.account)`), as a
  memory local of that type, and `x := t`, for a `bool` term `t`
  (`se1 := x <= 255`), as a `bool` local;
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
  the clause for such a line (`copyDecls`); `Account storage p` and `uint v`
  declare the other kinds.

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
  /-- `a <= b`, `a < b` as a term: the right-hand side of a captured
  comparison, `x := a <= b`. -/
  | cmp (op : BinOp) (a b : RawTerm)
  /-- `a / b`: an operation on two `uint`s other than `+` and `-`. -/
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
  read as `Fml.slot i` and put back after (`fillSlots`). -/
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
  | .assign x t => if x = "storage" || x = "memory" then t.names else x :: t.names
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

/-- The statements of every program in a formula. -/
def RawFml.stmts : RawFml → List RawStmt
  | .not φ | .upd _ _ φ | .all _ _ φ | .decl _ φ => φ.stmts
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

def nameKind (Γ : ECtx) (x : String) : NameKind :=
  match lookupBy x Γ with
  | some (.val ..) => .local
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
  | .at t _ | .atIn t _ _ => do
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

/-- The readers of the eight sorts, each given the others: what a term of
one sort reads through a term of another.  They are one cycle (a value reads
a storage, a storage a path, a path a value index), tied once by `readers`
rather than as a `mutual` block, which the compiler handles badly at this
size. -/
structure Readers (C : Contract) where
  val : RawTerm → Except String (Term C)
  path : RawTerm → Except String (PTerm C)
  /-- A path in the frame of a `select`: its root a member (`account.balance`
  under `select(storage, alice)`), where `path` would read a name. -/
  fpath : RawTerm → Except String (PTerm C)
  stor : RawTerm → Except String (STerm C)
  sval : RawTerm → Except String (SValT C)
  ident : RawTerm → Except String (ITerm C)
  addr : RawTerm → Except String (MAddr C)
  mem : RawTerm → Except String (MTerm C)
  mval : RawTerm → Except String (MValT C)

instance : Inhabited (Readers C) :=
  ⟨⟨fun _ => throw "", fun _ => throw "", fun _ => throw "", fun _ => throw "", fun _ => throw "",
    fun _ => throw "", fun _ => throw "", fun _ => throw "", fun _ => throw ""⟩⟩

/-- A term at the value sort. -/
def rVal (R : Readers C) (Γ : ECtx) : RawTerm → Except String (Term C)
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
  | .add a b => do pure (.binop .add .uint (← R.val a) (← R.val b))
  | .sub a b => do pure (.binop .sub .uint (← R.val a) (← R.val b))
  | .cmp op a b | .arith op a b => do pure (.binop op .uint (← R.val a) (← R.val b))
  | .field p "length" => do
    if isMemTerm C Γ p then pure (.mlen .memory (← R.ident p))
    else pure (.len .storage (← R.path p))
  | t@(.field ..) | t@(.at ..) | t@(.atIn ..) => do
    if isMemTerm C Γ t then pure (.read .memory (← R.addr t))
    else pure (.find .storage (← R.path t))
  | .app "find" [s, .field p "length"] => do
    pure (.len (← R.stor s) (← (if s.hasSelect then R.fpath else R.path) p))
  | .app "delValue" [t] => do pure (.delValue (← R.val t))
  | .app "wt" [s] => do pure (.wt C.vars (← R.stor s))
  | .app "select" [s, .name r] => do pure (.find (← R.stor s) (.root r))
  | .app "select" [s, r] | .app "find" [s, r] => do
    pure (.find (← R.stor s) (← (if s.hasSelect then R.fpath else R.path) r))
  | .app "read" [m, a] => do pure (.read (← R.mem m) (← R.addr a))
  | .app "net" [a] => do pure (.net (← R.val a))
  | .app "net" [.name x, a] => do pure (.netOf (Var.ofName x) (← R.val a))
  | .app "!" [t] => do pure (.unop .not .bool (← R.val t))
  | .app "defVal" [.name "uint"] => pure (.lit (PrimTy.default .uint))
  | .app "defVal" [.name "int"] => pure (.lit (PrimTy.default .int))
  | .app "defVal" [.name "bool"] => pure (.lit (PrimTy.default .bool))
  | .app f _ => throw s!"`{f}(…)` is not a value term"
  | .env k => pure (.env k)

/-- A term at the storage-path sort. -/
def rPath (R : Readers C) (Γ : ECtx) : RawTerm → Except String (PTerm C)
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
def rPathFrame (R : Readers C) (Γ : ECtx) : RawTerm → Except String (PTerm C)
  | .name x =>
    match nameKind C Γ x with
    | .mem => throw s!"`{x}` is a memory reference, not a storage path"
    | .alias | .store => pure (.pv (Var.ofName x))
    | _ => pure (.root x)
  | .field t f => do pure (.field (← R.fpath t) f)
  | .at t i => do
    -- `p[p.length]`, the slot one past the end (a push's alias): no bounds check
    match i with
    | .field t' "length" =>
      if t == t' then pure (.next (← R.fpath t)) else pure (.at (← R.fpath t) (← R.val i))
    | _ => pure (.at (← R.fpath t) (← R.val i))
  | .atIn t i S => do
    match i with
    | .field t' "length" =>
      if t == t' then pure (.nextIn (← R.stor S) (← R.fpath t))
      else pure (.atIn (← R.stor S) (← R.fpath t) (← R.val i))
    | _ => pure (.atIn (← R.stor S) (← R.fpath t) (← R.val i))
  | _ => throw "not a storage path: a name, `p.f`, `p[t]` or `p[t]@S`"

/-- A term at the storage sort; a push and a pop are nested
`save`s over the length. -/
def rStor (R : Readers C) (Γ : ECtx) : RawTerm → Except String (STerm C)
  | .name "storage" => pure .storage
  | .name "mtSt" => pure (.mtSt C.vars)
  | .name x =>
    if nameKind C Γ x matches .store then pure (.pv (Var.ofName x))
    else throw s!"`{x}` is not a storage: `storage`, or a variable an update binds to one"
  | .app "store" [s, .name r, v] => do pure (.save (← R.stor s) (.root r) (← R.sval v))
  | .app "save" [s, .field b "length", v] => do
    match s, v with
    | .app "save" [s', .at _ _, w], .add _ (.num 1) =>
      pure (.push (← R.stor s') (← R.path b) (← R.sval w))
    | .app "delAt" [s', .at _ _], .add _ (.num 1) =>
      pure (.pushSlot (← R.stor s') (← R.path b) (← elemTy C Γ b))
    | .app "delAt" [s', .at _ _], .sub _ (.num 1) => pure (.pop (← R.stor s') (← R.path b))
    | _, .add _ (.num 1) => pure (.extend (← R.stor s) (← R.path b) (← elemTy C Γ b))
    | _, .sub _ (.num 1) => pure (.shrink (← R.stor s) (← R.path b))
    | _, _ => throw "the length of an array is written by a push or a pop"
  | .app "save" [s, p, v] => do
    pure (.save (← R.stor s) (← (if s.hasSelect then R.fpath else R.path) p) (← R.sval v))
  | .app "delAt" [s, p] => do pure (.delAt (← R.stor s) (← (if s.hasSelect then R.fpath else R.path) p))
  | .app "select" [s, .name r] => do pure (.select (← R.stor s) r)
  | _ => throw "not a storage: `storage`, `store(s, r, v)`, `save(s, p, v)`, `delAt(s, p)` or \
      `select(s, r)`"

/-- What a storage `save` writes. -/
def rSVal (R : Readers C) (_Γ : ECtx) : RawTerm → Except String (SValT C)
  | .app "find" [s, p] => do pure (.find (← R.stor s) (← (if s.hasSelect then R.fpath else R.path) p))
  | .app "copyMem" [_, m, i] => do pure (.copyMem (← R.mem m) (← R.ident i))
  | .app "newArr" [T, n] => do pure (.newArr (← allocTy C T) (← R.val n))
  | .app "newArr" _ => throw "`newArr(n)` does not say what it allocates: write `newArr(T, n)`"
  | t => do pure (.val (← R.val t))

/-- A term at the memory-identity sort. -/
def rIdent (R : Readers C) (Γ : ECtx) : RawTerm → Except String (ITerm C)
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
def rAddr (R : Readers C) (_Γ : ECtx) : RawTerm → Except String (MAddr C)
  | .field t f => do pure (.field (← R.ident t) f)
  | .at t k => do pure (.at (← R.ident t) (← R.val k))
  | _ => throw "not a memory location: `i.f` or `i[k]`"

/-- A term at the memory sort. -/
def rMem (R : Readers C) (_Γ : ECtx) : RawTerm → Except String (MTerm C)
  | .name "memory" => pure .memory
  | .app "write" [m, a, v] => do pure (.write (← R.mem m) (← R.addr a) (← R.mval v))
  | .app "copySt" [m, v] => do pure (.copySt (← R.mem m) (← R.sval v))
  | .app "addM" [m, T] => do pure (.addM (← R.mem m) (← allocTy C T))
  | .app "addM" _ => throw "`addM(m)` does not say what it allocates: write `addM(m, T)` for a type `T`"
  | _ => throw "not a memory: `memory`, `write(m, a, v)`, `addM(m, T)` or `copySt(m, v)`"

/-- What a memory `write` writes: a memory local, a fresh identity or a read
of a reference (`memTy`) is a reference, anything else a value. -/
def rMVal (R : Readers C) (Γ : ECtx) : RawTerm → Except String (MValT C)
  | t@(.name x) => do
    if nameKind C Γ x matches .mem then pure (.ref (← R.ident t)) else pure (.val (← R.val t))
  | t@(.app "freshId" _) => do pure (.ref (← R.ident t))
  | t => do
    if (memTy C Γ t).isSome then pure (.ref (← R.ident t)) else pure (.val (← R.val t))


/-- The readers, each calling the others through this record. -/
partial def readers (Γ : ECtx) : Readers C :=
  { val := fun t => rVal C (readers Γ) Γ t, path := fun t => rPath C (readers Γ) Γ t,
    fpath := fun t => rPathFrame C (readers Γ) Γ t,
    stor := fun t => rStor C (readers Γ) Γ t, sval := fun t => rSVal C (readers Γ) Γ t,
    ident := fun t => rIdent C (readers Γ) Γ t, addr := fun t => rAddr C (readers Γ) Γ t,
    mem := fun t => rMem C (readers Γ) Γ t, mval := fun t => rMVal C (readers Γ) Γ t }

/-- A term at the value sort. -/
def tVal (Γ : ECtx) (t : RawTerm) : Except String (Term C) := (readers C Γ).val t
/-- A term at the storage-path sort. -/
def tPath (Γ : ECtx) (t : RawTerm) : Except String (PTerm C) := (readers C Γ).path t
/-- A path in the frame of a `select`, its root a member. -/
def tFPath (Γ : ECtx) (t : RawTerm) : Except String (PTerm C) := (readers C Γ).fpath t
/-- A term at the storage sort. -/
def tStor (Γ : ECtx) (t : RawTerm) : Except String (STerm C) := (readers C Γ).stor t
/-- What a storage `save` writes. -/
def tSVal (Γ : ECtx) (t : RawTerm) : Except String (SValT C) := (readers C Γ).sval t
/-- A term at the memory-identity sort. -/
def tIdent (Γ : ECtx) (t : RawTerm) : Except String (ITerm C) := (readers C Γ).ident t
/-- A term at the memory-location sort. -/
def tAddr (Γ : ECtx) (t : RawTerm) : Except String (MAddr C) := (readers C Γ).addr t
/-- A term at the memory sort. -/
def tMem (Γ : ECtx) (t : RawTerm) : Except String (MTerm C) := (readers C Γ).mem t
/-- What a memory `write` writes. -/
def tMVal (Γ : ECtx) (t : RawTerm) : Except String (MValT C) := (readers C Γ).mval t

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
  | _ => []

/-- A parallel update, and the scope under it: `x := p` for a path `p` of
reference type binds `x` as an alias of that type, `x := i` for a memory
object `i` whose type the scope gives (`memTy`: `freshId(addM(memory, S))`,
`read(memory, carol.account)`, `carol`) binds it as a memory local of that
type, and `x := t` for a `bool` term `t` (`se1 := x <= 255`) as a `bool`
local, where `x` is a parameter.  Every right-hand side is read in the scope in front of the update. -/
def elabUpd (Γ : ECtx) : List RawUpdElem → Except String (Upd C × ECtx)
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
      -- `se1 := x <= 255`: a `bool` capture, which a program under it reads as one
      let Γ' := if isBool t && (lookupBy x Γ' matches none | some (.val .uint 256)) then
        setBy x (.val .bool) Γ' else Γ'
      return (.val (Var.ofName x) (← tVal C Γ t) :: U', Γ')
where
  /-- A `bool` term: a comparison, a negation, a literal, a `bool` local. -/
  isBool : RawTerm → Bool
    | .cmp .. | .app "!" _ | .name "true" | .name "false" => true
    | .name y => (lookupBy y Γ matches some (.val .bool _))
    | _ => false
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
    | _ => match synth C Δ r with
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
        | .assignPush (.name x) b => hint x (match synth C Δ b with
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
        -- `(uint a, , bool b) = …;`: each variable declared at its type
        | .tupleDecl vs _ => vs.foldl (fun (Γ, Δ) v => match v with
          | some (T, x) => match elabDeclTy C T with
            | .ok (.prim p, n) => (Γ, setBy x (.val p n) Δ)
            | _ => (Γ, Δ)
          | none => (Γ, Δ)) (Γ, Δ)
        | _ => (Γ, Δ)
      go decls ss acc

/-- The least index `k` or above that the formula does not write: what a
capture is numbered while a formula is read (`elabDl`). -/
def nextFree (taken : List Nat) (k : Nat) : Nat :=
  go taken.length k
where
  go : Nat → Nat → Nat
    | 0, k => k
    | n + 1, k => if taken.contains k then go n (k + 1) else k

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
declarations are in scope in its postcondition.  `taken` are the indices of
the fresh variables the formula writes: a capture the program makes while it
is read takes the least index above the last that none of them has
(`nextFree`), statement by statement; a statement whose captures would run
into a written index is numbered past them all. -/
def elabFml (taken : List Nat) : RawFml → ElabM (Fml C)
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
    pure (.all (Var.ofName x) p (← elabFml taken φ))
  | .not φ => do pure (.not (← inScope (elabFml taken φ)))
  | .and φ ψ => do pure (.and (← inScope (elabFml taken φ)) (← inScope (elabFml taken ψ)))
  | .imp φ ψ => do pure (.imp (← inScope (elabFml taken φ)) (← inScope (elabFml taken ψ)))
  | .upd m U φ => inScope do
    let (Γ, k) ← get
    let (U', Γ') ← elabUpd C Γ U
    set (Γ', k)
    pure (.upd m U' (← elabFml taken φ))
  | .modal m P φ => inScope do
    modify fun (Γ, k) => (scopeHints C Γ P, k)
    let mut P' : Prog C := []
    for s in P do
      let (Γ, k) ← get
      let k₀ := nextFree taken k
      set (Γ, k₀)
      let mut Q ← elabStmt C s
      let (_, k₁) ← get
      -- captures that would run into a written index: past them all
      if (List.range' k₀ (k₁ - k₀)).any taken.contains then
        set (Γ, max k (taken.foldl max 0 + 1))
        Q ← elabStmt C s
      P' := P' ++ Q
    pure (.modal m P' (← elabFml taken φ))
  | .lean i => pure (Fml.slot i)
  | .decl ds φ => inScope do
    for d in ds do
      let (x, t) ← match d with
        | .declMemory T x none => do
          let .ref R ← ElabM.lift (elabTy C T) | throw s!"`{x}`: a memory local is of a reference type"
          pure (x, LocalTy.mem R)
        | .declStorage T x none => do
          let .ref R ← ElabM.lift (elabTy C T) | throw s!"`{x}`: a storage alias is of a reference type"
          pure (x, LocalTy.alias R)
        | .decl T x none => do
          let .prim p ← ElabM.lift (elabTy C T) | throw s!"`{x}`: a local without a location is a value"
          pure (x, LocalTy.val p)
        | _ => throw "`where` declares locals: `Person memory carol`, `Account storage p`, `uint v`"
      modify fun (Γ, k) => (setBy x t Γ, k)
    elabFml taken φ

/-- Elaborate a formula against `C`.  Its parameters (the names nothing
declares) are in scope from the start: an alias if a program binds one to a
storage path, else a `uint` local.  A capture takes the least index no fresh
variable the formula writes has (`elabFml`): a line of a derivation leaves a
gap exactly where the elaborator numbered a capture it does not show, the
locals of a callee its call statement carries.  With `pastAll`, a capture
is numbered past every written index instead: a Lean formula in the formula
(`‹…›`) may write fresh variables the reading does not see (`elabDlAt`). -/
def elabDl (φ : RawFml) (pastAll : Bool := false) : Except String (Fml C) :=
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
  let taken := ((used ++ declared).map fun x => (Var.ofName x).idx).filter (· > 0)
  let taken := if pastAll then List.range' 1 (taken.foldl max 0) else taken
  ((elabFml C taken φ).run { funs := C.funs }).run' (params, 1)

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
  -- a hole that is no postcondition (`φ : Post C` writes no fresh variable)
  -- may write fresh variables the reading cannot see: captures are then
  -- numbered past every written index
  let opaqueHole ← holes.anyM fun h => do
    let some t := fmlHole? h | return true
    withoutModifyingState do
      try
        let e ← withoutErrToSorry <| withoutAutoBoundImplicit <| elabTerm t none
        return !(← whnfR (← inferType e)).isAppOf `Solidity.Post
      catch _ => return true
  let pastAll := quote opaqueHole
  let read (μ : Option Lean.Name) : TermElabM Lean.Term :=
    liftMacroM (expandFml { either := μ.map fun n => (mkCIdent n : Lean.Term), holes } φ)
  let once (μ : Option Lean.Name) : TermElabM Lean.Expr := do
    let raw ← read μ
    elabAgainst c fun q => `((elabDl $c $raw $pastAll).map (Fml.quote $q))
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
          `((do pure (Fml.and (← elabDl $c $rd $pastAll) (← elabDl $c $rb $pastAll))).map
              (Fml.quote $q))
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

/-- `st!{ s }`, `pt!{ p }`: a storage term and a storage path read against the
file's contract, as `dl!{ … }` reads them: the operands of a law's premise
(`STerm.KindFreeAt st!{ save(storage, alice.age, 1) } pt!{ alice }`).  The path
is read as in the frame of a `select`: its root may be a member (`account`). -/
syntax "st!{ " dl_term " }" : term
@[inherit_doc «termSt!{_}»] syntax "pt!{ " dl_term " }" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(st!{ $t:dl_term }) => do
    let raw ← liftMacroM (expandTerm t)
    let c ← `(InContract.contract)
    elabAgainst c fun q => `((tStor $c [] $raw).map (Tm.quote $q))
  | `(pt!{ $t:dl_term }) => do
    let raw ← liftMacroM (expandTerm t)
    let c ← `(InContract.contract)
    elabAgainst c fun q => `((tFPath $c [] $raw).map (Tm.quote $q))

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

/-- A capture takes the least index the formula's fresh variables leave. -/
example : dl!{ ⟨ values[total + 1] += 2; ⟩ ie1 == 0 } =
    dl!{ ⟨ uint ie2 = total + 1; values[ie2] += 2; ⟩ ie1 == 0 } := rfl
example : dl!{ ⟨ values[total + 1] += 2; ⟩ ie3 == 0 } =
    dl!{ ⟨ uint ie1 = total + 1; values[ie1] += 2; ⟩ ie3 == 0 } := rfl

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

/-! ### Memory objects -/

/-- What `Person memory carol;` leaves reads back, and binds `carol` as a
`Person` in memory under it. -/
example : (dl!{ ⟨ Person memory carol; carol.age = 5; ⟩ true }).step =
    some dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
      ⟨ carol.age = 5; ⟩ true } := rfl

/--
info: dl{
  { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
    ⟨ carol.age = 5; ⟩ true } : Fml StandardExample
-/
#guard_msgs in
#check dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
  ⟨ carol.age = 5; ⟩ true }

/-- A dropped memory declaration: `carolAcc` is typed from `carol.account`
(`scopeHints`), and a read of a reference binds a memory local. -/
example : Fml StandardExample :=
  dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       ⟨ carolAcc = carol.account; carolAcc.balance = 1; ⟩ true }
example : Fml StandardExample :=
  dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       { carolAcc := read(memory, carol.account) } ⟨ carolAcc.balance = 1; ⟩ true }

/-- … with the memory locals the program declares before it, in a branch too. -/
example : Fml StandardExample :=
  dl!{ ⟨ Person memory d; if (a == 1) { acc = d.account; } else { acc = d.account; }; acc.balance = 1; ⟩
       true }

/-- A state variable is no memory local: `alice = carol;` copies to storage. -/
example : (dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
    ⟨ alice = carol; ⟩ true }).step =
    some dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
      { storage := save(storage, alice, copyMem(mtSt, memory, carol)) } ⟨⟩ true } := rfl

/-- A name the program declares is left to its declaration. -/
example : Fml StandardExample :=
  dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       ⟨ Person memory d; d = carol; ⟩ true }

/-- An array's allocation carries its type, as a struct's does. -/
example : (dl!{ ⟨ uint[] memory xs; xs[0] = 5; ⟩ true }).step =
    some dl!{ { xs := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) }
      ⟨ xs[0] = 5; ⟩ true } := rfl

/-- info: dl{ { ts := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) } true } : Fml StandardExample -/
#guard_msgs in
#check dl!{ { ts := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) } true }

/-- `new` says what it allocates, so its local is a memory array
(`scopeHints`), and the copy it leaves says so too. -/
example : (dl!{ ⟨ uint[] memory xs = new uint[](3); ⟩ true }).step =
    some dl!{ ⟨ xs = new uint[](3); ⟩ true } := rfl
example : symex 3 dl!{ ⟨ uint[] memory xs = new uint[](3); ⟩ true } =
    dl!{ { xs := freshId(copySt(memory, newArr(uint[], 3))) ‖ memory := copySt(memory, newArr(uint[], 3)) }
      true } := rfl

/--
info: dl{
  { xs := freshId(copySt(memory, newArr(uint[], 3))) ‖ memory := copySt(memory, newArr(uint[], 3)) }
    true } : Fml StandardExample
-/
#guard_msgs in
#check dl!{ { xs := freshId(copySt(memory, newArr(uint[], 3))) ‖ memory := copySt(memory, newArr(uint[], 3)) }
  true }

/-- `carol = alice;` is a memory copy only by `carol`'s declaration, which a
line that dropped it carries after `where`. -/
example : (dl!{ ⟨ Person memory carol = alice; carol.age = 1; ⟩ true }).step =
    some dl!{ ⟨ carol = alice; carol.age = 1; ⟩ true where Person memory carol } := rfl
example : (dl!{ ⟨ Person storage carol = alice; carol.age = 1; ⟩ true }).step =
    some dl!{ ⟨ carol = alice; carol.age = 1; ⟩ true } := rfl

/-- info: dl{ ⟨ carol = alice; carol.age = 1; ⟩ true where Person memory carol } : Fml StandardExample -/
#guard_msgs in #check dl!{ ⟨ carol = alice; carol.age = 1; ⟩ true where Person memory carol }

/--
info: dl{
  { sp2 := alice.account } ⟨ acc = sp2; ⟩ read(memory, acc.balance) = 1 where Account memory acc } : Fml StandardExample
-/
#guard_msgs in #check dl!{ { sp2 := alice.account } ⟨ acc = sp2; ⟩ acc.balance == 1
  where Account memory acc }

-- An allocation reads back at a struct or an array only.
/-- error: Solidity elaboration failed: `addM(m, T)`: a value type is not allocated in memory -/
#guard_msgs in #check dl!{ { memory := addM(memory, uint) } true }

/--
error: Solidity elaboration failed: `addM(m)` does not say what it allocates: write `addM(m, T)` for a type `T`
-/
#guard_msgs in #check dl!{ { memory := addM(memory) } true }

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
