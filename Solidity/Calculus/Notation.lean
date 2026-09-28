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
shows reads back through `dl[C]{ φ }` (or `dl!{ φ }`) as the formula it is.
The reading is mini-solkey's: the macros build a raw formula, `elabDl`
resolves its names at compile time (`elabAgainst`, as `sol[C]{ … }` does),
and `Fml.quote` (`Quote.lean`) splices the result.

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

What does not read back: `‹…›` (a Lean term, which is also how a
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
  | transfer (r a : RawTerm)
  deriving Repr, Inhabited

/-- A formula as written.  `peq`/`pne` compare program expressions (`==`, `!=`). -/
inductive RawFml where
  | tt
  | eq (a b : RawTerm)
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
  | upd (U : List RawUpdElem) (φ : RawFml)
  | modal (m : Modality) (P : List RawStmt) (φ : RawFml)
  deriving Repr, Inhabited

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
        | [] => pure (← `(RawTerm.name $(quote root)), flds)
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
    | `(dl_upd_elem| transfer($r, $a)) =>
      `(RawUpdElem.transfer $(← expandTerm r) $(← expandTerm a))
    | `(dl_upd_elem| $l:dl_term := $r:dl_term) =>
      let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
      let [n] := nameParts x.getId | Macro.throwErrorAt l "an update assigns a variable"
      `(RawUpdElem.assign $(quote n) $(← expandTerm r))
    | _ => Macro.throwUnsupported
  `([$elems,*])

partial def expandFml : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| true) => `(RawFml.tt)
  | `(dl_fml| false) => `(RawFml.not RawFml.tt)
  | `(dl_fml| $a:dl_term = $b:dl_term) => do `(RawFml.eq $(← expandTerm a) $(← expandTerm b))
  | `(dl_fml| $a:dl_term == $b:dl_term) => do
      `(RawFml.peq $(← expandOperand a) $(← expandOperand b))
  | `(dl_fml| $a:dl_term != $b:dl_term) => do
      `(RawFml.pne $(← expandOperand a) $(← expandOperand b))
  | `(dl_fml| $a:dl_term < $b:dl_term) => cmp ``BinOp.lt a b
  | `(dl_fml| $a:dl_term <= $b:dl_term) => cmp ``BinOp.le a b
  | `(dl_fml| $a:dl_term > $b:dl_term) => cmp ``BinOp.gt a b
  | `(dl_fml| $a:dl_term >= $b:dl_term) => cmp ``BinOp.ge a b
  | `(dl_fml| ∀ $T:ident $x:ident; $φ:dl_fml) => do
      `(RawFml.all $(← specSort T) $(quote x.getId.toString) $(← expandFml φ))
  | `(dl_fml| ¬ $φ:dl_fml) => do `(RawFml.not $(← expandFml φ))
  | `(dl_fml| $φ:dl_fml ∧ $ψ:dl_fml) | `(dl_fml| $φ:dl_fml && $ψ:dl_fml) => do
      `(RawFml.and $(← expandFml φ) $(← expandFml ψ))
  | `(dl_fml| $φ:dl_fml → $ψ:dl_fml) => do `(RawFml.imp $(← expandFml φ) $(← expandFml ψ))
  | `(dl_fml| $U:dl_upd $φ:dl_fml) => do `(RawFml.upd $(← expandUpd U) $(← expandFml φ))
  | `(dl_fml| ⟨ $[$ss:sol_stmt;]* ⟩ $φ:dl_fml) => do
      `(RawFml.modal .diamond [$(← ss.mapM expandStmt),*] $(← expandFml φ))
  | `(dl_fml| [ $[$ss:sol_stmt;]* ] $φ:dl_fml) => do
      `(RawFml.modal .box [$(← ss.mapM expandStmt),*] $(← expandFml φ))
  | stx@`(dl_fml| ⟨[ $[$_:sol_stmt;]* ]⟩ $_:dl_fml) =>
      Macro.throwErrorAt stx "`⟨[ … ]⟩` stands for either modality, in a taclet: write `⟨ … ⟩` or `[ … ]`"
  | stx@`(dl_fml| ⟨ $_:sol_block ⟩ $_:dl_fml) | stx@`(dl_fml| [ $_:sol_block ] $_:dl_fml) =>
      Macro.throwErrorAt stx "a program that is a schema variable belongs to `dl{ … }`"
  | `(dl_fml| ( $φ:dl_fml )) => expandFml φ
  | stx@`(dl_fml| ‹ $_:term ›) => noEscape stx
  | _ => Macro.throwUnsupported
where
  cmp (op : Lean.Name) (a b : TSyntax `dl_term) : MacroM Lean.Term := do
    `(RawFml.cmp $(mkIdent op) $(← expandTerm a) $(← expandTerm b))

end Expand

/-! ## Names -/

/-- The names a raw expression reads. -/
def RawExpr.names : RawExpr → List String
  | .name x => [x]
  | .field e _ | .unop _ e | .incDec _ e | .newArr _ e => e.names
  | .index a b | .binop _ a b => a.names ++ b.names
  | .ternary c a b => c.names ++ a.names ++ b.names
  | .call _ as => as.attach.flatMap fun ⟨a, _⟩ => a.names
  | .named _ _ as => as.attach.flatMap fun ⟨a, _⟩ => a.names
  | .num _ | .bool _ | .env _ => []

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

mutual

/-- The names a raw statement reads. -/
def RawStmt.names : RawStmt → List String
  | .assign l r | .assignPush l r | .opAssign _ l r | .assignIncDec l _ r => l.names ++ r.names
  | .decl _ _ i | .declStorage _ _ i | .declMemory _ _ i => (i.map RawExpr.names).getD []
  | .declStoragePush _ _ b | .delete b | .incDec _ b | .require b | .assert b => b.names
  -- a function's name is not a name the formula reads
  | .call (.name _) as => (as.map RawExpr.names).flatten
  | .call f as => f.names ++ (as.map RawExpr.names).flatten
  | .ite c t e => c.names ++ RawStmt.namesList t ++ RawStmt.namesList e
  | .ret e => (e.map RawExpr.names).getD []
  | .revert => []
  | .eval as => (as.map RawExpr.names).flatten
  | .unchecked b => RawStmt.namesList b

def RawStmt.namesList : List RawStmt → List String
  | [] => []
  | s :: ss => s.names ++ RawStmt.namesList ss

end

mutual

/-- The names a raw statement declares, in either branch of an `if`. -/
def RawStmt.decls : RawStmt → List String
  | .decl _ x _ | .declStorage _ x _ | .declMemory _ x _ | .declStoragePush _ x _ => [x]
  | .ite _ t e => RawStmt.declsList t ++ RawStmt.declsList e
  | .unchecked b => RawStmt.declsList b
  | _ => []

def RawStmt.declsList : List RawStmt → List String
  | [] => []
  | s :: ss => s.decls ++ RawStmt.declsList ss

end

def RawUpdElem.names : RawUpdElem → List String
  | .assign x t => if x = "storage" || x = "memory" then t.names else x :: t.names
  | .transfer r a => r.names ++ a.names

/-- The names a raw formula mentions, and those its programs declare. -/
def RawFml.names : RawFml → List String × List String
  | .tt => ([], [])
  | .eq a b => (a.names ++ b.names, [])
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
  | .upd U φ =>
    let (u, d) := φ.names
    ((U.map RawUpdElem.names).flatten ++ u, d)
  | .modal _ P φ =>
    let (u, d) := φ.names
    (RawStmt.namesList P ++ u, RawStmt.declsList P ++ d)

/-- The statements of every program in a formula. -/
def RawFml.stmts : RawFml → List RawStmt
  | .not φ | .upd _ φ | .all _ _ φ => φ.stmts
  | .and φ ψ | .imp φ ψ => φ.stmts ++ ψ.stmts
  | .modal _ P φ => P ++ φ.stmts
  | _ => []

/-- The modality of the formula under an update: an update is judged as the
goal it came from (`fmlModality?` of the schema reader). -/
def RawFml.modality : RawFml → Modality
  | .modal m _ _ => m
  | .upd _ φ => φ.modality
  | _ => .diamond

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

mutual

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
  | .ite _ t e => RawStmt.aliasHintsList t ++ RawStmt.aliasHintsList e
  | _ => []

def RawStmt.aliasHintsList : List RawStmt → List (String × RefTy)
  | [] => []
  | s :: ss => s.aliasHints ++ RawStmt.aliasHintsList ss

end

/-- A parallel update, and the scope under it: `x := p` for a path `p` of
reference type binds `x` as an alias of that type.  Every right-hand side is
read in the scope in front of the update. -/
def elabUpd (Γ : ECtx) : List RawUpdElem → Except String (Upd C × ECtx)
  | [] => pure ([], Γ)
  | .transfer r a :: U => do
    let (U', Γ') ← elabUpd Γ U
    pure (.transfer (← tVal C Γ r) (← tVal C Γ a) :: U', Γ')
  | .assign x t :: U => do
    let (U', Γ') ← elabUpd Γ U
    if x = "storage" then return (.storage (← tStor C Γ t) :: U', Γ')
    if x = "memory" then return (.memory (← tMem C Γ t) :: U', Γ')
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
    pure (.eq (← tVal C Γ a) (← tVal C Γ b))
  | .peq a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.eq a b)
  | .pne a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.not (.eq a b))
  | .cmp op a b => do
    let (Γ, _) ← get
    pure (.eq (.binop op .uint (← tVal C Γ a) (← tVal C Γ b)) (.lit (.bool true)))
  | .all p x φ => inScope do
    modify fun (Γ, k) => (setBy x (.val p) Γ, k)
    pure (.all (Var.ofName x) p (← elabFml φ))
  | .not φ => do pure (.not (← inScope (elabFml φ)))
  | .and φ ψ => do pure (.and (← inScope (elabFml φ)) (← inScope (elabFml ψ)))
  | .imp φ ψ => do pure (.imp (← inScope (elabFml φ)) (← inScope (elabFml ψ)))
  | .upd U φ => inScope do
    let (Γ, k) ← get
    let (U', Γ') ← elabUpd C Γ U
    set (Γ', k)
    pure (.upd φ.modality U' (← elabFml φ))
  | .modal m P φ => inScope do
    let P' ← elabStmts C P
    pure (.modal m P' (← elabFml φ))

/-- Elaborate a formula against `C`.  Its parameters (the names nothing
declares) are in scope from the start: an alias if a program binds one to a
storage path, else a `uint` local.  A capture is numbered past every fresh
variable the formula writes. -/
def elabDl (φ : RawFml) : Except String (Fml C) :=
  let (used, declared) := φ.names
  let hints := RawStmt.aliasHintsList C φ.stmts
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

/-! ## `dl[C]{ … }` and `dl!{ … }` -/

/-- `dl[C]{ φ }`: the formula `φ`, its names resolved against the contract `C`. -/
syntax "dl[" term "]{ " dl_fml " }" : term

/-- `dl!{ φ }`: `dl[C]{ φ }` for the file's `InContract` contract.  (`dl{ φ }`
is the schema reading.) -/
syntax "dl!{ " dl_fml " }" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(dl[ $c ]{ $φ:dl_fml }) => do
    let raw ← liftMacroM (expandFml φ)
    elabAgainst c fun q => `((elabDl $c $raw).map (Fml.quote $q))

macro_rules
  | `(dl!{ $φ:dl_fml }) => `(dl[InContract.contract]{ $φ })

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

/-- error: Solidity elaboration failed: unknown name y -/
#guard_msgs in #check dl!{ ⟨ uint y = 1; ⟩ true ∧ y == 1 }

end Examples

end Solidity
