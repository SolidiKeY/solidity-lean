import Solidity.Calculus.RuleSyntax.Grammar

/-!
# The rule syntax: terms and scoped taclets

Reading schemas, continued: terms and scoped taclets; the schema macros
and the side conditions' elaborator.

A piece of `Calculus/RuleSyntax.lean`, whose docstring describes the whole.
-/

namespace Solidity

section Expand

open Lean (Ident Macro MacroM mkIdent mkIdentFrom Name TSyntax Syntax)

/-! ### Terms -/

/-- The three sorts a term position asks for, and the memory ones. -/
inductive TPos where
  | val | path | storage | ident | addr | memory | svalue | mvalue
  deriving DecidableEq

def TPos.name : TPos → String
  | .val => "a value" | .path => "a storage path" | .storage => "a storage"
  | .ident => "a memory identity" | .addr => "a memory location" | .memory => "a memory"
  | .svalue => "a storage value" | .mvalue => "a memory value"

def tposError (x : Lean.Syntax) (what : String) (pos : TPos) : MacroM α :=
  Macro.throwErrorAt x s!"{what} is not {pos.name}"

/-- A name at a term sort: a schema variable of a program sort is lowered
(`se` is the term `se.lower`), a stack local is `pv`. -/
def headTerm (Γ : Scope) (pos : TPos) (x : Ident) : MacroM Lean.Term := do
  let n := x.getId.toString
  if stemOf n == "src" && pos == .svalue then
    return ← `($(Lean.mkCIdent `Solidity.Src.lower) $(rhsTerm Γ "src" ⟨x⟩ |>.getD x))
  if (n == "true" || n == "false") && pos == .val then
    return ← `(Term.litB $(mkIdent (Name.mkSimple n)))
  if n == "storage" && pos == .storage then return ← `(STerm.storage)
  if n == "memory" && pos == .memory then return ← `(MTerm.memory)
  if n == "selfBalance" && pos == .val then return ← `(Term.env EnvKey.selfBalance)
  if (n == "this" || n == "self") && pos == .val then return ← `(Term.env EnvKey.selfAddress)
  match headOf Γ x, pos with
  | .local v, .val => `(Term.pv $v)
  | .local v, .svalue => `(SValT.val (Term.pv $v))
  | .local v, .mvalue => `(MValT.val (Term.pv $v))
  | .alias v, .path => `(PTerm.pv $v)
  | .mem v _, .ident => `(ITerm.pv $v)
  | .mem v _, .mvalue => `(MValT.ref (ITerm.pv $v))
  | .root r h, .val => `(Term.find STerm.storage (PTerm.root $r $h))
  | .root r h, .path => `(PTerm.root $r $h)
  | .simple s, .val => `($(Lean.mkCIdent `Solidity.Simple.lower) $s)
  | .simple s, .svalue => `(SValT.val ($(Lean.mkCIdent `Solidity.Simple.lower) $s))
  | .simple s, .mvalue => `(MValT.val ($(Lean.mkCIdent `Solidity.Simple.lower) $s))
  | .val e, .val => `($(Lean.mkCIdent `Solidity.Val.lower) $e)
  | .spath p, .path => `($(Lean.mkCIdent `Solidity.SPath.lower) $p)
  | .mpath p, .ident => `($(Lean.mkCIdent `Solidity.MPath.lower) $p)
  | .mpath p, .mvalue => `(MValT.ref ($(Lean.mkCIdent `Solidity.MPath.lower) $p))
  | .loc l, .path => `($(Lean.mkCIdent `Solidity.Loc.lower) $l)
  | .other o, _ => pure o
  | _, _ => tposError x s!"`{n}`" pos

/-- `mv.f₁.….fₙ` at a term sort: the inner members are identities read. -/
def memMember (core : Bool) (pos : TPos) (stx : Lean.Syntax) :
    Lean.Term → List Ident → MacroM Lean.Term
  | b, [] => pure b
  | b, [f] =>
    -- in a rule, `mv.length` at the local's type (`Val.mlen`'s `hlen`)
    if f.getId.toString == "length" && pos == .val && core then
      `(Term.mlenH $(schemaIdent "hlen") MTerm.memory $b) else
    if f.getId.toString == "length" && pos == .val then `(Term.mlen MTerm.memory $b) else
    let h := proofIdent f f.getId.toString
    match pos with
    | .addr => `(MAddr.field $b $f $h)
    | .val => `(Term.read MTerm.memory (MAddr.field $b $f $h))
    | .ident => `(ITerm.read MTerm.memory (MAddr.field $b $f $h))
    | .mvalue => `(MValT.ref (ITerm.read MTerm.memory (MAddr.field $b $f $h)))
    | _ => tposError stx "a memory member" pos
  | b, f :: fs => do
    let h := proofIdent f f.getId.toString
    memMember core pos stx (← `(ITerm.read MTerm.memory (MAddr.field $b $f $h))) fs

/-- `p.length`, however it was parsed, or KeY's `consr(p, size)`: the path `p`. -/
def lengthBase? : TSyntax `dl_term → MacroM (Option (TSyntax `dl_term))
  | `(dl_term| consr($b, $sz:ident)) => pure (if sz.getId.toString == "size" then some b else none)
  | `(dl_term| $x:ident) =>
    match (nameParts x.getId).reverse with
    | "length" :: r :: rs => do
      let n := (r :: rs).reverse.foldl (fun n s => Name.str n s) Name.anonymous
      some <$> `(dl_term| $(mkIdentFrom x n):ident)
    | _ => pure none
  | `(dl_term| $t:dl_term . $f:ident) => pure (if f.getId.toString == "length" then some t else none)
  | _ => pure none

/-- How a storage receiver term is indexed, as `indexTyOf` reads a program
expression: `map[ie]` by key, `arr[ie]` (and its kin) by position, anything
else by the schema variable `it`. -/
def indexTyOfTerm : TSyntax `dl_term → MacroM Lean.Term
  | `(dl_term| $x:ident) =>
    match nameParts x.getId with
    | [n] => indexTyOfStem n
    | _ => pure (schemaIdent "it")
  | _ => pure (schemaIdent "it")

/-- A reference type written as a term: `S`, `T[]`, `T[n]`. -/
partial def refTyTerm (t : TSyntax `dl_term) : MacroM Lean.Term := do
  let elem (e : TSyntax `dl_term) : MacroM Lean.Term := do
    match e with
    | `(dl_term| uint) => `(Ty.prim PrimTy.uint)
    | `(dl_term| int) => `(Ty.prim PrimTy.int)
    | `(dl_term| bool) => `(Ty.prim PrimTy.bool)
    | _ => `(Ty.ref $(← refTyTerm e))
  match t with
  | `(dl_term| $e:dl_term []) => `(RefTy.array $(← elem e))
  | `(dl_term| $e:dl_term [ $k:num ]) => `(RefTy.fixed $(← elem e) $k)
  | `(dl_term| $s:ident) => `(RefTy.struct $(Lean.quote s.getId.toString))
  | _ => Macro.throwErrorAt t "a reference type: `S`, `T[]` or `T[n]`"

mutual

/-- A term at a sort.  At a storage or a memory value's sort, a value term is
wrapped as one; a path, `find(…)` and `copyMem(…)` are storage values of
their own, a memory path a memory value of its own. -/
partial def schemaTerm (Γ : Scope) (pos : TPos) (t : TSyntax `dl_term) : MacroM Lean.Term := do
  -- in `tm{ … }` a name is a variable of the sort it stands at
  if Γ.isRaw && (pos == .svalue || pos == .mvalue) then
    if let `(dl_term| $x:ident) := t then
      if (nameParts x.getId).length == 1 then return x
  match pos with
  | .svalue =>
    match t with
    | `(dl_term| $x:ident) =>
      if stemOf x.getId.toString == "src" then headTerm Γ .svalue x
      else `(SValT.val $(← schemaTerm0 Γ .val t))
    | `(dl_term| $f:ident($_,*)) =>
      if ["find", "copyMem", "newArr", "fixedCopy"].contains f.getId.toString then
        schemaTerm0 Γ .svalue t
      else `(SValT.val $(← schemaTerm0 Γ .val t))
    | _ => `(SValT.val $(← schemaTerm0 Γ .val t))
  | .mvalue =>
    let memHead := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | [h] => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem .. | .mpath _ => true
          | _ => false
        | _ => false
      | `(dl_term| $f:ident($_,*)) => f.getId.toString == "freshId"
      | _ => false
    if memHead then `(MValT.ref $(← schemaTerm0 Γ .ident t))
    else `(MValT.val $(← schemaTerm0 Γ .val t))
  | _ => schemaTerm0 Γ pos t

/-- A storage index: a program expression's term is its lowering
(`Simple.lower`, `Loc.lower`'s), any other term itself. -/
partial def schemaKey (Γ : Scope) (i : TSyntax `dl_term) : MacroM Lean.Term := do
  if let `(dl_term| $x:ident) := i then
    if (nameParts x.getId).length == 1 then
      match headOf Γ x with
      | .simple s => return ← `($(Lean.mkCIdent `Solidity.Simple.lower) $s)
      | .val e => return ← `($(Lean.mkCIdent `Solidity.Val.lower) $e)
      | _ => pure ()
  schemaTerm Γ .val i

partial def schemaTerm0 (Γ : Scope) (pos : TPos) : TSyntax `dl_term → MacroM Lean.Term
  | stx@`(dl_term| $n:num) =>
    match pos with
    | .val => `(Term.nat $n)
    | .svalue => `(SValT.val (Term.nat $n))
    | .mvalue => `(MValT.val (Term.nat $n))
    | _ => tposError stx "a number" pos
  | stx@`(dl_term| $x:ident) => do
    match nameParts x.getId with
    | [] => Macro.throwError "empty identifier"
    | [_] => headTerm Γ pos x
    | h :: fs =>
      -- `sp.fld`: a path, or (at a memory sort) a member of a memory object
      let hx := partIdent x h
      match headOf Γ hx with
      | .mem .. | .mpath _ =>
        memMember Γ.isCore pos stx (← headTerm Γ .ident hx) (fs.map (partIdent x))
      | _ =>
        if fs.getLast? == some "length" then
          let p' ← (fs.dropLast).foldlM (init := ← headTerm Γ .path hx) fun acc f =>
            `(PTerm.field $acc $(partIdent x f) $(proofIdent x f))
          match pos with
          | .val =>
            if Γ.isCore then `(Term.lenH $(schemaIdent "hlen") STerm.storage $p')
            else `(Term.len STerm.storage $p')
          | _ => tposError stx "a length" pos
        else
        let p ← fs.foldlM (init := ← headTerm Γ .path hx) fun acc f =>
          `(PTerm.field $acc $(partIdent x f) $(proofIdent x f))
        match pos with
        | .path => pure p
        | .val => `(Term.find STerm.storage $p)
        | .svalue => `(SValT.find STerm.storage $p)
        | _ => tposError stx "a storage path" pos
  | stx@`(dl_term| $t:dl_term . $f:ident) => do
    let p ← (nameParts f.getId).foldlM (init := ← schemaTerm Γ .path t) fun acc c =>
      `(PTerm.field $acc $(partIdent f c) $(proofIdent f c))
    match pos with
    | .path => pure p
    | _ => tposError stx "a member" pos
  | stx@`(dl_term| $t:dl_term [ $i:dl_term ]) => do
    let mem := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem .. | .mpath _ => true
          | _ => false
        | [] => false
      | _ => false
    if mem then
      let a ← `(MAddr.at $(schemaIdent "mk") $(← schemaTerm Γ .ident t) $(← schemaTerm Γ .val i))
      match pos with
      | .addr => pure a
      | .val => `(Term.read MTerm.memory $a)
      | .ident => `(ITerm.read MTerm.memory $a)
      | .mvalue => `(MValT.ref (ITerm.read MTerm.memory $a))
      | _ => tposError stx "a memory element" pos
    else
      -- `p[p.length]`, the slot one past the end: no bounds check
      let pastEnd ← do
        let some b ← lengthBase? i | pure false
        match b, t with
        | `(dl_term| $b:ident), `(dl_term| $x:ident) => pure (b.getId == x.getId)
        | _, _ => pure false
      let p ← if pastEnd then `(PTerm.next $(← schemaTerm Γ .path t))
        else `(PTerm.at $(← indexTyOfTerm t) $(← schemaTerm Γ .path t) $(← schemaKey Γ i))
      match pos with
      | .path => pure p
      | .val => `(Term.find STerm.storage $p)
      | .svalue => `(SValT.find STerm.storage $p)
      | _ => tposError stx "an entry" pos
  | `(dl_term| $a:dl_term ⊕ $b:dl_term) => do
    -- the operator schema variable's proofs are `Val.binop`'s (`hop`, `hq`);
    -- in a compound assignment `schemaTacletCore` turns them into `⊕=`'s
    `(Term.binopS $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
        $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ⊖ $a:dl_term) => do
    `(Term.unopS $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
        $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term ± $b:dl_term) => do
    -- the step of `++`/`--`, `1` at the target's type
    let b ← match b with
      | `(dl_term| 1) => `(Term.one $(schemaIdent "p") $(schemaIdent "hp"))
      | _ => schemaTerm Γ .val b
    `(Term.binopI $(schemaIdent "op") $(schemaIdent "hp") $(← schemaTerm Γ .val a) $b)
  | `(dl_term| $a:dl_term ⊕⊕) => do
    `(Term.bumped $(schemaIdent "op") $(schemaIdent "hp") $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term + $b:dl_term) => do
    `(Term.binop BinOp.add PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term - $b:dl_term) => do
    `(Term.binop BinOp.sub PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term / $b:dl_term) => do
    `(Term.binop BinOp.div PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term * $b:dl_term) => do
    `(Term.binop BinOp.mul PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term % $b:dl_term) => do
    `(Term.binop BinOp.mod PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term && $b:dl_term) => do
    `(Term.binop BinOp.and PrimTy.bool $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term || $b:dl_term) => do
    `(Term.binop BinOp.or PrimTy.bool $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ( $a:dl_term == $b:dl_term )) => do
    `(Term.binop BinOp.eqB _ $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | stx@`(dl_term| ( $c:dl_term ? $a:dl_term : $b:dl_term )) => do
    unless pos matches .val do tposError stx "a conditional value" pos
    `($(Lean.mkCIdent `Solidity.Tm.app3) $(Lean.mkCIdent `Solidity.Op3.ite)
      $(← schemaTerm Γ .val c) $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ( $t:dl_term )) => schemaTerm Γ pos t
  | `(dl_term| ‹ $t:term ›) => pure t
  | stx@`(dl_term| $f:ident($args,*)) => do
    let args := args.getElems
    let st := schemaTerm Γ .storage
    let pa := schemaTerm Γ .path
    let me := schemaTerm Γ .memory
    -- KeY's three-argument `read(m, i, f)`, four-argument `write(m, i, f, v)`:
    -- the member `f`, the element `at(k)`
    let maddr (i a : TSyntax `dl_term) : MacroM Lean.Term := do
      match a with
      | `(dl_term| at($k)) =>
        `(MAddr.at $(schemaIdent "mk") $(← schemaTerm Γ .ident i) $(← schemaTerm Γ .val k))
      | `(dl_term| $g:ident) =>
        `(MAddr.field $(← schemaTerm Γ .ident i) $g $(proofIdent g g.getId.toString))
      | _ => tposError a "a member `f` or an element `at(k)`" .addr
    match f.getId.eraseMacroScopes.toString, args, pos with
    | "addmod", #[a, b, k], .val =>
      `(Term.modular ModOp.addmod $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b)
        $(← schemaTerm Γ .val k))
    | "mulmod", #[a, b, k], .val =>
      `(Term.modular ModOp.mulmod $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b)
        $(← schemaTerm Γ .val k))
    | "hash", #[m, i], .val =>
      if Γ.isCore then
        `(Term.hashH $(schemaIdent "hh") $(schemaIdent "hk") $(← me m) $(← schemaTerm Γ .ident i))
      else `(Term.hash $(schemaIdent "hh") $(← me m) $(← schemaTerm Γ .ident i))
    | "select", #[s, r], .val => `(Term.find $(← st s) $(← pa r))
    | "select", #[s, r], .storage | "selectSt", #[s, r], .storage =>
      let `(dl_term| $r:ident) := r | tposError r "a member name" .storage
      `(STerm.select $(← st s) $r $(proofIdent r r.getId.toString))
    | "net", #[a], .val => `(Term.net $(← schemaTerm Γ .val a))
    | "selectSt", #[n, a], .val =>
      let `(dl_term| net) := n | tposError n "`net`" .val
      let `(dl_term| at($a)) := a | tposError a "`at(a)`" .val
      `(Term.net $(← schemaTerm Γ .val a))
    | "find", #[s, p], .val =>
      match ← lengthBase? p with
      | some b =>
        if Γ.isCore then `(Term.lenH $(schemaIdent "hlen") $(← st s) $(← pa b))
        else `(Term.len $(← st s) $(← pa b))
      | none => `(Term.find $(← st s) $(← pa p))
    | "find", #[s, p], .svalue =>
      match ← lengthBase? p with
      | some b => `(SValT.val (Term.len $(← st s) $(← pa b)))
      | none => `(SValT.find $(← st s) $(← pa p))
    | "consr", #[p, f], .path =>
      match f with
      | `(dl_term| at($i)) =>
        -- `consr(p, at(find(storage, consr(p, size))))`: the slot past the end
        let past ← match i with
          | `(dl_term| find(storage, $q)) => do
            match ← lengthBase? q with
            | some b => pure (b.raw.structEq p.raw)
            | none => pure false
          | _ => pure false
        if past then `(PTerm.next $(← pa p))
        else `(PTerm.at $(← indexTyOfTerm p) $(← pa p) $(← schemaKey Γ i))
      | `(dl_term| atMap($i)) => `(PTerm.at IndexTy.map $(← pa p) $(← schemaKey Γ i))
      | `(dl_term| $g:ident) =>
        if g.getId.toString == "size" then tposError f "`consr(p, size)` outside `find`" .path
        else `(PTerm.field $(← pa p) $g $(proofIdent g g.getId.toString))
      | _ => tposError f "a member, `at(i)` or `atMap(i)`" .path
    | "read", #[m, a], .val => `(Term.read $(← me m) $(← schemaTerm Γ .addr a))
    | "read", #[m, a], .ident => `(ITerm.read $(← me m) $(← schemaTerm Γ .addr a))
    | "read", #[m, i, a], .val =>
      if let `(dl_term| $g:ident) := a then
        if g.getId.toString == "size" then
          if Γ.isCore then
            return ← `(Term.mlenH $(schemaIdent "hlen") $(← me m) $(← schemaTerm Γ .ident i))
          return ← `(Term.mlen $(← me m) $(← schemaTerm Γ .ident i))
      `(Term.read $(← me m) $(← maddr i a))
    | "read", #[m, i, a], .ident => `(ITerm.read $(← me m) $(← maddr i a))
    | "write", #[m, i, a, v], .memory =>
      `(MTerm.write $(← me m) $(← maddr i a) $(← schemaTerm Γ .mvalue v))
    | "delValue", #[t], .val => `(Term.delValue $(← schemaTerm Γ .val t))
    | "lit", #[v], .val =>
      match v with
      | `(dl_term| $x:ident) => `(Term.lit $x)
      | `(dl_term| ‹ $x:term ›) => `(Term.lit $x)
      | _ => tposError v "a value variable" .val
    | "copyMem", #[_, m, i], .svalue => `(SValT.copyMem $(← me m) $(← schemaTerm Γ .ident i))
    | "newArr", #[n], .svalue => `(SValT.newArr $(schemaIdent "R") $(← schemaTerm Γ .val n))
    | "fixedCopy", #[T, v], .svalue =>
      `(SValT.fixedCopyTo $(← refTyTerm T) $(← schemaTerm Γ .svalue v))
    | "freshId", #[t], .ident =>
      match t with
      | `(dl_term| addM($m)) => `(ITerm.alloc $(← me m) $(schemaIdent "R"))
      | `(dl_term| copySt($m, $v)) => `(ITerm.copy $(← me m) $(← schemaTerm Γ .svalue v))
      | _ => Macro.throwErrorAt t "`freshId(addM(m))` or `freshId(copySt(m, v))`"
    | "store", #[s, r, v], .storage => `(STerm.save $(← st s) $(← pa r) $(← schemaTerm Γ .svalue v))
    | "save", #[s, p, v], .storage =>
      -- push and pop, nested writes over the extent
      match ← lengthBase? p with
      | some b =>
        -- the element written or deleted: `p[i]`, KeY's `consr(p, at(i))`
        let elem (q : TSyntax `dl_term) : Bool := match q with
          | `(dl_term| $_[$_]) => true
          | `(dl_term| consr($_, at($_))) => true
          | _ => false
        match s, v with
        | `(dl_term| save($s', $q, $w)), `(dl_term| $_ + 1) =>
          if elem q then return ← `(STerm.push $(← st s') $(← pa b) $(← schemaTerm Γ .svalue w))
        | `(dl_term| delAt($s', $q)), `(dl_term| $_ - 1) =>
          if elem q then return ← `(STerm.pop $(← st s') $(← pa b))
        | _, _ => pure ()
        match v with
        | `(dl_term| $_ + 1) =>
          -- an empty push saves only the length (solkey's `storagePushLengthSave`)
          `(STerm.pushSlot $(← st s) $(← pa b) _)
        | `(dl_term| $_ - 1) => `(STerm.shrink $(← st s) $(← pa b))
        | _ => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
      | none => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
    | "delAt", #[s, p], .storage => `(STerm.delAt $(← st s) $(← pa p))
    | "defVal", #[_], .val => `(Term.dflt $(schemaIdent "p"))
    | "write", #[m, a, v], .memory =>
      `(MTerm.write $(← me m) $(← schemaTerm Γ .addr a) $(← schemaTerm Γ .mvalue v))
    | "addM", #[m], .memory => `(MTerm.addM $(← me m) $(schemaIdent "R"))
    | "copySt", #[m, v], .memory => `(MTerm.copySt $(← me m) $(← schemaTerm Γ .svalue v))
    | _, _, _ => tposError stx s!"`{f.getId}(…)` here" pos
  | _ => Macro.throwUnsupported

end

/-- The sort of a term of `tm{ … }`, read off its head. -/
def tmSort : TSyntax `dl_term → TPos
  | `(dl_term| $f:ident($_,*)) =>
    match f.getId.toString with
    | "save" | "delAt" | "store" | "select" | "selectSt" => .storage
    | "write" | "addM" | "copySt" => .memory
    | "consr" => .path
    | "freshId" => .ident
    | "copyMem" | "newArr" | "fixedCopy" => .svalue
    | _ => .val
  | `(dl_term| $x:ident) =>
    match x.getId.toString with
    | "storage" => .storage
    | "memory" => .memory
    | _ => if (nameParts x.getId).length > 1 then .path else .val
  | `(dl_term| $_:dl_term . $_:ident) | `(dl_term| $_:dl_term [ $_:dl_term ]) => .path
  | _ => .val

/-- One elementary update of a global: `selfBalance`, `net`, `storage` or
`memory` (`schemaUpdCore` reads a local's itself, as `UpdElem.local`). -/
def schemaUpdElem (Γ : Scope) : TSyntax `dl_upd_elem → MacroM Lean.Term
  | `(dl_upd_elem| pay($r:dl_term, $a:dl_term)) => do
    `(UpdElem.pay $(← schemaTerm Γ .val r) $(← schemaTerm Γ .val a))
  | `(dl_upd_elem| $l:dl_term := $r:dl_term) => do
    let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
    let n := x.getId.toString
    if n == "selfBalance" then
      return ← match r with
        | `(dl_term| selfBalance - $a) => do
          `(UpdElem.selfBalance IntOp.sub $(← schemaTerm Γ .val a))
        | `(dl_term| selfBalance + $a) => do
          `(UpdElem.selfBalance IntOp.add $(← schemaTerm Γ .val a))
        | _ => Macro.throwErrorAt r "`selfBalance - a` or `selfBalance + a`"
    if n == "net" then
      return ← match r with
        | `(dl_term| store(net, at($a), net($a') - $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.sub $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| store(net, at($a), net($a') + $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.add $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| storeSt(net, at($a), selectSt(net, at($a')) - $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.sub $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| storeSt(net, at($a), selectSt(net, at($a')) + $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.add $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| if($a = $t:ident) then $n':ident else storeSt(net, at($a'), selectSt(net, at($a'')) - $v))
        | `(dl_term| if($a = $t:ident) then $n':ident else store(net, at($a'), net($a'') - $v)) => do
          unless ["this", "self"].contains t.getId.toString do
            Macro.throwErrorAt t "a payment compares with `this`"
          unless n'.getId.toString == "net" do Macro.throwErrorAt n' "a payment to `this` leaves `net`"
          unless a.raw.structEq a'.raw && a.raw.structEq a''.raw do
            Macro.throwErrorAt a' "the entry read is the one written, and the one compared"
          Macro.throwErrorAt r "use `pay(receiver, amount)`: a payment updates both ledger and balance"
        | _ => Macro.throwErrorAt r "`store(net, at(r), net(r) - a)` or `… + a`; use `pay(r, a)` for payments"
    if n == "storage" then return ← `(UpdElem.storage $(← schemaTerm Γ .storage r))
    if n == "memory" then return ← `(UpdElem.memory $(← schemaTerm Γ .memory r))
    Macro.throwErrorAt x "an elementary update of a global assigns `selfBalance`, `net`, \
      `storage` or `memory`"
  | _ => Macro.throwUnsupported

/-- The modality of the formula under an update: an update is judged as the
goal it came from.  `⟨[ ]⟩` is `either`: the taclet's `m` in `dl{ … }`, the
formula's modality in `dl![m]{ … }` (`Calculus/Notation.lean`). -/
partial def fmlModality? (either : Lean.Term) : TSyntax `dl_fml → MacroM (Option Lean.Term)
  | `(dl_fml| ⟨ $[$_:sol_stmt;]* ⟩ $_:dl_fml) | `(dl_fml| ⟨ $_:sol_block ⟩ $_:dl_fml) =>
    some <$> `(Modality.diamond)
  | `(dl_fml| [ $[$_:sol_stmt;]* ] $_:dl_fml) | `(dl_fml| [ $_:sol_block ] $_:dl_fml) =>
    some <$> `(Modality.box)
  | `(dl_fml| ⟨ $[$_:sol_stmt;]* .. $_:term ⟩ $_:dl_fml) => some <$> `(Modality.diamond)
  | `(dl_fml| [ $[$_:sol_stmt;]* .. $_:term ] $_:dl_fml) => some <$> `(Modality.box)
  | `(dl_fml| ⟨[ $[$_:sol_stmt;]* ]⟩ $_:dl_fml) | `(dl_fml| ⟨[ $[$_:sol_stmt;]* .. $_:term ]⟩ $_:dl_fml)
  | `(dl_fml| ⟨[ $_:sol_block ]⟩ $_:dl_fml) => pure (some either)
  | `(dl_fml| $_:dl_upd $φ:dl_fml) | `(dl_fml| { havoc } $φ:dl_fml) => fmlModality? either φ
  | `(dl_fml| ( $φ:dl_fml )) => fmlModality? either φ
  | _ => pure none

/-- One goal of `Premise.branches`: the locals it binds (`∀ rets.`; `∀ code.`
the `Panic` code's, `CodeBinder.binders`), and its block.  The label is dropped. -/
def schemaBranch (fresh : Bool) (Γ : Scope) (b : TSyntax `dl_branch) : MacroM Lean.Term := do
  let (x?, blk) ← match b with
    | `(dl_branch| $[$_:str :]? $[∀ $x?:ident .]? ⟨[ $blk:sol_block ]⟩) => pure (x?, blk)
    | `(dl_branch| $[$_:str :]? $[∀ $x?:ident .]? [ $blk:sol_block ]) => pure (x?, blk)
    | _ => Macro.throwUnsupported
  -- its binders (`Binders`, the `Panic` code's `CodeBinder.binders`) and
  -- its block read on top of them
  let xs ← match x? with
    | none => pure (Lean.mkCIdent `Solidity.Binders.nil : Lean.Term)
    | some x =>
      if stemOf x.getId.toString == "code" then
        `($(Lean.mkCIdent `Solidity.CodeBinder.binders) $x)
      else pure x
  `($(Lean.mkCIdent `Solidity.Branch.mk) $xs $(← schemaBlock fresh Γ blk) none)

/-- The identifiers of a `\find`, outside `‹…›`. -/
partial def findIdents : Lean.Syntax → Array Ident
  | stx@(.ident ..) => #[⟨stx⟩]
  | .node _ _ args =>
    if args[0]?.any (·.isOfKind `atom) && args[0]!.getAtomVal == "‹" then #[]
    else args.flatMap findIdents
  | _ => #[]

/-- A right-hand side that is one schema variable, and its spelling. -/
def singleVar? : TSyntax `sol_expr → Option String
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [s] => some s
    | _ => none
  | _ => none

/-- A memory location every part of which is simple: a member or an element
of a memory local at a simple index (`mv.fld`, `mv[ie]`). -/
def memTarget : TSyntax `sol_expr → Bool
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [h, _] => stemOf h == "mv"
    | _ => false
  | `(sol_expr| $b:ident [ $i:ident ]) =>
    stemOf b.getId.toString == "mv" && ["se", "ie"].contains (stemOf i.getId.toString)
  | _ => false

/-- **The side conditions of a `\find`**, as hypothesis names and types: what
`Stmt.step` knows of the parts when it fires the rule.

* by name: `nsp` is not simple and `sp`, `map`, `arr` are (`SPath.isSimple`),
  `nse`, `nadr` are not simple values, `nmp` is not a memory local, and `loc`
  is a member or an entry at a target, never a state variable;
* by position: a hole `lhs` lands in a target (`Hole.isTarget`,
  `MHole.isTarget`, `VHole.isTarget`); a value `e`, `nse` written to storage
  or memory is not a conditional (`Val.notTernary`: a conditional is lowered
  first); a memory path `mpath` written as a reference is bindable
  (`MPath.isBindable`). -/
def sideConds (s : TSyntax `sol_stmt) : MacroM (Array (Ident × Lean.Term)) := do
  let mut out : Array (Ident × Lean.Term) := #[]
  let mut seen : List String := []
  let hyp (n : String) : Ident := mkIdent (Name.mkSimple ("h" ++ n))
  for x in findIdents s.raw do
    let some n := (nameParts x.getId).head? | continue
    if seen.contains n then continue
    seen := n :: seen
    let v := schemaIdent n
    match stemOf n with
    | "nsp" => out := out.push (hyp n, ← `(SPath.isSimple $v = false))
    | "sp" | "map" | "arr" => out := out.push (hyp n, ← `(SPath.isSimple $v = true))
    | "parr" | "rarr" | "marr" | "darr" =>
      out := out.push (hyp n, ← `(SPath.isSimple $v = true))
      let (pred, b) := match stemOf n with
        | "parr" => (`Solidity.SPath.elemPrim, true)
        | "rarr" => (`Solidity.SPath.elemPrim, false)
        | "marr" => (`Solidity.SPath.elemMapping, true)
        | _ => (`Solidity.SPath.elemMapping, false)
      let bv ← if b then `(true) else `(false)
      out := out.push (hyp (n ++ "_e"), ← `($(mkIdent pred) $v = $bv))
      if stemOf n == "rarr" then
        out := out.push (hyp (n ++ "_nm"), ← `($(mkIdent `Solidity.SPath.elemMapping) $v = false))
    | "nse" | "nadr" => out := out.push (hyp n, ← `(Val.isSimple $v = false))
    | "nmp" => out := out.push (hyp n, ← `(MPath.isSimple $v = false))
    | "loc" =>
      out := out.push (hyp n, ← `($(mkIdent `Solidity.Loc.isTarget) $v = true))
      out := out.push (hyp (n ++ "_nr"), ← `($(mkIdent `Solidity.Loc.isRoot) $v = false))
    | _ => pure ()
  let notTernary (r : TSyntax `sol_expr) : MacroM (Array (Ident × Lean.Term)) := do
    let some n := singleVar? r | return #[]
    unless ["e", "nse"].contains (stemOf n) do return #[]
    return #[(hyp (n ++ "_nt"), ← `($(mkIdent `Solidity.Val.notTernary) $(schemaIdent n) = true))]
  let pushArg ← match s with
    | `(sol_stmt| $_:sol_expr .push( $e:sol_expr )) => pure (some e)
    | `(sol_stmt| $f:sol_expr ( $e:sol_expr )) => do
      let some (_, "push") ← callRecv? f | pure none
      pure (some e)
    | _ => pure none
  if let some e := pushArg then
    if let some n := singleVar? e then
      if stemOf n == "nse" then
        out := out.push (hyp (n ++ "_path"),
          ← `(Val.complexStorageRead $(schemaIdent n) = false))
  match s with
  | `(sol_stmt| $x:ident) =>
    -- `fbs`, `ic`, a call: its arguments simple (`functionCallArgCapture`
    -- first), and with targets (`fbs`) or without (`ic`)
    let n := x.getId.toString
    unless isCallStem n do return out
    let b ← if stemOf n == "fbs" then `(true) else `(false)
    let out' := out.push (mkIdent `hexp, ← `($(mkIdent `Solidity.Args.firstNonSimple) $(schemaIdent "args") = none))
      |>.push (mkIdent `hrets, ← `($(mkIdent `Solidity.CallRet.isRets) $(schemaIdent "ret") = $b))
    -- `ic`: no summary (`internalCallSummary` runs one)
    if stemOf n == "fbs" then return out'
    return out'.push (mkIdent `hsum, ← `($(mkIdent `Solidity.CallRet.summary?) $(schemaIdent "args")
      $(schemaIdent "ret") $(schemaIdent "body") = none))
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) =>
    match lhsHead [] l with
    | some (.other h) =>
      let some n := singleVar? l | return out
      unless stemOf n == "lhs" do return out
      if isMem [] r then return out.push (hyp n, ← `($(mkIdent `Solidity.MHole.isTarget) $h = true))
      if isPath [] r then return out.push (hyp n, ← `($(mkIdent `Solidity.SHole.isTarget) $h = true))
      return out.push (hyp n, ← `($(mkIdent `Solidity.VHole.isTarget) $h = true))
    | some (.local _) | some (.alias _) | some (.mem ..) => return out
    | _ =>
      if isMem [] l then
        if (rhsVar? "msrc" r).isSome then return out
        -- only into a target (`mv.fld`, `mv[ie]`) is a source lowered or
        -- written as it is; into any other the capture takes it whole
        unless memTarget l do return out
        if isMem [] r then
          let some n := singleVar? r | return out
          return out.push (hyp (n ++ "_b"), ← `($(mkIdent `Solidity.MPath.isBindable) $(schemaIdent n) = true))
        return out ++ (← notTernary r)
      if isMem [] r || (rhsVar? "src" r).isSome || isPath [] r then return out
      return out ++ (← notTernary r)
  | _ => return out

/-! ### Scoped taclets

The lines read into `Solidity`'s scoped syntax under `open scoped
Solidity.Schema`.  The statements and expressions are read as above, from
`coreScope`: a fresh local is a position, a `\find`'s schema variable is
weakened past the fresh locals before it (`headOfCore`); a program is
`Prog.cons`.  The terms are written by their symbols' KeY names
(`Term.find`, `STerm.save`), which no declaration here resolves, and then
turned into the scoped symbols (`coreNames`); a formula is written scoped
(`fmlC`).  The premise: an
unfolding premise pops its fresh locals (`Premise.unfold P (Ext.push^d
.refl)`), a `\find` that declares binds its local in front of the premise
(`Premise.bind`) or declares it in the update (`Upd.decl`), a split says how
its goals end (`BlockKind`), a check has no program. -/

/-- The scoped family a symbol's family name stands for: the
term symbols (`Term.find`, `STerm.save`, …) are `Calculus/Rules.lean`'s,
under `Tms` (`Solidity.MAddr` is the typed heap's); a term, an update and
its elements their families of the same name.  A formula is written scoped
(`fmlC`). -/
def coreFamily? : Lean.Name → Option Lean.Name
  | n =>
    if [`Term, `PTerm, `STerm, `SValT, `ITerm, `MAddr, `MTerm, `MValT].contains n then
      some (`Tms ++ n)
    else if [`Tm, `UpdElem, `Upd].contains n then some n
    else none

/-- `Solidity.F.x` as `Solidity.F'.x`, `F'` the scoped twin of `F`. -/
def coreName? (n : Lean.Name) : Option Lean.Name :=
  match n.components with
  | s :: s' :: f :: rest =>
    if s != `Solidity then none
    else (coreFamily? s').map fun f' => (f :: rest).foldl (· ++ ·) (`Solidity ++ f')
  | [s, f] => if s != `Solidity then none else (coreFamily? f).map fun f' => `Solidity ++ f'
  | _ => none

/-- Every name of a term symbol the reader wrote, by its quotation's
resolution, spelled in full, or (a symbol `F.x` of a family `coreFamily?`
names, which no declaration below the rule table resolves) by its family,
turned into its scoped twin, which must exist. -/
partial def coreNames (stx : Syntax) : MacroM Syntax := do
  match stx with
  | .ident _ _ val pre =>
    let byPre := pre.findSome? fun
      | .decl n [] => if (`Solidity).isPrefixOf n then some n else none
      | _ => none
    let v := val.eraseMacroScopes
    let byFamily := match v.components with
      | f :: _ :: _ => if (coreFamily? f).isSome then some (`Solidity ++ v) else none
      | _ => none
    let some n := byPre <|> (if (`Solidity).isPrefixOf v then some v else none) <|> byFamily
      | return stx
    let some n' := coreName? n | return stx
    unless ← Macro.hasDecl n' do Macro.throwErrorAt stx s!"no scoped twin `{n'}` of `{n}`"
    return Lean.mkCIdentFrom stx n'
  | .node info k args => return .node info k (← args.mapM coreNames)
  | _ => return stx

/-- A scoped update's right-hand side for the local `x`, by its kind:
`Rhs.val`, `Rhs.path` (`unset` too), `Rhs.mref`. -/
def schemaRhsCore (Γ : Scope) (x : Ident) (r : TSyntax `dl_term) : MacroM Lean.Term := do
  match headOf Γ x with
  | .local _ => `($(Lean.mkCIdent `Solidity.Rhs.val) $(← schemaTerm Γ .val r))
  | .alias _ =>
    if let `(dl_term| $u:ident) := r then
      if u.getId == `unset then return Lean.mkCIdent `Solidity.Rhs.unset
    `($(Lean.mkCIdent `Solidity.Rhs.path) $(← schemaTerm Γ .path r))
  | .mem .. => `($(Lean.mkCIdent `Solidity.Rhs.mref) $(← schemaTerm Γ .ident r))
  | _ => Macro.throwErrorAt x "an update assigns a local, an alias, a memory local, \
      `storage` or `memory`"

/-- `Ext.push^d .refl`: the `d` fresh locals a premise declared, popped. -/
def extPush (d : Nat) : MacroM Lean.Term := do
  let mut h : Lean.Term := Lean.mkCIdent `Solidity.Ext.refl
  for _ in [0:d] do h ← `($(Lean.mkCIdent `Solidity.Ext.push) $h)
  return h

/-- The fresh local an update element declares by its spelling: KeY's `b`
(`bType b = cond;`, a `bool`) and `variant` (`\\skolemTerm int variant`, a
`uint`), the invariant rules' (`headOf` names them `se`, `ie`). -/
def updFresh? (n : String) : Option (Lean.Term × Lean.Term) :=
  let k := schemaIdent "k"
  match stemOf n with
  | "b" => some (Lean.Syntax.mkApp (mkIdent ``Var.fresh) #[Lean.Syntax.mkStrLit "se", k],
      Lean.mkCIdent ``PrimTy.bool)
  | "variant" => some (Lean.Syntax.mkApp (mkIdent ``Var.fresh) #[Lean.Syntax.mkStrLit "ie", k],
      Lean.mkCIdent ``PrimTy.uint)
  | _ => none

/-- A scoped update: its elements `snoc`ed onto `Upd.nil` in order, every
right-hand side read in `Γ`; the local the `\find` declares (`found`), and
an invariant rule's `b` and `variant` (`updFresh?`), declared (`Upd.decl`),
the scope after it returned. -/
def schemaUpdCore (Γ : Scope) (found : Option String) (U : TSyntax `dl_upd) :
    MacroM (Lean.Term × Scope) := do
  if let `(dl_upd| ‹ $t:term ›) := U then return (t, Γ)
  let mut acc : Lean.Term := Lean.mkCIdent `Solidity.Upd.nil
  let mut Γ' := Γ
  for e in U.raw[1].getSepArgs do
    match (⟨e⟩ : TSyntax `dl_upd_elem) with
    | `(dl_upd_elem| pay($_:dl_term, $_:dl_term)) =>
      acc ← `($(Lean.mkCIdent `Solidity.Upd.snoc) $acc $(← schemaUpdElem Γ ⟨e⟩))
    | `(dl_upd_elem| $l:dl_term := $r:dl_term) =>
      let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
      let n := x.getId.toString
      if found == some n then
        acc ← `($(Lean.mkCIdent `Solidity.Upd.decl) $acc $x $(← schemaRhsCore Γ x r))
        Γ' := (n, .val x) :: Γ'
      else if let some (v, p) := updFresh? n then
        acc ← `($(Lean.mkCIdent `Solidity.Upd.decl) $acc $v
          ($(Lean.mkCIdent `Solidity.Rhs.val) (p := $p) $(← schemaTerm Γ .val r)))
        Γ' := (n, .val v) :: Γ'
      else if ["storage", "memory", "net", "selfBalance"].contains n then
        acc ← `($(Lean.mkCIdent `Solidity.Upd.snoc) $acc $(← schemaUpdElem Γ ⟨e⟩))
      else
        -- the target a local of the scope after the declarations so far
        let tgt ← match headOf Γ' x with
          | .local v | .alias v | .mem v _ => pure v
          | _ => Macro.throwErrorAt x "an update assigns a local, an alias, a memory local, \
              `storage` or `memory`"
        acc ← `($(Lean.mkCIdent `Solidity.Upd.snoc) $acc
          ($(Lean.mkCIdent `Solidity.UpdElem.local) $tgt $(← schemaRhsCore Γ x r)))
    | _ => Macro.throwErrorAt e "a scoped taclet's update has no update variable"
  return (acc, Γ')

/-- `Solidity.Fml.c`, a constructor of the scoped formulas, by its full
name, so that `coreNames` leaves it as it is. -/
def fmlC (c : String) : Lean.Term := Lean.mkCIdent (`Solidity.Fml ++ Name.mkSimple c)

/-- A scoped formula, its names read in `Γ`: a fresh local an update in it
declares (`{ b := cond } (b = TRUE → …)`) is a position in the formula after
it.  The forms the rule lines write. -/
partial def schemaFmlCore (Γ : Scope) : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| true) => pure (fmlC "tt")
  | `(dl_fml| false) => `($(fmlC "not") $(fmlC "tt"))
  | `(dl_fml| $a:dl_term != $b:dl_term) => do
    `($(fmlC "not") ($(fmlC "eq") $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b)))
  | `(dl_fml| $a:dl_term = $b:dl_term) => do
    if let `(dl_term| $c:ident) := b then
      let n := c.getId.toString
      -- a loop's invariant: `inv` read `true` and its quantified clauses `qs`
      -- (`invFml`, solkey's `\getInvariant`), under the scope's locals
      if let `(dl_term| $i:ident) := a then
        if n == "TRUE" && i.getId.toString == "inv" && (Γ.lookup "inv").isNone then
          let d := Γ.depth
          let qs := (List.range d).foldl (fun (acc : Lean.Term) _ =>
            Lean.Syntax.mkApp (Lean.mkCIdent ``List.map) #[Lean.mkCIdent `Solidity.LoopQ.up, acc])
            (schemaIdent "qs")
          return ← `($(Lean.mkCIdent `Solidity.invFml) $(iterApp `Solidity.Val.up d i) $qs)
      if n == "TRUE" || n == "FALSE" then
        let v := mkIdent (Name.mkSimple (if n == "TRUE" then "true" else "false"))
        return ← `($(fmlC "eq") $(← schemaTerm Γ .val a) (Term.litB $v))
    `($(fmlC "eq") $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_fml| ¬ $φ:dl_fml) => do `($(fmlC "not") $(← schemaFmlCore Γ φ))
  | `(dl_fml| $φ:dl_fml ∧ $ψ:dl_fml) => do
    `($(fmlC "and") $(← schemaFmlCore Γ φ) $(← schemaFmlCore Γ ψ))
  | `(dl_fml| $φ:dl_fml → $ψ:dl_fml) => do
    `($(fmlC "imp") $(← schemaFmlCore Γ φ) $(← schemaFmlCore Γ ψ))
  | `(dl_fml| $U:dl_upd $φ:dl_fml) => do
    let m ← match ← fmlModality? (schemaIdent "m") φ with
      | some m => pure m
      | none => `(Modality.diamond)
    let (U, Γ') ← schemaUpdCore Γ none U
    `($(fmlC "upd") $m $U $(← schemaFmlCore Γ' φ))
  | `(dl_fml| ( $φ:dl_fml )) => schemaFmlCore Γ φ
  | `(dl_fml| ‹ $t:term ›) => pure t
  | `(dl_fml| $x:ident) => pure x
  | `(dl_fml| $a:dl_term <= $b:dl_term) => do
    `($(fmlC "eq") (Term.binop BinOp.le PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
        (Term.litB true))
  | `(dl_fml| $a:dl_term < $b:dl_term) => do
    `($(fmlC "eq") (Term.binop BinOp.lt PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
        (Term.litB true))
  | φ => Macro.throwErrorAt φ "no scoped reading of this formula yet"

/-- The invariant rule's premise: the invariant now;
the body's frame (`xs`, `hv`, bound by the side condition
`Prog.frame body = some (xs, hv)`); the update of the condition's value `b`
(and under the diamond the variant's `variant`), the conditions read after
it; the body and its postcondition read where `b` is popped (`hb`), the
variant kept above the loop's context (`hu`). -/
def schemaInvCore (i : TSyntax `dl_fml) (b : TSyntax `sol_block) (h : TSyntax `dl_fml)
    (U : TSyntax `dl_upd) (c : TSyntax `dl_fml) (t : TSyntax `sol_block)
    (post c' : TSyntax `dl_fml) (B : Option Lean.Term := none) : MacroM Lean.Term := do
  unless i.raw.structEq h.raw do
    Macro.throwErrorAt h "the invariant assumed is the one shown initially valid"
  unless b.raw.structEq t.raw do
    Macro.throwErrorAt t "the frame is the body's, which the goal runs"
  let (Ut, Γu) ← schemaUpdCore coreScope none U
  -- the body's scope: the update's locals but `b`
  let Γ₀ : Scope := Γu.filter (·.1 != "b")
  let hu ← extPush (Scope.depth Γ₀)
  let hb ← extPush (Scope.depth Γu - Scope.depth Γ₀)
  let B ← match B with
    | some B => pure B
    | none => `(Option.none)
  `($(Lean.mkCIdent `Solidity.Premise.inv) $(← schemaFmlCore coreScope i) $B
      $(schemaIdent "xs") $(schemaIdent "hv") $Ut $(← schemaFmlCore Γu c) $(← schemaFmlCore Γu c')
      $hu $hb $(← schemaBlock true Γ₀ t) $(← schemaFmlCore Γ₀ post))

/-- `expand_function_body(fbs)`, a whole premise. -/
def expandBody? : TSyntax `sol_stmt → Bool
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) =>
    match f with
    | `(sol_expr| $g:ident) =>
      g.getId.toString == "expand_function_body" && (stemOfExpr? a).any isCallStem
    | _ => false
  | _ => false

/-- A scoped premise.  `Γ` is the scope after the `\find`, `found` the local
it declares (its name and its variable), `split` how a split's goals end. -/
def schemaPremiseCore (Γ : Scope) (found : Option (String × Lean.Term)) (split : Lean.Term) :
    TSyntax `dl_premise → MacroM Lean.Term
  | `(dl_premise| lexInvariant($I:sol_expr, ‹$metrics:term›, $c:sol_expr, $body:sol_block)) => do
    `($(Lean.mkCIdent `Solidity.LoopLex.diamondPremise) $(schemaIdent "k")
      $(← schemaAt coreScope .val I) $(← schemaAt coreScope .val c) $metrics
      $(← schemaBlock false coreScope body) $(schemaIdent "xs") $(schemaIdent "hv"))
  | `(dl_premise| if $c:dl_fml then ($U:dl_upd $V:dl_upd ⟨[ ]⟩) else (⟨[ revert(); ]⟩)) => do
    let (Ut, Δ) ← schemaUpdCore coreScope none U
    let (Vt, _) ← schemaUpdCore Δ none V
    let ct ← match c with
      | `(dl_fml| $a:dl_term != 0) => do
        let lhsTerm ← schemaTerm coreScope .val a
        `($(fmlC "not") ($(fmlC "eq") $lhsTerm
          ($(Lean.mkCIdent `Solidity.Tm.zeroLike) $lhsTerm)))
      | _ => schemaFmlCore coreScope c
    `($(Lean.mkCIdent `Solidity.Premise.guardedUpdates) $ct $Ut $Vt)
  | `(dl_premise| $U:dl_upd $V:dl_upd ⟨[ ]⟩) => do
    let declared := found.map (·.1)
    let inFirst := declared.filter fun n => U.raw[1].getSepArgs.any fun e =>
      match (⟨e⟩ : TSyntax `dl_upd_elem) with
      | `(dl_upd_elem| $x:ident := $_:dl_term) => x.getId.toString == n
      | _ => false
    let (Ut, Δ) ← schemaUpdCore coreScope inFirst U
    let (Vt, _) ← schemaUpdCore Δ (if inFirst.isSome then none else declared) V
    `($(Lean.mkCIdent `Solidity.Premise.updates) $Ut $Vt)
  | `(dl_premise| $U:dl_upd ⟨[ ]⟩) => do
    `($(Lean.mkCIdent `Solidity.Premise.update)
      $((← schemaUpdCore coreScope (found.map (·.1)) U).1))
  | `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) => do
    if ss.size == 1 && expandBody? ss[0]! then
      -- a call inlined: the premise `Stmt.step` builds (`Premise.expandCall`)
      return ← `($(Lean.mkCIdent `Solidity.Premise.expandCall) $(schemaIdent "k")
        $(schemaIdent "args") $(schemaIdent "ret") $(schemaIdent "body"))
    let (ts, Γ') ← schemaProg true Γ ss
    let P ← progTermCore ts
    match found with
    | some (_, x) => `($(Lean.mkCIdent `Solidity.Premise.bind) $x _ $P)
    | none => `($(Lean.mkCIdent `Solidity.Premise.unfold) $P $(← extPush (Γ'.depth - Γ.depth)))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ ; $[$_:str :]? $nc:dl_fml ⟹ ⟨[ $f:sol_block ]⟩) => do
    `($(Lean.mkCIdent `Solidity.Premise.split) $split $(← schemaFmlCore coreScope c) $(← schemaFmlCore coreScope nc)
        $(← schemaBlock true Γ t) $(← schemaBlock true Γ f))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $[$ts:sol_stmt;]* ]⟩ ;
      $[$_:str :]? $nc:dl_fml ⟹ ⟨[ $[$fs:sol_stmt;]* ]⟩) => do
    let (ts, _) ← schemaProg true Γ ts
    let (fs, _) ← schemaProg true Γ fs
    `($(Lean.mkCIdent `Solidity.Premise.split) $split $(← schemaFmlCore coreScope c) $(← schemaFmlCore coreScope nc)
        $(← progTermCore ts) $(← progTermCore fs))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $[$ts:sol_stmt;]* ]⟩ ; $[$_:str :]? $c':dl_fml) => do
    unless c.raw.structEq c'.raw do
      Macro.throwErrorAt c' "a check assumes the condition it checks: write it on both sides"
    unless ts.isEmpty do Macro.throwErrorAt c "a scoped check goes on with the rest of the program"
    `($(Lean.mkCIdent `Solidity.Premise.check) $(← schemaFmlCore coreScope c))
  | `(dl_premise| true) => `($(Lean.mkCIdent `Solidity.Premise.done) true)
  | `(dl_premise| false) => `($(Lean.mkCIdent `Solidity.Premise.done) false)
  | `(dl_premise| $b:dl_branch ; $bs:dl_branch;*) => do
    let bs ← (#[b] ++ bs.getElems).mapM (schemaBranch true coreScope)
    `($(Lean.mkCIdent `Solidity.Premise.branches) [$bs,*])
  | `(dl_premise| $c:dl_case ; $cs:dl_case;*) => do
    let mut fs : Array Lean.Term := #[]
    let mut us : Array Lean.Term := #[]
    for c in #[c] ++ cs.getElems do
      match c with
      | `(dl_case| $[$_:str :]? $U:dl_upd ⟨[ ]⟩) => us := us.push (← schemaUpdCore coreScope none U).1
      | `(dl_case| $[$_:str :]? $φ:dl_fml) =>
        unless us.isEmpty do Macro.throwErrorAt c "the formula goals come first"
        fs := fs.push (← schemaFmlCore coreScope φ)
      | _ => Macro.throwUnsupported
    `($(Lean.mkCIdent `Solidity.Premise.cases) [$fs,*] [$us,*])
  | `(dl_premise| $[$_:str :]? $i:dl_fml ; $[$_:str :]? { anon($b:sol_block) } ($h:dl_fml →
      $U:dl_upd ($c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ $post:dl_fml ; $c':dl_fml ⟹ ⟨[ ]⟩))) => do
    schemaInvCore i b h U c t post c'
  | `(dl_premise| $[$_:str :]? $i:dl_fml ; $[$_:str :]? { anon($b:sol_block) } ($h:dl_fml ∧ ¬$k₁:dl_fml →
      $U:dl_upd ($c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ (¬$k₂:dl_fml → $post:dl_fml) ∧ ($k₃:dl_fml → ⟨[ ]⟩) ;
        $c':dl_fml ⟹ ⟨[ ]⟩))) => do
    -- the break test is the one `Stmt.step` computes (`loopBreak`), named
    -- `broke` as solkey names it
    for k in [k₁, k₂, k₃] do
      let named := match k with
        | `(dl_fml| $x:ident) => x.getId.toString == "broke"
        | _ => false
      unless named do Macro.throwErrorAt k "a loop's break test is written `broke`"
    unless post.raw.structEq h.raw do
      Macro.throwErrorAt post "a body that does not break keeps the invariant"
    -- the invariant initially valid, the flag not set
    let i ← match i with
      | `(dl_fml| $i:dl_fml ∧ ¬$k₀:dl_fml) =>
        unless k₀.raw.structEq k₁.raw do
          Macro.throwErrorAt k₀ "a loop's break test is written `broke`"
        pure i
      | _ => Macro.throwErrorAt i "the loop starts with the invariant and its flag not set"
    schemaInvCore i b h U c t post c'
      (some (← `($(Lean.mkCIdent `Solidity.loopBreak) $(schemaIdent "brk") $(schemaIdent "cond"))))
  | p => Macro.throwErrorAt p "no scoped reading of this premise yet"

/-- A compound assignment's operator terms: `l ⊕ se` in `l ⊕= se`'s premise
takes `⊕=`'s proofs (`hop` that it has a compound form, `hp` that the type is
numeric), not `Val.binop`'s (`hop`, `hq`): `Term.binopS … hq` becomes
`Term.binopC … hp`. -/
partial def compoundOps : Syntax → Syntax
  | stx@(.ident _ _ val _) =>
    let v := val.eraseMacroScopes
    if v == `Term.binopS then (mkIdentFrom stx `Term.binopC).raw
    else if v == `hq then (mkIdentFrom stx `hp).raw
    else stx
  | .node i k args => .node i k (args.map compoundOps)
  | stx => stx

/-- Instantiate a fixed push operator in its otherwise shared replacement
shape; its appended index is always a dynamic-array index. -/
partial def specializePush (op proof index : Syntax) : Syntax → Syntax
  | stx@(.ident _ _ val _) =>
    match val.eraseMacroScopes with
    | `op => op
    | `hop => proof
    | `it => index
    | _ => stx
  | .node i k args => .node i k (args.map (specializePush op proof index))
  | stx => stx

/-- The indexed primitive read in a push suffix replacement, excluding its
`size` reads. `sp.push() += se` determines the arithmetic's numeric type;
the index arithmetic remains `uint`. -/
def pushValueRead : TSyntax `dl_term → Bool
  | `(dl_term| find($_, $_:dl_term[$_:dl_term])) => true
  | `(dl_term| find($_, consr($_, at($_)))) => true
  | _ => false

/-- Read the literal arithmetic of a native push rule at its target type.
Only the matching operator on the appended primitive is specialized: a
`size + 1` or `size - 1` still uses the ordinary `uint` term reader. -/
partial def pushArithmetic (compound : Bool) (sym : String) (s : Syntax) : MacroM Syntax := do
  let .node info kind args := s | return s
  let s := Syntax.node info kind (← args.mapM (pushArithmetic compound sym))
  let bin : Option (String × TSyntax `dl_term × TSyntax `dl_term) := match (⟨s⟩ : TSyntax `dl_term) with
    | `(dl_term| $a + $b) => some ("+", a, b)
    | `(dl_term| $a - $b) => some ("-", a, b)
    | `(dl_term| $a * $b) => some ("*", a, b)
    | `(dl_term| $a / $b) => some ("/", a, b)
    | `(dl_term| $a % $b) => some ("%", a, b)
    | _ => none
  let some (actual, a, b) := bin | return s
  unless actual == sym && pushValueRead a do return s
  if compound then return (← `(dl_term| $a ⊕ $b)).raw
  if let `(dl_term| 1) := b then return (← `(dl_term| $a ± $b)).raw
  return s

/-- The literal arithmetic symbol supplied by a native push statement. -/
def pushOperatorSymbol (op : Lean.Term) : String :=
  match op with
  | `($name:ident) =>
    match name.getId.eraseMacroScopes.getString! with
    | "add" | "preInc" | "postInc" => "+"
    | "sub" | "preDec" | "postDec" => "-"
    | "mul" => "*" | "div" => "/" | "mod" => "%"
    | _ => ""
  | _ => ""

/-- Whether a statement is a compound assignment `l ⊕= r`. -/
def isCompound : TSyntax `sol_stmt → Bool
  | `(sol_stmt| $_:sol_expr ⊕= $_:sol_expr) => true
  | _ => false

/-- The receiver and argument of either spelling of `sp.push(arg)`. -/
def valuePushParts? : TSyntax `sol_stmt → MacroM (Option (TSyntax `sol_expr × TSyntax `sol_expr))
  | `(sol_stmt| $b:sol_expr .push( $a:sol_expr )) => pure (some (b, a))
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) => do
    let some (b, "push") ← callRecv? f | pure none
    pure (some (b, a))
  | _ => pure none

/-- The operation in either spelling of `fc.push(e)`, `fc.push()` or `fc.pop()`. -/
def receiverParts? (s : TSyntax `sol_stmt) :
    MacroM (Option (TSyntax `sol_expr × Option (TSyntax `sol_expr) × Bool)) := do
  if let some (b, a) ← valuePushParts? s then return some (b, some a, false)
  match s with
  | `(sol_stmt| $b:sol_expr .push()) => return some (b, none, false)
  | `(sol_stmt| $b:sol_expr .pop()) => return some (b, none, true)
  | `(sol_stmt| $f:sol_expr ( )) =>
    let some (b, method) ← callRecv? f | return none
    if method == "push" then return some (b, none, false)
    if method == "pop" then return some (b, none, true)
    return none
  | _ => return none

/-- A native call-receiver capture. The two written statements must retain
the same getter, operation and operand, and bind the fresh `sp` they use. -/
def callReceiverTaclet? (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise) :
    MacroM (Option (Lean.Term × Lean.Term)) := do
  let some (fc, arg, pop) ← receiverParts? s | return none
  unless (singleVar? fc).any (fun n => stemOf n == "fc") do return none
  let `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) := p |
    Macro.throwErrorAt p "a call receiver is captured in `sp` before its array operation"
  unless ss.size == 2 do
    Macro.throwErrorAt p "a call-receiver capture has a declaration and its array operation"
  let `(sol_stmt| $aliasType:sol_ty storage $sp:ident = $getter:sol_expr) := ss[0]! |
    Macro.throwErrorAt ss[0]! "a call receiver is bound as a storage alias"
  let _ := aliasType
  unless stemOf sp.getId.toString == "sp" && fc.raw.structEq getter.raw do
    Macro.throwErrorAt ss[0]! "the fresh `sp` captures the getter of the find"
  let some (recv, arg', pop') ← receiverParts? ss[1]! |
    Macro.throwErrorAt ss[1]! "the captured receiver is pushed or popped"
  let sameArg := match arg, arg' with
    | none, none => true
    | some a, some b => a.raw.structEq b.raw
    | _, _ => false
  unless singleVar? recv == some sp.getId.toString && pop == pop' && sameArg do
    Macro.throwErrorAt ss[1]! "the replacement keeps the operation and operand on fresh `sp`"
  if let some a := arg then
    let some n := singleVar? a |
      Macro.throwErrorAt a "the call-receiver operand is a typed source schema variable"
    let st ← `($(Lean.mkCIdent `Solidity.ReceiverValue.statement) $(schemaIdent "f")
      $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body") $(schemaIdent n))
    let pt ← `($(Lean.mkCIdent `Solidity.ReceiverValue.step) $(schemaIdent "k")
      $(schemaIdent "f") $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body")
      $(schemaIdent n))
    return some (st, pt)
  let op ← if pop then `($(Lean.mkCIdent `Solidity.ReceiverOp.pop)) else
    match arg with
    | none => `($(Lean.mkCIdent `Solidity.ReceiverOp.push) none $(schemaIdent "hd"))
    | some a =>
      let some n := singleVar? a |
        Macro.throwErrorAt a "the call-receiver operand is a typed source schema variable"
      `($(Lean.mkCIdent `Solidity.ReceiverOp.push) (some $(schemaIdent n)) rfl)
  let st ← `($(Lean.mkCIdent `Solidity.Stmt.callReceiver) $(schemaIdent "f")
    $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body") $op)
  let pt ← `($(Lean.mkCIdent `Solidity.callReceiverStep) $(schemaIdent "k")
    $(schemaIdent "f") $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body") $op)
  return some (st, pt)

/-- Recognise the exact upstream `whileUnwind` shape, retaining a typed proof-search mode. -/
def whileUnwindTaclet? (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise) :
    MacroM (Option (Lean.Term × Lean.Term)) := do
  let rec plain : Syntax → Syntax
    | .ident info raw name _ => .ident info raw name.eraseMacroScopes []
    | .node info kind args => .node info kind (args.map plain)
    | stx => stx
  let find ← `(sol_stmt| while (cond) body)
  unless (plain s.raw).structEq (plain find.raw) do return none
  let expected ← `(dl_premise| ⟨[ if (cond) { body; while (cond) body; }; ]⟩)
  unless (plain p.raw).structEq (plain expected.raw) do return none
  let c ← schemaAt coreScope .val ⟨s.raw[2]⟩
  let body ← schemaBlock false coreScope ⟨s.raw[4]⟩
  let st ← `($(Lean.mkCIdent `Solidity.Stmt.loop)
    ($(Lean.mkCIdent `Solidity.LoopUnwind.before) $(schemaIdent "u")) $c $body)
  let pt ← `($(Lean.mkCIdent `Solidity.loopUnwindStep) $(schemaIdent "u") $c $body)
  return some (st, pt)

/-- The taclet `s ⇝ p` under modality `m`: the find binds schema variables;
the replacement reads them and introduces its own fresh declarations. -/
def schemaTacletCore (m : Lean.Term) (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise)
    (J : Option Lean.Term := none) : MacroM Lean.Term := do
  let receiver ← callReceiverTaclet? s p
  let native ← if receiver.isSome then pure receiver else whileUnwindTaclet? s p
  let conds ← sideConds s
  -- A value declaration in this capture replacement identifies a primitive
  -- source. A storage declaration instead keeps the reference-copy reading.
  let primitive : Option (TSyntax `sol_expr × TSyntax `sol_expr) ← do
    let some (b, a) ← valuePushParts? s | pure none
    let `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) := p | pure none
    if ss.size != 2 then pure none else do
      let `(sol_stmt| $sourceTy:sol_ty $source:ident = $r:sol_expr) := ss[0]! | pure none
      let _ := sourceTy
      let some (b', v) ← valuePushParts? ss[1]! | pure none
      if isPath coreScope a && a.raw.structEq r.raw && b.raw.structEq b'.raw &&
          (singleVar? v) == some source.getId.toString then pure (some (b, a)) else pure none
  let (st, Γ) ← match native, primitive with
    | some (st, _), _ => pure (st, coreScope)
    | none, some (b, a) => do
      let src ← schemaAt coreScope .spath a
      let recv ← schemaAt coreScope .spath b
      pure (← `(Stmt.push $recv (some (Src.val (SPath.primitiveRead $src))) rfl), coreScope)
    | none, none => schemaStmt false coreScope s
  let found : Option (String × Lean.Term) := match Γ with
    | (n, .val v) :: _ | (n, .alias v) :: _ | (n, .mem v _) :: _ => some (n, v)
    | _ => none
  let split := match s with
    | `(sol_stmt| if ($_:sol_expr) $_:sol_block else $_:sol_block) =>
      Lean.mkCIdent `Solidity.BlockKind.block
    | _ => Lean.mkCIdent `Solidity.BlockKind.capture
  let fixed ← fixedPushOperator? s
  let p : TSyntax `dl_premise ← match fixed with
    | none => pure p
    | some (op, compound) => do pure ⟨← pushArithmetic compound (pushOperatorSymbol op) p⟩
  let pt ← match native with
    | some (_, pt) => pure pt
    | none => schemaPremiseCore Γ found split p
  let pt : Lean.Term := if isCompound s || fixed.any (·.2) then ⟨compoundOps pt⟩ else pt
  let pt : Lean.Term ← match fixed with
    | none => pure pt
    | some (op, _) => do
      pure ⟨specializePush op (← `(by rfl)) (← `(IndexTy.arr ArrTy.dyn)) pt⟩
  let st ← `(($st : $(Lean.mkCIdent `Solidity.Stmt) $(schemaIdent "C") $(schemaIdent "Γ") _))
  let jArgs : Array Lean.Term := #[schemaIdent "C", schemaIdent "k"]
  let ((f, args) : Ident × Array Lean.Term) ← match J with
    | none => pure (mkIdent `Taclet, jArgs)
    | some J => match J with
      | `($f:ident $args*) => pure (f, args)
      | `($f:ident) => pure (f, #[])
      | _ => Macro.throwErrorAt J "`dl[J]{ … }` names a judgement: `LeanTaclet C k`"
  let t ← `($f:ident $args* $m $st $pt)
  let t ← if conds.isEmpty then pure t else
    let hs := conds.map (·.1)
    let cs := conds.map (·.2)
    `(taclet_side% $t $[($hs : $cs)]*)
  return ⟨← coreNames t⟩

/-- A quantifier's type written by name: `uint`, `int`, `bool`, or a Lean term. -/
def schemaPrim (T : Ident) : MacroM Lean.Term :=
  match T.getId.toString with
  | "uint" => `(PrimTy.uint)
  | "int" => `(PrimTy.int)
  | "bool" => `(PrimTy.bool)
  | _ => pure T

end Expand

namespace Schema

/-- Under `open scoped Solidity.Schema`, a taclet line writes a scoped
taclet (`schemaTacletCore`): the same text, the `Taclet` (or the judgement
named) in scope where it is used. -/
scoped macro_rules
  | `(dl{ if $c:dl_fml then ($U:dl_upd $V:dl_upd ⟨[ ]⟩) else (⟨[ revert(); ]⟩) }) => do
    let t ← schemaPremiseCore coreScope none (← `(BlockKind.capture))
      (← `(dl_premise| if $c:dl_fml then ($U:dl_upd $V:dl_upd ⟨[ ]⟩) else (⟨[ revert(); ]⟩)))
    coreNames t
  | `(dl{ $U:dl_upd $V:dl_upd ⟨[ ]⟩ }) => do
    schemaPremiseCore coreScope none (← `(BlockKind.capture))
      (← `(dl_premise| $U:dl_upd $V:dl_upd ⟨[ ]⟩))
  | `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => schemaTacletCore (schemaIdent "m") s p
  | `(dl{ [ $s:sol_stmt; ] ⇝ $p:dl_premise }) => do schemaTacletCore (← `(Modality.box)) s p
  | `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p:dl_premise }) => do schemaTacletCore (← `(Modality.diamond)) s p
  | `(dl[ $J:term ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => schemaTacletCore (schemaIdent "m") s p J
  | `(dl[ $J:term ]{ [ $s:sol_stmt; ] ⇝ $p:dl_premise }) => do
    schemaTacletCore (← `(Modality.box)) s p J
  | `(dl[ $J:term ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p:dl_premise }) => do
    schemaTacletCore (← `(Modality.diamond)) s p J

end Schema

section Side
open Lean Elab Term

elab_rules : term
  | `(taclet_side% $t $[($hs : $cs)]*) => do
    let T ← elabType t
    let mut hyps : Array (Lean.Name × Expr) := #[]
    for h in hs, c in cs do
      hyps := hyps.push (h.getId, ← elabType c)
    return hyps.foldr (init := T) fun (n, ty) b =>
      .forallE n (mkApp2 (mkConst ``autoParam [levelZero]) ty (mkConst ``Solidity.sideCond)) b
        .default

end Side

end Solidity
