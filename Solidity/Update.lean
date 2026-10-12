import Solidity.Semantics.Agree
import Solidity.Semantics.WellFormed
import Solidity.TermSimp
import Solidity.Theory.Abs

/-!
# Terms, updates, formulas

After a rule fires, the calculus talks about *terms* of the logic, not about
program expressions (mini-solkey's `Ch05_Logic`).  The sorts are KeY's:

* `Term` — a value: a constant, a stack local, `a + b`, `find(s, p)`,
  `read(m, a)`, the length of an array, what the ledger holds, `net(a)`;
* `PTerm` — a storage path: a state variable, an alias, `p.f`, `p[i]`;
* `STerm` — a storage: the program variable `storage`, a storage variable
  (`old`, which `\old` reads), `save(s, p, v)`, `delAt(s, p)`, a push and a
  pop (KeY's nested `save`s over `size`);
* `ITerm`, `MAddr`, `MTerm` — a memory identity, a member or element of one,
  a memory: `memory`, `write(m, a, v)`, `addM(m)`, `copySt(m, v)`.

**Updates are terms.**  `{storage := save(storage, alice.age, 3)}` is a list
of elementary updates, applied in parallel: every right-hand side is read in
the state the update is applied in.  Nothing runs when a rule produces one.

This module holds the signature (`Srt`, `Op0` … `Op3`) and what each
symbol means (`OpN.eval`, `OpN.denote`); the terms are the scoped
calculus's (`Calculus/Fml.lean`: `Tm C Γ s`, its locals at positions), and
the notation reads a formula's text to them by name
(`Calculus/NamedTerm.lean`, `Calculus/NotationResolve.lean`).

Unlike KeY's, these terms can halt: they are read by the interpreter's own
functions, so `a + b` reverts on overflow and `values[i]` on an index out of
range, exactly as the statement they came from.  An update therefore
carries the modality of the goal it was produced in, and `{U} φ` with a
halting `U` is judged as the halting statement would be.  It prints as
`{U}` all the same; `dl{ … }` reads the modality back off the formula
under it.
-/

namespace Solidity

open Semantics

/-- The two modalities: the diamond `⟨ P ⟩ φ` and the box `[ P ] φ`. -/
inductive Modality where
  | diamond
  | box
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- What a modality says of a run that reverts (or is `undef`): every box
formula holds of it, no diamond formula does. -/
def Modality.onHalt : Modality → Prop
  | .diamond => False
  | .box => True

/-- `p` after a run under `m`: `p` of the state it ends in, or `m.onHalt`.
An update reads so: a term never panics (`Upd.apply_noPanic`). -/
def Modality.after (m : Modality) (p : State → Prop) : Res State → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-! ## Terms

One signature, KeY's: a sort (`Srt`) per kind of term, and function symbols
by arity (`Op0` … `Op3`), each indexed by the sorts of its arguments and of
its result.  A term (`Tm C s`) is a variable of a sort that has them, or a
symbol applied to terms of its argument sorts.  So every traversal — what a
term reads (`Tm.vars`), substitution, replacing a subterm — is written once,
for the four arities, and a new symbol is a constructor of an `Op` and its
meaning (`OpN.eval`, `OpN.denote`), nothing more.

The sorts keep KeY's names (`Term`, `PTerm`, `STerm`, …, in the
docstrings below). -/

/-- The sorts of terms. -/
inductive Srt where
  /-- `Term`: a value. -/
  | val
  /-- `PTerm`: a storage path. -/
  | path
  /-- `STerm`: a storage. -/
  | st
  /-- `SValT`: what a storage `save` writes. -/
  | sv
  /-- `ITerm`: a memory identity. -/
  | ident
  /-- `MAddr`: a member or an element of a memory object. -/
  | addr
  /-- `MTerm`: a memory. -/
  | mem
  /-- `MValT`: what a memory `write` writes. -/
  | mv
  deriving DecidableEq, Repr

/-- Constants. -/
inductive Op0 : Srt → Type where
  | lit (v : Value) : Op0 .val
  /-- `msgSender`, `msgValue`, `selfBalance`: KeY's program variables of
  `netHeader.key`, and `block.timestamp`. -/
  | env (k : EnvKey) : Op0 .val
  | root (r : Name) : Op0 .path
  | storage : Op0 .st
  | memory : Op0 .mem
  /-- `mtSt`: KeY's empty storage, a deployment's (`structRules.key`'s
  `selectOnEmptyStorage` reads the default anywhere in it).  Here every root
  of `vs`, the contract's, is present at its type's default
  (`Contract.initStorage`): reads agree, which is all a formula sees. -/
  | mtSt (vs : List (Name × Ty)) : Op0 .st
  deriving DecidableEq, Repr

/-- Unary symbols. -/
inductive Op1 : Srt → Srt → Type where
  | unop (op : UnOp) (p : PrimTy) : Op1 .val .val
  /-- `net(a)`: what the ledger holds for the address `a`, KeY's
  `selectSt(net, at(a))`; `0` where it never booked `a`. -/
  | net : Op1 .val .val
  /-- `x[a]`: what the ledger bound at `x` holds for `a`, KeY's
  `selectSt(oldNet, at(a))`, which a specification's `\old(net(a))` reads. -/
  | netOf (x : Var) : Op1 .val .val
  /-- `delValue(t)`: the default of the word `t`, what a delete leaves at a
  word (`Theory.delValue`).  solkey replaced its `delValue<[α]>` by
  `delField<[α]>(st, a)`, which is `delValue(selectSt(st, a))` here. -/
  | delValue : Op1 .val .val
  | field (f : Name) : Op1 .path .path
  /-- `p[p.length]`: the slot one past the end, where `lsv = p.push()` binds
  its alias (KeY's `consr(p, at(find(storage, consr(p, size))))`).  No bounds
  check: it is past them by construction. -/
  | next : Op1 .path .path
  /-- `select(s, r)`: the struct at member `r` of `s`, KeY's
  `selectSt<[Struct]>(s, r)`.  No program writes it: it is a line of a read
  taken head first, as solkey reads `find(s, cons(r, flds))`. -/
  | select (r : Name) : Op1 .st .st
  /-- `SValT.val`: a value written. -/
  | sval : Op1 .val .sv
  /-- `newArr(n)`: an array of `n` defaults of `R`'s element type, what
  `new R(n)` copies into memory (`newArrVal`). -/
  | newArr (R : RefTy) : Op1 .val .sv
  /-- `freshId(addM(m))`: the identity allocating a default `R` takes. -/
  | alloc (R : RefTy) : Op1 .mem .ident
  /-- `MAddr.field`: a member of a memory object. -/
  | mfield (f : Name) : Op1 .ident .addr
  /-- `addM(m)`: a default `R` allocated. -/
  | addM (R : RefTy) : Op1 .mem .mem
  /-- `MValT.val`: a value written. -/
  | mval : Op1 .val .mv
  /-- `MValT.ref`: a reference written. -/
  | ref : Op1 .ident .mv
  /-- `wt(s)`: the storage `s` holds the roots `vs`, each canonical, tight
  and with its words in range (`storageWtB`): KeY's `wellFormed(heap)`, the
  premise of an obligation (`Calculus/Problem.lean`).  It returns `true` or
  halts, so a formula states it as `defined`. -/
  | wt (vs : List (Name × Ty)) : Op1 .st .val
  deriving DecidableEq, Repr

/-- Binary symbols. -/
inductive Op2 : Srt → Srt → Srt → Type where
  /-- `a ⊕ b`, range-checked at `p` as the interpreter checks it. -/
  | binop (op : BinOp) (p : PrimTy) : Op2 .val .val .val
  /-- `find(s, p)`, KeY's `find`, at a state variable as well
  (`storageRootReadSelect`: `find(storage, gsp)`); `select(s, r)` still reads. -/
  | find : Op2 .st .path .val
  /-- `s[p].length`: KeY's `find(s, p.size)`. -/
  | len : Op2 .st .path .val
  /-- `read(m, a)`: a value in memory. -/
  | read : Op2 .mem .addr .val
  /-- `m[i].length`: KeY's `read(m, i, size)`. -/
  | mlen : Op2 .mem .ident .val
  /-- `p[i]`, the index checked against `p`'s length where it is taken
  (`State.checkIndex`), as the program checks it. -/
  | at : Op2 .path .val .path
  /-- `p[p.length]@S`: the slot one past the end, its length read in the
  storage `S` instead of the state's — `p[p.length]` merged under a storage
  write (`Tm.substSt`). -/
  | nextIn : Op2 .st .path .path
  /-- `delAt(s, p)`: the value at `p` reset to its default. -/
  | delAt : Op2 .st .path .st
  /-- `save(delAt(s, p[p.length]), p.length, p.length + 1)`: the slot a bare
  `push()` lands on, recycled or the default of `E`. -/
  | pushSlot (E : Ty) : Op2 .st .path .st
  /-- `save(delAt(s, p[p.length - 1]), p.length, p.length - 1)`. -/
  | pop : Op2 .st .path .st
  /-- `save(s, p.length, p.length - 1)`: a pop that leaves the element as it
  is, an array of mappings'. -/
  | shrink : Op2 .st .path .st
  /-- The extent write of `lsv = p.push()`: `save(s, p.length, p.length + 1)`. -/
  | extend (E : Ty) : Op2 .st .path .st
  /-- `SValT.find`: a subtree read out of a storage. -/
  | sfind : Op2 .st .path .sv
  /-- `copyMem(mtSt, m, i)`: a memory object copied back. -/
  | copyMem : Op2 .mem .ident .sv
  /-- `ITerm.read`: the reference held at a memory location. -/
  | iread : Op2 .mem .addr .ident
  /-- `freshId(copySt(m, v))`: the identity a copy of `v` takes. -/
  | copy : Op2 .mem .sv .ident
  /-- `MAddr.at`: an element of a memory array. -/
  | mat : Op2 .ident .val .addr
  /-- `copySt(m, v)`: a storage value copied in. -/
  | copySt : Op2 .mem .sv .mem
  deriving DecidableEq, Repr

/-- Ternary symbols. -/
inductive Op3 : Srt → Srt → Srt → Srt → Type where
  /-- `c ? a : b`, KeY's `if c then a else b`. -/
  | ite : Op3 .val .val .val .val
  /-- `save(s, p, v)`, KeY's `save`, at a state variable as well
  (`storageRootWriteStore`: `save(storage, gsp, se)`). -/
  | save : Op3 .st .path .sv .st
  /-- `save(save(s, p[p.length], v), p.length, p.length + 1)`. -/
  | push : Op3 .st .path .sv .st
  /-- `p[i]@S`: `p[i]` with its index checked in the storage `S` instead of
  the state's — `p[i]` merged under a storage write (`Tm.substSt`). -/
  | atIn : Op3 .st .path .val .path
  /-- `write(m, a, v)`. -/
  | write : Op3 .mem .addr .mv .mem
  deriving DecidableEq, Repr

/-! ## What terms mean

A term is read in a state `σ`; a storage or memory term denotes the state
with that storage or memory, and everything else of `σ`.  Each is the
interpreter's own operation, so a term halts where the statement it came
from halts. -/

variable {C : Contract}

/-- The slot at a memory address. -/
def readAddr (σ : State) : Addr → Res MVal
  | .memoryField id f => do
    match ← σ.getObj id with
    | .struct fields =>
      match lookupBy f fields with
      | some v => pure v
      | none => .error .undef
    | .array _ _ => .error .undef
  | .memoryIndex id i => do
    match ← σ.getObj id with
    | .array elems _ =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then pure (elems.get ⟨i.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .undef

/-- What a term of each sort reads to in the interpreter. -/
@[reducible] def Srt.Ev : Srt → Type
  | .val => Res Value
  | .path => Res (Name × List Seg)
  | .st => Res State
  | .sv => Res SVal
  | .ident => Res Nat
  | .addr => Res Addr
  | .mem => Res State
  | .mv => Res MVal

/-- A constant read in `σ`. -/
def Op0.eval (σ : State) : Op0 s → s.Ev
  | .lit v => pure v
  | .env k => pure (.int (σ.envVal k))
  | .root r => pure (r, [])
  | .storage => pure σ
  | .memory => pure σ
  | .mtSt vs => pure { σ with storage := vs.map fun (n, T) => (n, defaultForTy T) }

/-- A unary symbol read in `σ`, its argument's reading given. -/
def Op1.eval (σ : State) : Op1 a s → a.Ev → s.Ev
  | .unop op p, ra => do unopCheck op p (← applyUnOp op (← ra))
  | .net, ra => do pure (.int (σ.getNet (← (← ra).asInt)))
  | .netOf x, ra => do
    match ← σ.getEnv x with
    | .ledger l => pure (.int ((lookupBy (← (← ra).asInt) l).getD 0))
    | .val _ | .spath .. | .mref _ | .store _ | .unset => .error .undef
  | .delValue, ra => do pure (Theory.StValue.primDefault (← ra))
  | .field f, rp => do
    let (r, segs) ← rp
    pure (r, segs ++ [.field f])
  | .next, rp => do
    let (r, segs) ← rp
    match ← σ.findStorage r segs with
    | .array elems _ _ => pure (r, segs ++ [.at elems.length])
    | .prim _ | .struct _ | .map _ _ => .error .undef
  | .select r, rs => do
    let τ ← rs
    match ← τ.findStorage r [] with
    | .struct fields => pure { τ with storage := fields }
    | .prim _ | .array .. | .map .. => .error .undef
  | .sval, rt => do pure (← rt).toSVal
  | .newArr R, rn => do pure (newArrVal R (← (← rn).asInt))
  | .alloc R, rm => do
    let τ ← rm
    return (← allocDefault τ R).2
  | .mfield f, ri => do pure (.memoryField (← ri) f)
  | .addM R, rm => do
    let τ ← rm
    return (← allocDefault τ R).1
  | .mval, rt => do pure (← rt).toMVal
  | .ref, ri => do pure (.ref (← ri))
  | .wt vs, rs => do
    let τ ← rs
    if storageWtB vs τ.storage then pure (.bool true) else .error .undef

/-- A binary symbol read in `σ`, its arguments' readings given. -/
def Op2.eval (σ : State) : Op2 a b s → a.Ev → b.Ev → s.Ev
  | .binop op p, ra, rb => do evalBinop op p (← ra) rb
  | .find, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    (← τ.findStorage r segs).asValue
  | .len, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    arrayLen τ r segs
  | .read, rm, ra => do
    let τ ← rm
    (← readAddr τ (← ra)).asValue
  | .mlen, rm, ri => do
    let τ ← rm
    memArrayLen τ (← ri)
  | .at, rp, ri => do
    let (r, segs) ← rp
    let i ← (← ri).asInt
    σ.checkIndex r segs i
    pure (r, segs ++ [.at i])
  | .nextIn, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    match ← τ.findStorage r segs with
    | .array elems _ _ => pure (r, segs ++ [.at elems.length])
    | .prim _ | .struct _ | .map _ _ => .error .undef
  | .delAt, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    let cur ← τ.findStorage r segs
    τ.saveStorage r segs cur.defaultOf
  | .pushSlot E, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    pushAt τ E r segs pure
  | .pop, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    popAt τ false r segs
  | .shrink, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    popAt τ true r segs
  | .extend E, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    return (← pushPlaceAt τ E r segs).1
  | .sfind, rs, rp => do
    let τ ← rs
    let (r, segs) ← rp
    τ.findStorage r segs
  | .copyMem, rm, ri => do
    let τ ← rm
    Semantics.copyMem τ (.ref (← ri))
  | .iread, rm, ra => do
    let τ ← rm
    (← readAddr τ (← ra)).asRef
  | .copy, rm, rv => do
    let sv ← rv
    let τ ← rm
    (← copyStToM τ sv).2.asRef
  | .mat, ri, rk => do
    let id ← ri
    pure (.memoryIndex id (← (← rk).asInt))
  | .copySt, rm, rv => do
    let sv ← rv
    let τ ← rm
    return (← copyStToM τ sv).1

/-- A ternary symbol read in `σ`, its arguments' readings given. -/
def Op3.eval (_σ : State) : Op3 a b c s → a.Ev → b.Ev → c.Ev → s.Ev
  | .ite, rc, ra, rb => do pickBranch (← rc) ra rb
  | .save, rs, rp, rv => do
    let sv ← rv
    let τ ← rs
    let (r, segs) ← rp
    τ.writeStorage r segs sv
  | .push, rs, rp, rv => do
    let τ ← rs
    let (r, segs) ← rp
    pushAt τ .uint r segs fun _ => do pure (← rv).strip
  | .atIn, rs, rp, ri => do
    let τ ← rs
    let (r, segs) ← rp
    let i ← (← ri).asInt
    τ.checkIndex r segs i
    pure (r, segs ++ [.at i])
  | .write, rm, ra, rv => do
    let mv ← rv
    let τ ← rm
    writeAddr τ mv (← ra)

attribute [tm_eval] Op0.eval Op1.eval Op2.eval Op3.eval

/-- The variable a symbol carries: `netOf`'s ledger. -/
def Op1.vars : Op1 a s → List Var
  | .netOf x => [x]
  | _ => []

/-! ## What a term denotes in the Theory

`Tm.denoteT` (`Calculus/Lands.lean`) reads a formula's terms in the Theory
algebra over the storage node `State.abs σ`, total, as KeY reads them: a
read off the end of what is there is a node, not a halt.  `Tm.evalT` is the
interpreter's reading; the
term bridge (`Theory/Bridge/Denote.lean`) says the two agree wherever `eval`
returns.  An equation is read through `denote` (`holds`).

**Where it does not follow the Theory.**
- Arithmetic is the interpreter's checked arithmetic (`evalBinop`,
  `unopCheck`), and a halt reads `st mtSt` (`Res.toSt`): exact against
  `eval`, not KeY's unbounded integers.
- The memory island is not bridged: `read`, `mlen` and `SValT.copyMem`
  denote the interpreter's value, and `ITerm`/`MAddr`/`MTerm`/`MValT` have
  no `denote`.
- A path is not bounds-checked (`PTerm.at`): that is KeY's guard, a premise
  of the laws, not a halt.  `PTerm.next` reads the length in `σ`, as
  `Tm.evalT` does; `PTerm.nextIn` reads it in its storage term, and
  `PTerm.atIn` is `PTerm.at` (the check is `eval`'s alone).

Both read a symbol through `Op0.eval` … `Op3.eval` and `Op0.denote` …
`Op3.denote`.
-/

section Denote

open Theory Theory.StValue

/-- A Theory value as an interpreter result: a primitive, or a halt. -/
def Theory.StValue.toRes : StValue → Res Value
  | .prim p => .ok p
  | .st _ => .error .undef

/-- An interpreter result as a Theory value: a halt reads as nothing. -/
def Semantics.Res.toSt : Res Value → StValue
  | .ok v => .prim v
  | .error _ => .st .mtSt

/-- What a term of each sort denotes in the Theory: the memory sorts denote
nothing of their own (a memory read denotes the interpreter's value). -/
@[reducible] def Srt.Den : Srt → Type
  | .val => StValue
  | .path => List Seg
  | .st => Struct
  | .sv => StValue
  | .ident | .addr | .mem | .mv => Unit

/-- A constant in the Theory. -/
def Op0.denote (σ : State) : Op0 s → s.Den
  | .lit v => .prim v
  | .env k => .prim (.int (σ.envVal k))
  | .root r => [.field r]
  | .storage => σ.abs
  | .memory => ()
  | .mtSt vs => ({ σ with storage := vs.map fun (n, T) => (n, defaultForTy T) } : State).abs

/-- A unary symbol in the Theory, its argument's denotation given. -/
def Op1.denote (σ : State) : Op1 a s → a.Den → s.Den
  | .unop op p, da => Res.toSt (do unopCheck op p (← applyUnOp op (← da.toRes)))
  | .net, da => match da with
    | .prim (.int n) => .prim (.int (σ.getNet n))
    | _ => .st .mtSt
  | .netOf x, da => match σ.getEnv x, da with
    | .ok (.ledger l), .prim (.int n) => .prim (.int ((lookupBy n l).getD 0))
    | _, _ => .st .mtSt
  | .delValue, da => Theory.StValue.delValue da
  | .field f, dp => dp ++ [.field f]
  | .next, dp => dp ++ [.at (lenAt σ.abs dp)]
  | .select r, ds => asStruct (selectSt ds (.field r))
  | .sval, dt => dt
  | .newArr R, dn => (newArrVal R (asInt dn)).abs
  | .alloc _, _ => ()
  | .mfield _, _ => ()
  | .addM _, _ => ()
  | .mval, _ => ()
  | .ref, _ => ()
  | .wt _, _ => .prim (.bool true)

/-- A binary symbol in the Theory, its arguments' readings and denotations
given. -/
def Op2.denote (σ : State) : Op2 a b s → a.Ev → b.Ev → a.Den → b.Den → s.Den
  | .binop op p, _, _, da, db => Res.toSt (do evalBinop op p (← da.toRes) db.toRes)
  | .find, _, _, ds, dp => findSt ds dp
  | .sfind, _, _, ds, dp => findSt ds dp
  | .len, _, _, ds, dp => findSt ds (dp ++ [lengthSeg])
  | .read, rm, ra, _, _ => Res.toSt (Op2.eval σ .read rm ra)
  | .mlen, rm, ri, _, _ => Res.toSt (Op2.eval σ .mlen rm ri)
  | .at, _, _, dp, di => dp ++ [.at (asInt di)]
  | .nextIn, _, _, ds, dp => dp ++ [.at (lenAt ds dp)]
  | .delAt, _, _, ds, dp => Theory.StValue.delAt ds dp
  | .pushSlot E, _, _, ds, dp | .extend E, _, _, ds, dp =>
    pushSlotT E.isPrimitive (defaultForTy E).abs ds dp
  | .pop, _, _, ds, dp => popT ds dp
  | .shrink, _, _, ds, dp => shrinkT ds dp
  | .copyMem, rm, ri, _, _ => match Op2.eval σ .copyMem rm ri with
    | .ok w => w.abs
    | .error _ => .st .mtSt
  | .iread, _, _, _, _ => ()
  | .copy, _, _, _, _ => ()
  | .mat, _, _, _, _ => ()
  | .copySt, _, _, _, _ => ()

/-- A ternary symbol in the Theory, its arguments' denotations given. -/
def Op3.denote : Op3 a b c s → a.Den → b.Den → c.Den → s.Den
  | .ite, dc, da, db => match dc with
    | .prim (.bool true) => da
    | .prim (.bool false) => db
    | _ => .st .mtSt
  | .save, ds, dp, dv => copyTo ds dp dv
  | .push, ds, dp, dv => pushT ds dp (stripVal dv)
  | .atIn, _, dp, di => dp ++ [.at (asInt di)]
  | .write, _, _, _ => ()

attribute [tm_denote] Op0.denote Op1.denote Op2.denote Op3.denote

/-- A binop that returns on a halting right operand short-circuited, so it
returns the same on any.  `denote` hands `evalBinop` the right operand's
`toRes`, which is not `eval`'s halt where `eval` halts. -/
theorem Denote.evalBinop_of_error {op : BinOp} {p : PrimTy} {lv x : Value} {e : Halt}
    (rb : Res Value) (h : evalBinop op p lv (.error e) = .ok x) :
    evalBinop op p lv rb = .ok x := by
  unfold evalBinop at h ⊢
  split <;> simp_all only [bind, Except.bind, reduceCtorEq]

/-- A stored word read as a value abstracts to that value. -/
theorem _root_.Solidity.Semantics.SVal.abs_of_asValue {w : SVal} {x : Value}
    (h : w.asValue = .ok x) : w.abs = .prim x := by
  match w, h with
  | .prim (.int _), h => cases h; rfl
  | .prim (.bool _), h => cases h; rfl
  | .struct _, h | .array .., h | .map .., h => cases h

/-- The Theory's `int` cast agrees with the interpreter's where it returns:
an index and `newArr`'s size are read with the Theory's total cast. -/
theorem Denote.asInt_prim_of_asInt {v : Value} {i : Int} (h : v.asInt = .ok i) :
    asInt (.prim v) = i := by
  cases v <;> cases h; rfl

end Denote

/-! ## Updates -/

/-- `+` or `-` of KeY's `int`, which has no range to check: the arithmetic
of the ledger updates, where a `Term.binop` would be range-checked. -/
inductive IntOp where
  | add | sub
  deriving DecidableEq, Repr

def IntOp.apply : IntOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b

/-- The operator as a Lean term, for the quoter (`Calculus/Quote.lean`). -/
def IntOp.quote : IntOp → Lean.Expr
  | .add => Lean.mkConst ``IntOp.add
  | .sub => Lean.mkConst ``IntOp.sub

/-! ## States a callee may leave -/

/-- The state after a callback: storage and ledger replaced by what the
callee left (KeY's `{storage := storageSk ‖ net := netSk}`, fresh skolem
constants), the locals, memory and funds of the caller kept: the funds are
not a transfer's to change. -/
def Semantics.State.havoc (σ : State) (st : List (Name × SVal)) (nt : List (Int × Int)) :
    State :=
  { σ with storage := st, net := nt }

/-- A callee that changes nothing. -/
@[simp] theorem Semantics.State.havoc_self (σ : State) :
    σ.havoc σ.storage σ.net = σ := by
  cases σ; rfl

theorem Semantics.EnvAgreeExcept.havoc {ns : List Var} {σ τ : State} (h : EnvAgreeExcept ns σ τ)
    (st : List (Name × SVal)) (nt : List (Int × Int)) :
    EnvAgreeExcept ns (σ.havoc st nt) (τ.havoc st nt) :=
  ⟨rfl, h.heap, h.nextId, rfl, h.env, h.selfBalance, h.tx⟩

/-! ## States a loop iteration may leave

solkey's `#loopAnon` gives every local a loop body assigns or declares a
fresh constant (`LoopFrame`).  Here the locals `xs` are bound as `b` says,
or unbound: an untyped state may hold anything there, and a local the body
declares is unbound before the first iteration. -/

/-- The environment `e` with each local of `xs` bound as `b` says. -/
def anonEnv (b : Var → Option Binding) : List Var → List (Var × Binding) → List (Var × Binding)
  | [], e => e
  | x :: xs, e =>
    match b x with
    | some v => setBy x v (anonEnv b xs e)
    | none => (anonEnv b xs e).filter (·.1 != x)

/-- The state after an anonymising update of the locals `xs`. -/
def Semantics.State.anon (σ : State) (xs : List Var) (b : Var → Option Binding) : State :=
  { σ with env := anonEnv b xs σ.env }

theorem lookupBy_filter_self {α : Type} (x : Var) :
    (l : List (Var × α)) → lookupBy x (l.filter (·.1 != x)) = none
  | [] => rfl
  | (y, v) :: l => by
    by_cases h : y = x
    · subst h; simp only [List.filter, bne_self_eq_false]; exact lookupBy_filter_self y l
    · have h' : (y != x) = true := bne_iff_ne.2 h
      simp only [List.filter, h', lookupBy, Ne.symm h, if_false]
      exact lookupBy_filter_self x l

theorem lookupBy_filter_ne {α : Type} {x y : Var} (hne : y ≠ x) :
    (l : List (Var × α)) → lookupBy y (l.filter (·.1 != x)) = lookupBy y l
  | [] => rfl
  | (z, v) :: l => by
    by_cases h : z = x
    · subst h
      simp only [List.filter, bne_self_eq_false, lookupBy, hne, if_false]
      exact lookupBy_filter_ne hne l
    · have h' : (z != x) = true := bne_iff_ne.2 h
      simp only [List.filter, h', lookupBy]
      split
      · rfl
      · exact lookupBy_filter_ne hne l

/-- A local of `xs` reads as `b` says, any other as before. -/
theorem lookupBy_anonEnv (b : Var → Option Binding) (y : Var) :
    (xs : List Var) → (e : List (Var × Binding)) →
      lookupBy y (anonEnv b xs e) = if y ∈ xs then b y else lookupBy y e
  | [], e => by simp only [anonEnv, List.not_mem_nil, if_false]
  | x :: xs, e => by
    have ih := lookupBy_anonEnv b y xs e
    by_cases h : y = x
    · subst h
      simp only [anonEnv, List.mem_cons, true_or, if_true]
      cases hb : b y with
      | some v => exact SemanticsProperties.lookupBy_setBy_self _ _ _
      | none => exact lookupBy_filter_self _ _
    · simp only [anonEnv, List.mem_cons, h, false_or]
      cases b x with
      | some v => rw [SemanticsProperties.lookupBy_setBy_ne h, ih]
      | none => rw [lookupBy_filter_ne h, ih]

theorem Semantics.EnvAgreeExcept.anon {ns : List Var} {σ τ : State} (h : EnvAgreeExcept ns σ τ)
    (xs : List Var) (b : Var → Option Binding) :
    EnvAgreeExcept ns (σ.anon xs b) (τ.anon xs b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun n hn => by
    simp only [State.anon, lookupBy_anonEnv, h.env n hn], h.selfBalance, h.tx⟩

/-- The values of the primitive type `p`, which a quantifier ranges over. -/
def PrimTy.admits : PrimTy → Value → Prop
  | .bool, .bool _ => True
  | .uint, .int n => 0 ≤ n ∧ n < uintBound
  | .int, .int n => -intBound ≤ n ∧ n < intBound
  | _, _ => False

end Solidity
