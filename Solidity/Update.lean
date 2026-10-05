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

A formula is first-order (`=`, `¬`, `∧`, `→`, `∀`) plus `{U} φ` and the two
modalities: the diamond `⟨ P ⟩ φ` ("`P` runs to the end and φ holds after",
total correctness) and the box `[ P ] φ` ("if `P` runs to the end, φ holds
after", partial correctness).  They differ on a run that halts: it satisfies
every box formula and no diamond formula.

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

/-- What a modality says of a run that reverts (or is stuck): every box
formula holds of it, no diamond formula does. -/
def Modality.onHalt : Modality → Prop
  | .diamond => False
  | .box => True

/-- `p` after a run under `m`: `p` of the state it ends in, or `m.onHalt`.
An update reads so: a term never panics (`Upd.apply_ne_panic`). -/
def Modality.after (m : Modality) (p : State → Prop) : Res State → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-- `p` after a program's run under `m`: as `after`, and the run did not
panic.  A failed `assert` satisfies neither modality: KeY's `assertSimple`
leaves its condition as a goal under both. -/
def Modality.afterRun (m : Modality) (p : State → Prop) (r : Res State) : Prop :=
  m.after p r ∧ r ≠ .error .panic

/-! ## Terms

One signature, KeY's: a sort (`Srt`) per kind of term, and function symbols
by arity (`Op0` … `Op3`), each indexed by the sorts of its arguments and of
its result.  A term (`Tm C s`) is a variable of a sort that has them, or a
symbol applied to terms of its argument sorts.  So every traversal — what a
term reads (`Tm.vars`), substitution, replacing a subterm — is written once,
for the four arities, and a new symbol is a constructor of an `Op` and its
meaning (`OpN.eval`, `OpN.denote`), nothing more.

The sorts keep their names: `Term C` is `Tm C .val`, `STerm C` is
`Tm C .st`, and every symbol has its old constructor name as a pattern
(`Term.find s p` is `.app2 .find s p`), so `.find s p` builds and matches a
term as before. -/

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
  /-- `delValue(t)`: the default of the word `t`, KeY's `delValue<[α]>`, what
  a delete leaves at a word (`Theory.delValue`). -/
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
  /-- `find(s, p)`, and at a state variable KeY's `select(s, r)`. -/
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
  /-- `save(s, p, v)`; at a state variable, KeY's `store(s, r, v)`. -/
  | save : Op3 .st .path .sv .st
  /-- `save(save(s, p[p.length], v), p.length, p.length + 1)`. -/
  | push : Op3 .st .path .sv .st
  /-- `p[i]@S`: `p[i]` with its index checked in the storage `S` instead of
  the state's — `p[i]` merged under a storage write (`Tm.substSt`). -/
  | atIn : Op3 .st .path .val .path
  /-- `write(m, a, v)`. -/
  | write : Op3 .mem .addr .mv .mem
  deriving DecidableEq, Repr

/-- A term of sort `s`: a variable, or a symbol applied to terms. -/
inductive Tm (C : Contract) : Srt → Type where
  /-- A stack local. -/
  | pvV (x : Var) : Tm C .val
  /-- A storage alias. -/
  | pvP (x : Var) : Tm C .path
  /-- A storage variable: KeY's `old`, of sort `Struct`, bound by the update
  `old := storage` in front of a specification's modality. -/
  | pvS (x : Var) : Tm C .st
  /-- A memory local. -/
  | pvI (x : Var) : Tm C .ident
  | app0 {s : Srt} (o : Op0 s) : Tm C s
  | app1 {a s : Srt} (o : Op1 a s) (x : Tm C a) : Tm C s
  | app2 {a b s : Srt} (o : Op2 a b s) (x : Tm C a) (y : Tm C b) : Tm C s
  | app3 {a b c s : Srt} (o : Op3 a b c s) (x : Tm C a) (y : Tm C b) (z : Tm C c) : Tm C s
  deriving DecidableEq, Repr

/-- A value term. -/
abbrev Term (C : Contract) := Tm C .val
/-- A storage path. -/
abbrev PTerm (C : Contract) := Tm C .path
/-- A storage. -/
abbrev STerm (C : Contract) := Tm C .st
/-- What a storage `save` writes: a value, a subtree read out of a storage,
or a memory object copied back (`copyMem(mtSt, m, i)`). -/
abbrev SValT (C : Contract) := Tm C .sv
/-- A memory identity. -/
abbrev ITerm (C : Contract) := Tm C .ident
/-- A member or an element of a memory object. -/
abbrev MAddr (C : Contract) := Tm C .addr
/-- A memory. -/
abbrev MTerm (C : Contract) := Tm C .mem
/-- What a memory `write` writes: a value or a reference. -/
abbrev MValT (C : Contract) := Tm C .mv

section Ctors

variable {C : Contract}

@[match_pattern, reducible] def Term.lit (v : Value) : Term C := .app0 (.lit v)
@[match_pattern, reducible] def Term.pv (x : Var) : Term C := .pvV x
@[match_pattern, reducible] def Term.binop (op : BinOp) (p : PrimTy) (a b : Term C) : Term C :=
  .app2 (.binop op p) a b
@[match_pattern, reducible] def Term.unop (op : UnOp) (p : PrimTy) (a : Term C) : Term C :=
  .app1 (.unop op p) a
@[match_pattern, reducible] def Term.find (s : STerm C) (p : PTerm C) : Term C := .app2 .find s p
@[match_pattern, reducible] def Term.len (s : STerm C) (p : PTerm C) : Term C := .app2 .len s p
@[match_pattern, reducible] def Term.read (m : MTerm C) (a : MAddr C) : Term C := .app2 .read m a
@[match_pattern, reducible] def Term.ite (c a b : Term C) : Term C := .app3 .ite c a b
@[match_pattern, reducible] def Term.mlen (m : MTerm C) (i : ITerm C) : Term C := .app2 .mlen m i
@[match_pattern, reducible] def Term.env (k : EnvKey) : Term C := .app0 (.env k)
@[match_pattern, reducible] def Term.net (a : Term C) : Term C := .app1 .net a
@[match_pattern, reducible] def Term.netOf (x : Var) (a : Term C) : Term C := .app1 (.netOf x) a
@[match_pattern, reducible] def Term.delValue (t : Term C) : Term C := .app1 .delValue t
@[match_pattern, reducible] def Term.wt (vs : List (Name × Ty)) (s : STerm C) : Term C :=
  .app1 (.wt vs) s

@[match_pattern, reducible] def PTerm.root (r : Name) : PTerm C := .app0 (.root r)
@[match_pattern, reducible] def PTerm.pv (x : Var) : PTerm C := .pvP x
@[match_pattern, reducible] def PTerm.field (p : PTerm C) (f : Name) : PTerm C := .app1 (.field f) p
@[match_pattern, reducible] def PTerm.at (p : PTerm C) (i : Term C) : PTerm C := .app2 .at p i
@[match_pattern, reducible] def PTerm.next (p : PTerm C) : PTerm C := .app1 .next p
@[match_pattern, reducible] def PTerm.nextIn (s : STerm C) (p : PTerm C) : PTerm C := .app2 .nextIn s p
@[match_pattern, reducible] def PTerm.atIn (s : STerm C) (p : PTerm C) (i : Term C) : PTerm C :=
  .app3 .atIn s p i

@[match_pattern, reducible] def STerm.storage : STerm C := .app0 .storage
@[match_pattern, reducible] def STerm.pv (x : Var) : STerm C := .pvS x
@[match_pattern, reducible] def STerm.save (s : STerm C) (p : PTerm C) (v : SValT C) : STerm C :=
  .app3 .save s p v
@[match_pattern, reducible] def STerm.delAt (s : STerm C) (p : PTerm C) : STerm C := .app2 .delAt s p
@[match_pattern, reducible] def STerm.push (s : STerm C) (p : PTerm C) (v : SValT C) : STerm C :=
  .app3 .push s p v
@[match_pattern, reducible] def STerm.pushSlot (s : STerm C) (p : PTerm C) (E : Ty) : STerm C :=
  .app2 (.pushSlot E) s p
@[match_pattern, reducible] def STerm.pop (s : STerm C) (p : PTerm C) : STerm C := .app2 .pop s p
@[match_pattern, reducible] def STerm.shrink (s : STerm C) (p : PTerm C) : STerm C := .app2 .shrink s p
@[match_pattern, reducible] def STerm.extend (s : STerm C) (p : PTerm C) (E : Ty) : STerm C :=
  .app2 (.extend E) s p
@[match_pattern, reducible] def STerm.select (s : STerm C) (r : Name) : STerm C := .app1 (.select r) s

@[match_pattern, reducible] def SValT.val (t : Term C) : SValT C := .app1 .sval t
@[match_pattern, reducible] def SValT.find (s : STerm C) (p : PTerm C) : SValT C := .app2 .sfind s p
@[match_pattern, reducible] def SValT.copyMem (m : MTerm C) (i : ITerm C) : SValT C := .app2 .copyMem m i
@[match_pattern, reducible] def SValT.newArr (R : RefTy) (n : Term C) : SValT C := .app1 (.newArr R) n

@[match_pattern, reducible] def ITerm.pv (x : Var) : ITerm C := .pvI x
@[match_pattern, reducible] def ITerm.read (m : MTerm C) (a : MAddr C) : ITerm C := .app2 .iread m a
@[match_pattern, reducible] def ITerm.alloc (m : MTerm C) (R : RefTy) : ITerm C := .app1 (.alloc R) m
@[match_pattern, reducible] def ITerm.copy (m : MTerm C) (v : SValT C) : ITerm C := .app2 .copy m v

@[match_pattern, reducible] def MAddr.field (i : ITerm C) (f : Name) : MAddr C := .app1 (.mfield f) i
@[match_pattern, reducible] def MAddr.at (i : ITerm C) (k : Term C) : MAddr C := .app2 .mat i k

@[match_pattern, reducible] def MTerm.memory : MTerm C := .app0 .memory
@[match_pattern, reducible] def MTerm.write (m : MTerm C) (a : MAddr C) (v : MValT C) : MTerm C :=
  .app3 .write m a v
@[match_pattern, reducible] def MTerm.addM (m : MTerm C) (R : RefTy) : MTerm C := .app1 (.addM R) m
@[match_pattern, reducible] def MTerm.copySt (m : MTerm C) (v : SValT C) : MTerm C := .app2 .copySt m v

@[match_pattern, reducible] def MValT.val (t : Term C) : MValT C := .app1 .mval t
@[match_pattern, reducible] def MValT.ref (i : ITerm C) : MValT C := .app1 .ref i

end Ctors

/-- The value `t++` has: the bumped value for `++t`, the old one for `t++`. -/
def Term.bumped {C : Contract} (op : IncDec) (p : PrimTy) (t : Term C) : Term C :=
  if op.isPre then .binop op.binOp p t (.lit (.int 1)) else t

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
      | none => .error .stuck
    | .array _ _ => .error .stuck
  | .memoryIndex id i => do
    match ← σ.getObj id with
    | .array elems _ =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then pure (elems.get ⟨i.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .stuck

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

/-- A unary symbol read in `σ`, its argument's reading given. -/
def Op1.eval (σ : State) : Op1 a s → a.Ev → s.Ev
  | .unop op p, ra => do unopCheck op p (← applyUnOp op (← ra))
  | .net, ra => do pure (.int (σ.getNet (← (← ra).asInt)))
  | .netOf x, ra => do
    match ← σ.getEnv x with
    | .ledger l => pure (.int ((lookupBy (← (← ra).asInt) l).getD 0))
    | .val _ | .spath .. | .mref _ | .store _ => .error .stuck
  | .delValue, ra => do pure (Theory.StValue.primDefault (← ra))
  | .field f, rp => do
    let (r, segs) ← rp
    pure (r, segs ++ [.field f])
  | .next, rp => do
    let (r, segs) ← rp
    match ← σ.findStorage r segs with
    | .array elems _ _ => pure (r, segs ++ [.at elems.length])
    | .prim _ | .struct _ | .map _ _ => .error .stuck
  | .select r, rs => do
    let τ ← rs
    match ← τ.findStorage r [] with
    | .struct fields => pure { τ with storage := fields }
    | .prim _ | .array .. | .map .. => .error .stuck
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
    if storageWtB vs τ.storage then pure (.bool true) else .error .stuck

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
    | .prim _ | .struct _ | .map _ _ => .error .stuck
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

/-- A term read in `σ` by the interpreter: a storage or memory term reads to
the state with that storage or memory. -/
def Tm.eval (σ : State) : Tm C s → s.Ev
  | .pvV x => do
    match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. | .mref _ | .store _ | .ledger _ => .error .stuck
  | .pvP x => aliasPath σ x
  | .pvS x => do
    match ← σ.getEnv x with
    | .store st => pure { σ with storage := st }
    | .val _ | .spath .. | .mref _ | .ledger _ => .error .stuck
  | .pvI x => do
    match ← σ.getEnv x with
    | .mref id => pure id
    | .val _ | .spath .. | .store _ | .ledger _ => .error .stuck
  | .app0 o => o.eval σ
  | .app1 o a => o.eval σ (a.eval σ)
  | .app2 o a b => o.eval σ (a.eval σ) (b.eval σ)
  | .app3 o a b c => o.eval σ (a.eval σ) (b.eval σ) (c.eval σ)

attribute [tm_eval] Tm.eval Op0.eval Op1.eval Op2.eval Op3.eval

/-! ## What a term denotes in the Theory

`Tm.denote` reads a formula's terms in the Theory algebra over the storage
node `State.abs σ`, total, as KeY reads them: a read off the end of what is
there is a node, not a halt.  `Tm.eval` is the interpreter's reading; the
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
  `Tm.eval` does; `PTerm.nextIn` reads it in its storage term, and
  `PTerm.atIn` is `PTerm.at` (the check is `eval`'s alone).
-/

section Denote

open Theory Theory.StValue

/-- A Theory value as an interpreter result: a primitive, or a halt. -/
def Theory.StValue.toRes : StValue → Res Value
  | .prim p => .ok p
  | .st _ => .error .stuck

/-- An interpreter result as a Theory value: a halt reads as nothing. -/
def Res.toSt : Res Value → StValue
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

/-- A term in the Theory, over `State.abs σ`. -/
def Tm.denote (σ : State) : Tm C s → s.Den
  | .pvV x => match σ.getEnv x with
    | .ok (.val v) => .prim v
    | _ => .st .mtSt
  | .pvP x => match aliasPath σ x with
    | .ok (r, segs) => rootPath r segs
    | .error _ => []
  | .pvS x => match σ.getEnv x with
    | .ok (.store roots) => SVal.abs.fields roots
    | _ => .mtSt
  | .pvI _ => ()
  | .app0 o => o.denote σ
  | .app1 o a => o.denote σ (a.denote σ)
  | .app2 o a b => o.denote σ (a.eval σ) (b.eval σ) (a.denote σ) (b.denote σ)
  | .app3 o a b c => o.denote (a.denote σ) (b.denote σ) (c.denote σ)

attribute [tm_denote] Tm.denote Op0.denote Op1.denote Op2.denote Op3.denote


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

/-- One elementary update. -/
inductive UpdElem (C : Contract) where
  /-- `v := t` -/
  | val (x : Var) (t : Term C)
  /-- `lsv := p`: an alias binds a path. -/
  | path (x : Var) (p : PTerm C)
  /-- `mv := i`: a memory local binds an identity. -/
  | mref (x : Var) (i : ITerm C)
  /-- `storage := s` -/
  | storage (s : STerm C)
  /-- `old := s`: a storage variable binds a storage. -/
  | store (x : Var) (s : STerm C)
  /-- `memory := m` -/
  | memory (m : MTerm C)
  /-- `selfBalance := selfBalance ± a`: the contract's funds, in KeY's `int`. -/
  | selfBalance (op : IntOp) (a : Term C)
  /-- `net := store(net, at(r), net(r) ± a)`: the ledger's entry for `r`
  moved by `a`, in KeY's `int`.  The address and the amount are read in the
  pre-state, as every right-hand side is; the move is made on the ledger the
  update has written so far, so two in one update add up. -/
  | net (r : Term C) (op : IntOp) (a : Term C)
  /-- `net := if(r = this) then net else store(net, at(r), net(r) - a)`: a
  payment of `a` to `r`, solkey's
  `\if(sadr = self) \then(net) \else(storeSt(net, at(sadr), selectSt(net, at(sadr)) - se))`.
  The amount is read as a word, so the update halts where it is negative, as
  the transfer does; a payment to the contract itself books nothing. -/
  | pay (r a : Term C)
  /-- `oldNet := net`: a ledger variable binds the ledger, which
  `\old(net(a))` reads. -/
  | saveNet (x : Var)

/-- A parallel update `{a ‖ b ‖ …}`. -/
abbrev Upd (C : Contract) := List (UpdElem C)

/-- One elementary update: the right-hand side is read in the *pre*-state
`σ₀`, the write goes into `τ`.  That is what makes a list of them parallel. -/
def UpdElem.write (σ₀ : State) : UpdElem C → State → Res State
  | .val x t, τ => do pure (τ.setEnv x (.val (← t.eval σ₀)))
  | .path x p, τ => do
    let (r, segs) ← p.eval σ₀
    pure (τ.setEnv x (.spath r segs))
  | .mref x i, τ => do pure (τ.setEnv x (.mref (← i.eval σ₀)))
  | .storage s, τ => do pure { τ with storage := (← s.eval σ₀).storage }
  | .store x s, τ => do pure (τ.setEnv x (.store (← s.eval σ₀).storage))
  | .memory m, τ => do
    let μ ← m.eval σ₀
    pure { τ with heap := μ.heap, nextId := μ.nextId }
  | .selfBalance op a, τ => do
    let amt ← (← a.eval σ₀).asInt
    pure { τ with selfBalance := op.apply σ₀.selfBalance amt }
  | .net r op a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    pure { τ with net := setBy addr (op.apply (τ.getNet addr) amt) τ.net }
  | .pay r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    if amt < 0 then .error .stuck
    else pure { τ with
      net := if addr = σ₀.tx.selfAddress then τ.net else setBy addr (τ.getNet addr - amt) τ.net }
  | .saveNet x, τ => pure (τ.setEnv x (.ledger σ₀.net))

/-- The state an update leaves, from `σ`. -/
def Upd.apply (U : Upd C) (σ : State) : Res State :=
  U.foldlM (fun τ e => e.write σ τ) σ

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

/-! ## Formulas -/

/-- A formula about programs of the contract `C`. -/
inductive Fml (C : Contract) where
  | tt
  /-- `a = b`, read in the Theory (`Tm.denote`): total, so it may hold
  of terms that halt. -/
  | eq (a b : Term C)
  /-- `t` returns: the interpreter's `eval` does not halt on it. -/
  | defined (t : Term C)
  | not (φ : Fml C)
  | and (φ ψ : Fml C)
  | imp (φ ψ : Fml C)
  /-- `{U} φ`, produced under the modality `m`. -/
  | upd (m : Modality) (U : Upd C) (φ : Fml C)
  /-- `⟨ P ⟩ φ` or `[ P ] φ`. -/
  | modal (m : Modality) (P : Prog C) (φ : Fml C)
  /-- `{havoc} φ`: `φ` after any storage and ledger a callee may
  leave — KeY's anonymising update with fresh skolem symbols. -/
  | havoc (φ : Fml C)
  /-- `∀ p x. φ`: `φ` for every value of the type `p` the local `x` may
  hold (a `uint` in `[0, 2^256)`), KeY's `\forall`. -/
  | all (x : Var) (p : PrimTy) (φ : Fml C)

instance : Inhabited (Fml C) := ⟨.tt⟩

/-- `false` is `¬true`. -/
abbrev Fml.ff : Fml C := .not .tt

/-- `a = b` with both sides defined: the equation of the interpreter, which
`holds_eqD_iff` (`Theory/Bridge/Denote.lean`) states. -/
abbrev Fml.eqD (a b : Term C) : Fml C := .and (.defined a) (.and (.defined b) (.eq a b))

/-- The values of the primitive type `p`, which a quantifier ranges over. -/
def PrimTy.admits : PrimTy → Value → Prop
  | .bool, .bool _ => True
  | .uint, .int n => 0 ≤ n ∧ n < uintBound
  | .int, .int n => -intBound ≤ n ∧ n < intBound
  | _, _ => False

/-- Whether `φ` holds in `σ`.  An equation compares the Theory values of its
sides, up to `StValue.Equiv`; `defined` says a term returns. -/
def holds (σ : State) : Fml C → Prop
  | .tt => True
  | .eq a b => Theory.StValue.Equiv (a.denote σ) (b.denote σ)
  | .defined t => ∃ x, t.eval σ = .ok x
  | .not φ => ¬ holds σ φ
  | .and φ ψ => holds σ φ ∧ holds σ ψ
  | .imp φ ψ => holds σ φ → holds σ ψ
  | .upd m U φ => m.after (holds · φ) (U.apply σ)
  | .modal m P φ => m.afterRun (holds · φ) (Prog.run σ P)
  | .havoc φ => ∀ st nt, holds (σ.havoc st nt) φ
  | .all x p φ => ∀ v, p.admits v → holds (σ.setEnv x (.val v)) φ

/-- Valid: true in every state. -/
def Valid (φ : Fml C) : Prop := ∀ σ, holds σ φ

/-! ## Goals over bound locals

A `try` has a goal per way its call may end, each for every value of the
locals the outcome binds (`Premise.branches`): `∀ xs. φ`, with `xs` bound
as the run decodes them (`bindData`). -/

/-- `∀ p₁ x₁. … ∀ pₙ xₙ. φ`. -/
def Fml.alls : List (PrimTy × Var) → Fml C → Fml C
  | [], φ => φ
  | (p, x) :: xs, φ => .all x p (Fml.alls xs φ)

/-- `φ₁ ∧ … ∧ φₙ`, `true` when there are none. -/
def Fml.conj : List (Fml C) → Fml C
  | [] => .tt
  | [φ] => φ
  | φ :: ψs => .and φ (Fml.conj ψs)

/-- A value of the type is one decoding accepts. -/
theorem PrimTy.admits_iff_fits (p : PrimTy) (v : Value) : p.admits v ↔ v.fits p = true := by
  cases p <;> cases v <;> simp [PrimTy.admits, PrimVal.fits]

/-- `σ'` is `σ` with the locals `xs` bound to values of their types, as an
outcome's data binds them. -/
def Binds (xs : List (PrimTy × Var)) (σ σ' : State) : Prop := ∃ vs, bindData xs vs σ = .ok σ'

theorem holds_conj {σ : State} : {φs : List (Fml C)} → (holds σ (Fml.conj φs) ↔ ∀ φ ∈ φs, holds σ φ)
  | [] => by simp [Fml.conj, holds]
  | [φ] => by simp [Fml.conj]
  | φ :: ψ :: φs => by simp [Fml.conj, holds, holds_conj (φs := ψ :: φs)]

theorem holds_alls {φ : Fml C} : {xs : List (PrimTy × Var)} → {σ : State} →
    (holds σ (Fml.alls xs φ) ↔ ∀ σ', Binds xs σ σ' → holds σ' φ)
  | [], σ => by
    simp only [Fml.alls, Binds, bindData]
    exact ⟨fun h σ' ⟨_, he⟩ => by cases he; exact h, fun h => h σ ⟨[], rfl⟩⟩
  | (p, x) :: xs, σ => by
    simp only [Fml.alls, holds, holds_alls (xs := xs), Binds, PrimTy.admits_iff_fits]
    constructor
    · rintro h σ' ⟨_ | ⟨v, vs⟩, he⟩
      · simp [bindData] at he
      · simp only [bindData] at he
        split at he
        · exact h v (by assumption) σ' ⟨vs, he⟩
        · cases he
    · intro h v hv σ' ⟨vs, he⟩
      exact h σ' ⟨v :: vs, by simp only [bindData, hv, if_true]; exact he⟩

/-- No modality anywhere, under a negation and on the left of an implication
included: a formula of the logic, which the calculus leaves to `Valid`. -/
def Fml.modalFree : Fml C → Bool
  | .tt | .eq .. | .defined _ => true
  | .not φ | .upd _ _ φ | .havoc φ | .all _ _ φ => φ.modalFree
  | .and φ ψ | .imp φ ψ => φ.modalFree && ψ.modalFree
  | .modal .. => false


/-! ## Frames

What a formula does not mention, it does not see: two states that agree off
`ns` satisfy a formula that avoids `ns` alike.  This is what lets a rule
declare a fresh `se1` in front of the rest of the program and the
postcondition. -/

/-- The variables a term reads. -/
def Tm.vars : Tm C s → List Var
  | .pvV x | .pvP x | .pvS x | .pvI x => [x]
  | .app0 _ => []
  | .app1 (.netOf x) a => x :: a.vars
  | .app1 _ a => a.vars
  | .app2 _ a b => a.vars ++ b.vars
  | .app3 _ a b c => a.vars ++ b.vars ++ c.vars

def UpdElem.vars : UpdElem C → List Var
  | .val x t => x :: t.vars
  | .path x p => x :: p.vars
  | .mref x i => x :: i.vars
  | .storage s => s.vars
  | .store x s => x :: s.vars
  | .memory m => m.vars
  | .selfBalance _ a => a.vars
  | .net r _ a => r.vars ++ a.vars
  | .pay r a => r.vars ++ a.vars
  | .saveNet x => [x]

def Upd.vars : Upd C → List Var
  | [] => []
  | e :: U => e.vars ++ Upd.vars U

/-- The variables a formula mentions, its programs' included, and a
quantifier's own. -/
def Fml.vars : Fml C → List Var
  | .tt => []
  | .eq a b => a.vars ++ b.vars
  | .defined t => t.vars
  | .not φ => φ.vars
  | .and φ ψ | .imp φ ψ => φ.vars ++ ψ.vars
  | .upd _ U φ => Upd.vars U ++ φ.vars
  | .modal _ P φ => Prog.vars P ++ φ.vars
  | .havoc φ => φ.vars
  | .all x _ φ => x :: φ.vars

section Frame

variable {ns : List Var}

theorem readAddr_congr {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (a : Addr) :
    readAddr σ a = readAddr τ a := by
  cases a <;> simp only [readAddr, getObj_congr hag]

theorem arrayLen_congr {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (r : Name) (segs : List Seg) :
    arrayLen σ r segs = arrayLen τ r segs := by
  simp only [arrayLen, findStorage_congr hag]

/-- Peel a shared prefix, or bind two agreeing states. -/
theorem ResultsAgree.bindEq {α : Type} {x₁ x₂ : Res State} (hx : ResultsAgree ns x₁ x₂)
    {f₁ f₂ : State → Res α} (hf : ∀ s₁ s₂, EnvAgreeExcept ns s₁ s₂ → f₁ s₁ = f₂ s₂) :
    (x₁ >>= f₁) = (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error _, .error _, hx => subst hx; rfl
  | .ok s₁, .ok s₂, hs => exact hf s₁ s₂ hs

/-! ### Reading a term off its variables

A symbol reads its arguments and, at most, the state's environment, ledger
and storage.  So two states that agree off `ns` read a symbol alike once its
arguments read alike (`OpN.eval_agree`), and a term that avoids `ns` reads
alike (`Tm.eval_frame`): a value equal, a storage or memory to states that
agree off `ns` (`Srt.Agree`).  Substitution (`Calculus/UpdateRules.lean`)
reuses the per-symbol lemmas, with the variables read after the update. -/

/-- Two readings of a sort agree off `ns`: equal, and for a storage or a
memory, states that agree off `ns`. -/
def Srt.Agree (ns : List Var) : (s : Srt) → s.Ev → s.Ev → Prop
  | .val => Eq
  | .path => Eq
  | .st => ResultsAgree ns
  | .sv => Eq
  | .ident => Eq
  | .addr => Eq
  | .mem => ResultsAgree ns
  | .mv => Eq

/-- The variable a symbol carries: `netOf`'s ledger. -/
def Op1.vars : Op1 a s → List Var
  | .netOf x => [x]
  | _ => []

theorem Tm.vars_app1 (o : Op1 a s) (t : Tm C a) : (Tm.app1 o t).vars = o.vars ++ t.vars := by
  cases o <;> rfl

theorem Op0.eval_agree {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (o : Op0 s) → Srt.Agree ns s (o.eval σ) (o.eval τ)
  | .lit _ | .root _ => rfl
  | .env _ => by simp only [Srt.Agree, Op0.eval, State.envVal_congr hag]
  | .storage | .memory => hag

theorem Op1.eval_agree {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (o : Op1 a s) → Avoids o.vars ns → {x₁ x₂ : a.Ev} → Srt.Agree ns a x₁ x₂ →
      Srt.Agree ns s (o.eval σ x₁) (o.eval τ x₂)
  | .unop .., _, _, _, hx | .delValue, _, _, _, hx | .field _, _, _, _, hx | .sval, _, _, _, hx
  | .newArr _, _, _, _, hx | .mfield _, _, _, _, hx | .mval, _, _, _, hx | .ref, _, _, _, hx => by
    simp only [Srt.Agree] at hx ⊢; subst hx; rfl
  | .net, _, _, _, hx => by
    simp only [Srt.Agree] at hx ⊢; subst hx
    simp only [Op1.eval, State.getNet, hag.net]
  | .netOf _, ho, _, _, hx => by
    simp only [Srt.Agree] at hx ⊢; subst hx
    simp only [Op1.eval, getEnv_congr hag ho.head]
  | .next, _, _, _, hx => by
    simp only [Srt.Agree] at hx ⊢; subst hx
    simp only [Op1.eval, findStorage_congr hag]
  | .select r, _, _, _, hx => by
    simp only [Srt.Agree, Op1.eval] at hx ⊢
    refine ResultsAgree.bind hx fun _ τ' h' => ?_
    simp only [findStorage_congr h']
    rcases τ'.findStorage r [] with _ | w
    · exact ResultsAgree.refl _ _
    · cases w
      all_goals first
        | exact ResultsAgree.refl _ _
        | exact ⟨rfl, h'.heap, h'.nextId, h'.net, h'.env, h'.selfBalance, h'.tx⟩
  | .alloc R, _, _, _, hx => by
    simp only [Srt.Agree, Op1.eval] at hx ⊢
    refine ResultsAgree.bindEq hx fun _ _ h' => ?_
    rcases (allocDefault_agree h' R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
      simp only [h₁, h₂] <;> rfl
  | .addM R, _, _, _, hx => by
    simp only [Srt.Agree, Op1.eval] at hx ⊢
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    exact ResAgree.bindState (allocDefault_agree h' R) fun _ _ _ h'' => h''
  | .wt _, _, _, _, hx => by
    simp only [Srt.Agree, Op1.eval] at hx ⊢
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [h'.storage]

theorem Op2.eval_agree {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (o : Op2 a b s) → {x₁ x₂ : a.Ev} → {y₁ y₂ : b.Ev} → Srt.Agree ns a x₁ x₂ →
      Srt.Agree ns b y₁ y₂ → Srt.Agree ns s (o.eval σ x₁ y₁) (o.eval τ x₂ y₂)
  | .binop .., _, _, _, _, hx, hy | .mat, _, _, _, _, hx, hy => by
    simp only [Srt.Agree] at hx hy ⊢; subst hx hy; rfl
  | .at, _, _, _, _, hx, hy => by
    simp only [Srt.Agree] at hx hy ⊢; subst hx hy
    simp only [Op2.eval, checkIndex_congr hag]
  | .nextIn, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [findStorage_congr h']
  | .find, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [findStorage_congr h']
  | .sfind, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [findStorage_congr h']
  | .len, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [arrayLen_congr h']
  | .read, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [readAddr_congr h']
  | .iread, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [readAddr_congr h']
  | .mlen, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [memArrayLen, getObj_congr h']
  | .copyMem, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [copyMem_congr h']
  | .delAt, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    simp only [findStorage_congr h']
    agree_run h'
  | .pushSlot _, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => pushAt_agree h' _ _ _ fun _ => rfl
  | .pop, _, _, _, _, hx, hy | .shrink, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    agree_run h'
  | .extend _, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    refine bindPureResults_agree _ fun _ => ?_
    exact ResAgree.bindState (pushPlaceAt_agree h' _ _ _) fun _ _ _ h'' => h''
  | .copy, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    refine congrArg (_ >>= ·) (funext fun sv => ?_)
    refine ResultsAgree.bindEq hx fun _ _ h' => ?_
    rcases (copyStToM_agree h' sv).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
      simp only [h₁, h₂] <;> rfl
  | .copySt, _, _, _, _, hx, hy => by
    simp only [Srt.Agree, Op2.eval] at hx hy ⊢; subst hy
    refine bindPureResults_agree _ fun sv => ?_
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    exact ResAgree.bindState (copyStToM_agree h' sv) fun _ _ _ h'' => h''

theorem Op3.eval_agree {σ τ : State} :
    (o : Op3 a b c s) → {x₁ x₂ : a.Ev} → {y₁ y₂ : b.Ev} → {z₁ z₂ : c.Ev} →
      Srt.Agree ns a x₁ x₂ → Srt.Agree ns b y₁ y₂ → Srt.Agree ns c z₁ z₂ →
      Srt.Agree ns s (o.eval σ x₁ y₁ z₁) (o.eval τ x₂ y₂ z₂)
  | .ite, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.Agree] at hx hy hz ⊢; subst hx hy hz; rfl
  | .atIn, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.Agree, Op3.eval] at hx hy hz ⊢; subst hy hz
    exact ResultsAgree.bindEq hx fun _ _ h' => by simp only [checkIndex_congr h']
  | .save, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.Agree, Op3.eval] at hx hy hz ⊢; subst hy hz
    refine bindPureResults_agree _ fun _ => ?_
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    agree_run h'
  | .push, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.Agree, Op3.eval] at hx hy hz ⊢; subst hy hz
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => pushAt_agree h' _ _ _ fun _ => rfl
  | .write, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.Agree, Op3.eval] at hx hy hz ⊢; subst hy hz
    refine bindPureResults_agree _ fun _ => ?_
    refine ResultsAgree.bind hx fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => writeAddr_agree h' _ _

/-- A term that avoids `ns` reads alike in two states that agree off `ns`. -/
theorem Tm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (t : Tm C s) → Avoids t.vars ns → Srt.Agree ns s (t.eval σ) (t.eval τ)
  | .pvV x, h | .pvI x, h => by simp only [Srt.Agree, Tm.eval, getEnv_congr hag h.head]
  | .pvP x, h => aliasPath_frame hag h.head
  | .pvS x, h => by
    simp only [Srt.Agree, Tm.eval, getEnv_congr hag h.head]
    rcases τ.getEnv x with _ | b
    · exact ResultsAgree.refl _ _
    · cases b
      all_goals first
        | exact ResultsAgree.refl _ _
        | exact ⟨rfl, hag.heap, hag.nextId, hag.net, hag.env, hag.selfBalance, hag.tx⟩
  | .app0 o, _ => o.eval_agree hag
  | .app1 o a, h => by
    rw [Tm.vars_app1] at h
    exact o.eval_agree hag h.left (a.eval_frame hag h.right)
  | .app2 o a b, h => o.eval_agree hag (a.eval_frame hag h.left) (b.eval_frame hag h.right)
  | .app3 o a b c, h =>
    o.eval_agree (a.eval_frame hag h.left.left) (b.eval_frame hag h.left.right)
      (c.eval_frame hag h.right)

theorem Term.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (t : Term C)
    (h : Avoids t.vars ns) : t.eval σ = t.eval τ := Tm.eval_frame hag t h
theorem PTerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (p : PTerm C)
    (h : Avoids p.vars ns) : p.eval σ = p.eval τ := Tm.eval_frame hag p h
theorem STerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (s : STerm C)
    (h : Avoids s.vars ns) : ResultsAgree ns (s.eval σ) (s.eval τ) := Tm.eval_frame hag s h
theorem SValT.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (v : SValT C)
    (h : Avoids v.vars ns) : v.eval σ = v.eval τ := Tm.eval_frame hag v h
theorem ITerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (i : ITerm C)
    (h : Avoids i.vars ns) : i.eval σ = i.eval τ := Tm.eval_frame hag i h
theorem MAddr.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (a : MAddr C)
    (h : Avoids a.vars ns) : a.eval σ = a.eval τ := Tm.eval_frame hag a h
theorem MTerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (m : MTerm C)
    (h : Avoids m.vars ns) : ResultsAgree ns (m.eval σ) (m.eval τ) := Tm.eval_frame hag m h
theorem MValT.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (v : MValT C)
    (h : Avoids v.vars ns) : v.eval σ = v.eval τ := Tm.eval_frame hag v h

theorem Op0.denote_agree {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (o : Op0 s) → o.denote σ = o.denote τ
  | .lit _ | .root _ | .memory => rfl
  | .env _ => by simp only [Op0.denote, State.envVal_congr hag]
  | .storage => by simp only [Op0.denote, State.abs, hag.storage]

theorem Op1.denote_agree {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (o : Op1 a s) → Avoids o.vars ns → (d : a.Den) → o.denote σ d = o.denote τ d
  | .net, _, _ => by simp only [Op1.denote, State.getNet, hag.net]
  | .netOf _, ho, _ => by simp only [Op1.denote, getEnv_congr hag ho.head]
  | .next, _, _ => by simp only [Op1.denote, State.abs, hag.storage]
  | .unop .., _, _ | .delValue, _, _ | .field _, _, _ | .select _, _, _ | .sval, _, _
  | .newArr _, _, _ | .alloc _, _, _ | .mfield _, _, _ | .addM _, _, _ | .mval, _, _
  | .ref, _, _ | .wt _, _, _ => rfl

theorem Op2.denote_agree {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (o : Op2 a b s) → {x₁ x₂ : a.Ev} → {y₁ y₂ : b.Ev} → Srt.Agree ns a x₁ x₂ →
      Srt.Agree ns b y₁ y₂ → (d : a.Den) → (e : b.Den) →
      o.denote σ x₁ y₁ d e = o.denote τ x₂ y₂ d e
  | .read, _, _, _, _, hx, hy, _, _ => by
    simp only [Op2.denote]; rw [show Op2.eval σ .read _ _ = _ from Op2.eval_agree hag .read hx hy]
  | .mlen, _, _, _, _, hx, hy, _, _ => by
    simp only [Op2.denote]; rw [show Op2.eval σ .mlen _ _ = _ from Op2.eval_agree hag .mlen hx hy]
  | .copyMem, _, _, _, _, hx, hy, _, _ => by
    simp only [Op2.denote]
    rw [show Op2.eval σ .copyMem _ _ = _ from Op2.eval_agree hag .copyMem hx hy]
  | .binop .., _, _, _, _, _, _, _, _ | .find, _, _, _, _, _, _, _, _
  | .len, _, _, _, _, _, _, _, _ | .at, _, _, _, _, _, _, _, _ | .nextIn, _, _, _, _, _, _, _, _
  | .delAt, _, _, _, _, _, _, _, _
  | .pushSlot _, _, _, _, _, _, _, _, _ | .pop, _, _, _, _, _, _, _, _
  | .shrink, _, _, _, _, _, _, _, _ | .extend _, _, _, _, _, _, _, _, _
  | .sfind, _, _, _, _, _, _, _, _ | .iread, _, _, _, _, _, _, _, _
  | .copy, _, _, _, _, _, _, _, _ | .mat, _, _, _, _, _, _, _, _
  | .copySt, _, _, _, _, _, _, _, _ => rfl

/-- A term that avoids `ns` denotes alike in two states that agree off `ns`. -/
theorem Tm.denote_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (t : Tm C s) → Avoids t.vars ns → t.denote σ = t.denote τ
  | .pvV x, h | .pvS x, h => by simp only [Tm.denote, getEnv_congr hag h.head]
  | .pvP x, h => by simp only [Tm.denote, aliasPath_frame hag h.head]
  | .pvI _, _ => rfl
  | .app0 o, _ => o.denote_agree hag
  | .app1 o a, h => by
    rw [Tm.vars_app1] at h
    simp only [Tm.denote, a.denote_frame hag h.right]
    exact o.denote_agree hag h.left _
  | .app2 o a b, h => by
    simp only [Tm.denote, a.denote_frame hag h.left, b.denote_frame hag h.right]
    exact o.denote_agree hag (a.eval_frame hag h.left) (b.eval_frame hag h.right) _ _
  | .app3 o a b c, h => by
    simp only [Tm.denote, a.denote_frame hag h.left.left, b.denote_frame hag h.left.right,
      c.denote_frame hag h.right]

theorem UpdElem.write_frame {σ₀ σ₀' τ τ' : State} (h₀ : EnvAgreeExcept ns σ₀ σ₀')
    (h : EnvAgreeExcept ns τ τ') : (e : UpdElem C) → Avoids e.vars ns →
      ResultsAgree ns (e.write σ₀ τ) (e.write σ₀' τ')
  | .val x t, hv => by
    simp only [UpdElem.write, t.eval_frame h₀ hv.tail]
    agree_run h
  | .path x p, hv => by
    simp only [UpdElem.write, p.eval_frame h₀ hv.tail]
    agree_run h
  | .mref x i, hv => by
    simp only [UpdElem.write, i.eval_frame h₀ hv.tail]
    agree_run h
  | .storage s, hv => by
    simp only [UpdElem.write]
    match s.eval σ₀, s.eval σ₀', s.eval_frame h₀ hv with
    | .error _, .error _, he => subst he; rfl
    | .ok a, .ok b, hs => exact ⟨hs.storage, h.heap, h.nextId, h.net, h.env, h.selfBalance, h.tx⟩
  | .store x s, hv => by
    simp only [UpdElem.write]
    match s.eval σ₀, s.eval σ₀', s.eval_frame h₀ hv.tail with
    | .error _, .error _, he => subst he; rfl
    | .ok a, .ok b, hs =>
      have hs : EnvAgreeExcept ns a b := hs
      show ResultsAgree ns (.ok (τ.setEnv x (.store a.storage))) (.ok (τ'.setEnv x (.store b.storage)))
      rw [hs.storage]
      exact h.setEnv_both x _
  | .memory m, hv => by
    simp only [UpdElem.write]
    match m.eval σ₀, m.eval σ₀', m.eval_frame h₀ hv with
    | .error _, .error _, he => subst he; rfl
    | .ok a, .ok b, hs => exact ⟨h.storage, hs.heap, hs.nextId, h.net, h.env, h.selfBalance, h.tx⟩
  | .selfBalance _ a, hv => by
    simp only [UpdElem.write, a.eval_frame h₀ hv, h₀.selfBalance]
    agree_run h
    exact ⟨h.storage, h.heap, h.nextId, h.net, h.env, rfl, h.tx⟩
  | .net r _ a, hv => by
    simp only [UpdElem.write, r.eval_frame h₀ hv.left, a.eval_frame h₀ hv.right, State.getNet]
    agree_run h
    exact ⟨h.storage, h.heap, h.nextId, by rw [h.net], h.env, h.selfBalance, h.tx⟩
  | .pay r a, hv => by
    simp only [UpdElem.write, r.eval_frame h₀ hv.left, a.eval_frame h₀ hv.right, h₀.tx]
    agree_run h
    exact ⟨h.storage, h.heap, h.nextId, by simp only [State.getNet, h.net], h.env, h.selfBalance, h.tx⟩
  | .saveNet x, _ => by
    show ResultsAgree ns (.ok (τ.setEnv x (.ledger σ₀.net))) (.ok (τ'.setEnv x (.ledger σ₀'.net)))
    rw [h₀.net]
    exact h.setEnv_both x _

theorem Upd.foldl_frame {σ₀ σ₀' : State} (h₀ : EnvAgreeExcept ns σ₀ σ₀') :
    (U : Upd C) → Avoids (Upd.vars U) ns → ∀ {τ τ' : State}, EnvAgreeExcept ns τ τ' →
      ResultsAgree ns (U.foldlM (fun τ e => e.write σ₀ τ) τ)
        (U.foldlM (fun τ e => e.write σ₀' τ) τ')
  | [], _, _, _, h => h
  | e :: U, hv, _, _, h => by
    simp only [List.foldlM_cons]
    exact ResultsAgree.bind (e.write_frame h₀ h hv.left) fun _ _ h' =>
      Upd.foldl_frame h₀ U hv.right h'

theorem Upd.apply_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (U : Upd C)
    (hv : Avoids (Upd.vars U) ns) : ResultsAgree ns (U.apply σ) (U.apply τ) :=
  Upd.foldl_frame hag U hv hag

theorem Modality.after_frame (m : Modality) {p q : State → Prop} {r r' : Res State}
    (hr : ResultsAgree ns r r') (hpq : ∀ a b, EnvAgreeExcept ns a b → (p a ↔ q b)) :
    m.after p r ↔ m.after q r' := by
  match r, r', hr with
  | .error _, .error _, _ => exact Iff.rfl
  | .ok a, .ok b, h => exact hpq a b h

theorem Modality.afterRun_frame (m : Modality) {p q : State → Prop} {r r' : Res State}
    (hr : ResultsAgree ns r r') (hpq : ∀ a b, EnvAgreeExcept ns a b → (p a ↔ q b)) :
    m.afterRun p r ↔ m.afterRun q r' := by
  match r, r', hr with
  | .error _, .error _, h => cases h; exact Iff.rfl
  | .ok a, .ok b, h =>
    simp only [Modality.afterRun, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
    exact hpq a b h

/-- **Frame, for formulas**: two states that agree off `ns` satisfy a formula
that avoids `ns` alike. -/
theorem holds_frame : (φ : Fml C) → Avoids φ.vars ns → ∀ {σ τ : State},
    EnvAgreeExcept ns σ τ → (holds σ φ ↔ holds τ φ)
  | .tt, _, _, _, _ => Iff.rfl
  | .eq a b, h, _, _, hag => by
    simp only [holds, a.denote_frame hag h.left, b.denote_frame hag h.right]
  | .defined t, h, _, _, hag => by simp only [holds, t.eval_frame hag h]
  | .not φ, h, _, _, hag => by simp only [holds, holds_frame φ h hag]
  | .and φ ψ, h, _, _, hag => by
    simp only [holds, holds_frame φ h.left hag, holds_frame ψ h.right hag]
  | .imp φ ψ, h, _, _, hag => by
    simp only [holds, holds_frame φ h.left hag, holds_frame ψ h.right hag]
  | .upd m U φ, h, _, _, hag => by
    simp only [holds]
    exact m.after_frame (Upd.apply_frame hag U h.left) fun _ _ h' => holds_frame φ h.right h'
  | .modal m P φ, h, _, _, hag => by
    simp only [holds]
    exact m.afterRun_frame (Prog.run_frame hag P h.left) fun _ _ h' => holds_frame φ h.right h'
  | .havoc φ, h, _, _, hag => by
    simp only [holds]
    exact forall_congr' fun st => forall_congr' fun nt =>
      holds_frame φ h (hag.havoc st nt)
  | .all x _ φ, h, _, _, hag => by
    simp only [holds]
    exact forall_congr' fun v => imp_congr_right fun _ =>
      holds_frame φ h.tail (hag.setEnv_both x (.val v))

end Frame

/-! ## Lowering program expressions to terms

A value position lowers with `lower`, a path position with `lowerPath`, once,
at the rule (Maude's `lower(LV, C)`).  Lowering keeps meaning:
`lower_eval` below. -/

def Simple.lower {p : PrimTy} : Simple C p → Term C
  | .lit n _ => .lit (.int n)
  | .bool b => .lit (.bool b)
  | .local x => .pv x
  | .env k _ => .env k

mutual

def SPath.lower : {T : Ty} → SPath C T → PTerm C
  | _, .alias x => .pv x
  | _, .loc l => l.lower

def Loc.lower : {T : Ty} → Loc C T → PTerm C
  | _, .root r _ => .root r
  | _, .field b f _ => .field b.lower f
  | _, .index _ b i => .at b.lower i.lower

def MPath.lower : {T : Ty} → MPath C T → ITerm C
  | _, .var x => .pv x
  | _, .loc l => .read .memory l.lower

def MLoc.lower : {T : Ty} → MLoc C T → MAddr C
  | _, .field b f _ => .field b.lower f
  | _, .index _ b i => .at b.lower i.lower

def Val.lower : {p : PrimTy} → Val C p → Term C
  | _, .simple s => s.lower
  | _, .read l => .find .storage l.lower
  | _, @Val.binop _ p _ op _ _ a b => .binop op p a.lower b.lower
  | _, @Val.unop _ p _ op _ _ a => .unop op p a.lower
  | _, .ternary c a b => .ite c.lower a.lower b.lower
  | _, .readMem l => .read .memory l.lower
  | _, .len b _ => .len .storage b.lower
  | _, .mlen b _ => .mlen .memory b.lower

end

/-- A write's source as a storage value: the value, or the copied subtree. -/
def Src.lower {T : Ty} : Src C T → SValT C
  | .val v => .val v.lower
  | .copy p _ => .find .storage p.lower

/-- A memory write's source. -/
def MSrc.lower {T : Ty} : MSrc C T → MValT C
  | .val v => .val v.lower
  | .ref p => .ref p.lower

/-! ### Lowering keeps meaning -/

/-- A simple value's term reads what it does: `x` is `x`. -/
@[simp] theorem Simple.lower_eval (σ : State) {p : PrimTy} (s : Simple C p) :
    s.lower.eval σ = s.eval σ := by
  cases s <;> rfl

mutual

/-- A path's term is the path it resolves to: `alice.account` lowers to
`alice.account`, `sp.age` to whatever `sp` is bound to, then `age`. -/
theorem SPath.lower_eval (σ : State) : {T : Ty} → (p : SPath C T) →
    p.lower.eval σ = p.resolve σ
  | _, .alias _ => rfl
  | _, .loc l => l.lower_eval σ

theorem Loc.lower_eval (σ : State) : {T : Ty} → (l : Loc C T) →
    l.lower.eval σ = l.resolve σ
  | _, .root .. => rfl
  | _, .field b f _ => by
    simp only [Loc.lower, tm_eval, Loc.resolve, b.lower_eval σ]
  | _, .index _ b i => by
    simp only [Loc.lower, tm_eval, Loc.resolve, b.lower_eval σ, i.lower_eval σ]

theorem MPath.lower_eval (σ : State) : {T : Ty} → (p : MPath C T) →
    p.lower.eval σ = (do (← p.mval σ).asRef)
  | _, .var x => by
    simp only [MPath.lower, tm_eval, MPath.mval, bind, Except.bind]
    cases σ.getEnv x with
    | error _ => rfl
    | ok b => cases b <;> rfl
  | _, .loc l => by
    simp only [MPath.lower, tm_eval, MPath.mval, ← l.lower_eval σ, bind_assoc, pure_bind]

theorem MLoc.lower_eval (σ : State) : {T : Ty} → (l : MLoc C T) →
    (do readAddr σ (← l.lower.eval σ)) = l.read σ
  | _, .field b f _ => by
    simp only [MLoc.lower, tm_eval, MLoc.read, b.lower_eval σ, bind_assoc, pure_bind]
    rfl
  | _, .index _ b i => by
    simp only [MLoc.lower, tm_eval, MLoc.read, b.lower_eval σ, i.lower_eval σ, bind_assoc, pure_bind]
    rfl

/-- A value's term reads what it does: `alice.age + 1` lowers to
`find(storage, alice.age) + 1`. -/
theorem Val.lower_eval (σ : State) : {p : PrimTy} → (v : Val C p) →
    v.lower.eval σ = v.eval σ
  | _, .simple s => s.lower_eval σ
  | _, .read l => by
    simp only [Val.lower, tm_eval, Val.eval, l.lower_eval σ, pure_bind]
  | _, .binop _ _ _ a b => by
    simp only [Val.lower, tm_eval, Val.eval, a.lower_eval σ, b.lower_eval σ]
  | _, .unop _ _ _ a => by
    simp only [Val.lower, tm_eval, Val.eval, a.lower_eval σ]
  | _, .ternary c a b => by
    simp only [Val.lower, tm_eval, Val.eval, c.lower_eval σ, a.lower_eval σ, b.lower_eval σ]
  | _, .readMem l => by
    simp only [Val.lower, tm_eval, Val.eval, ← l.lower_eval σ, bind_assoc, pure_bind]
  | _, .len b _ => by
    simp only [Val.lower, tm_eval, Val.eval, b.lower_eval σ, pure_bind]
  | _, .mlen b _ => by
    simp only [Val.lower, tm_eval, Val.eval, b.lower_eval σ, bind_assoc, pure_bind]

end

end Solidity
