import Solidity.Semantics.Agree
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

/-- What a modality says of a run that halts: every box formula holds of it,
no diamond formula does. -/
def Modality.onHalt : Modality → Prop
  | .diamond => False
  | .box => True

/-- `p` after a run under `m`: `p` of the state it ends in, or `m.onHalt`. -/
def Modality.after (m : Modality) (p : State → Prop) : Res State → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-! ## Terms -/

mutual

/-- A value term. -/
inductive Term (C : Contract) where
  | lit (v : Value)
  | pv (x : Var)
  /-- `a ⊕ b`, range-checked at `p` as the interpreter checks it. -/
  | binop (op : BinOp) (p : PrimTy) (a b : Term C)
  | unop (op : UnOp) (p : PrimTy) (a : Term C)
  /-- `find(s, p)`, and at a state variable KeY's `select(s, r)`. -/
  | find (s : STerm C) (p : PTerm C)
  /-- `s[p].length`: KeY's `find(s, p.size)`. -/
  | len (s : STerm C) (p : PTerm C)
  /-- `read(m, a)`: a value in memory. -/
  | read (m : MTerm C) (a : MAddr C)
  /-- `c ? a : b`, KeY's `if c then a else b`. -/
  | ite (c a b : Term C)
  /-- `m[i].length`: KeY's `read(m, i, size)`. -/
  | mlen (m : MTerm C) (i : ITerm C)
  /-- `msgSender`, `msgValue`, `selfBalance`: KeY's program variables of
  `netHeader.key`, and `block.timestamp`. -/
  | env (k : EnvKey)
  /-- `net(a)`: what the ledger holds for the address `a`, KeY's
  `selectSt(net, at(a))`; `0` where it never booked `a`. -/
  | net (a : Term C)
  /-- `x[a]`: what the ledger bound at `x` holds for `a`, KeY's
  `selectSt(oldNet, at(a))`, which a specification's `\old(net(a))` reads. -/
  | netOf (x : Var) (a : Term C)

/-- A storage path. -/
inductive PTerm (C : Contract) where
  | root (r : Name)
  | pv (x : Var)
  | field (p : PTerm C) (f : Name)
  /-- `p[i]`, the index checked against `p`'s length where it is taken
  (`State.checkIndex`), as the program checks it. -/
  | at (p : PTerm C) (i : Term C)
  /-- `p[p.length]`: the slot one past the end, where `lsv = p.push()` binds
  its alias (KeY's `consr(p, at(find(storage, consr(p, size))))`).  No bounds
  check: it is past them by construction. -/
  | next (p : PTerm C)

/-- A storage. -/
inductive STerm (C : Contract) where
  | storage
  /-- A storage variable: KeY's `old`, of sort `Struct`, bound by the update
  `old := storage` in front of a specification's modality. -/
  | pv (x : Var)
  /-- `save(s, p, v)`; at a state variable, KeY's `store(s, r, v)`. -/
  | save (s : STerm C) (p : PTerm C) (v : SValT C)
  /-- `delAt(s, p)`: the value at `p` reset to its default. -/
  | delAt (s : STerm C) (p : PTerm C)
  /-- `save(save(s, p[p.length], v), p.length, p.length + 1)`. -/
  | push (s : STerm C) (p : PTerm C) (v : SValT C)
  /-- `save(delAt(s, p[p.length]), p.length, p.length + 1)`: the slot a bare
  `push()` lands on, recycled or the default of `E`. -/
  | pushSlot (s : STerm C) (p : PTerm C) (E : Ty)
  /-- `save(delAt(s, p[p.length - 1]), p.length, p.length - 1)`. -/
  | pop (s : STerm C) (p : PTerm C)
  /-- `save(s, p.length, p.length - 1)`: a pop that leaves the element as it
  is, an array of mappings'. -/
  | shrink (s : STerm C) (p : PTerm C)
  /-- The extent write of `lsv = p.push()`: `save(s, p.length, p.length + 1)`. -/
  | extend (s : STerm C) (p : PTerm C) (E : Ty)
  /-- `select(s, r)`: the struct at member `r` of `s`, KeY's
  `selectSt<[Struct]>(s, r)`.  No program writes it: it is a line of a read
  taken head first, as solkey reads `find(s, cons(r, flds))`. -/
  | select (s : STerm C) (r : Name)

/-- What a storage `save` writes: a value, a subtree read out of a storage,
or a memory object copied back (`copyMem(mtSt, m, i)`). -/
inductive SValT (C : Contract) where
  | val (t : Term C)
  | find (s : STerm C) (p : PTerm C)
  | copyMem (m : MTerm C) (i : ITerm C)
  /-- `newArr(n)`: an array of `n` defaults of `R`'s element type, what
  `new R(n)` copies into memory (`newArrVal`). -/
  | newArr (R : RefTy) (n : Term C)

/-- A memory identity. -/
inductive ITerm (C : Contract) where
  | pv (x : Var)
  /-- The reference held at a memory location. -/
  | read (m : MTerm C) (a : MAddr C)
  /-- `freshId(addM(m))`: the identity allocating a default `R` takes. -/
  | alloc (m : MTerm C) (R : RefTy)
  /-- `freshId(copySt(m, v))`: the identity a copy of `v` takes. -/
  | copy (m : MTerm C) (v : SValT C)

/-- A member or an element of a memory object. -/
inductive MAddr (C : Contract) where
  | field (i : ITerm C) (f : Name)
  | at (i : ITerm C) (k : Term C)

/-- A memory. -/
inductive MTerm (C : Contract) where
  | memory
  /-- `write(m, a, v)`. -/
  | write (m : MTerm C) (a : MAddr C) (v : MValT C)
  /-- `addM(m)`: a default `R` allocated. -/
  | addM (m : MTerm C) (R : RefTy)
  /-- `copySt(m, v)`: a storage value copied in. -/
  | copySt (m : MTerm C) (v : SValT C)

/-- What a memory `write` writes: a value or a reference. -/
inductive MValT (C : Contract) where
  | val (t : Term C)
  | ref (i : ITerm C)

end

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

mutual

def Term.eval (σ : State) : Term C → Res Value
  | .lit v => pure v
  | .pv x => do
    match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. | .mref _ | .store _ | .ledger _ => .error .stuck
  | .binop op p a b => do evalBinop op p (← a.eval σ) (b.eval σ)
  | .unop op p a => do unopCheck op p (← applyUnOp op (← a.eval σ))
  | .find s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    (← τ.findStorage r segs).asValue
  | .len s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    arrayLen τ r segs
  | .read m a => do
    let τ ← m.eval σ
    (← readAddr τ (← a.eval σ)).asValue
  | .ite c a b => do pickBranch (← c.eval σ) (a.eval σ) (b.eval σ)
  | .mlen m i => do
    let τ ← m.eval σ
    memArrayLen τ (← i.eval σ)
  | .env k => pure (.int (σ.envVal k))
  | .net a => do pure (.int (σ.getNet (← (← a.eval σ).asInt)))
  | .netOf x a => do
    match ← σ.getEnv x with
    | .ledger l => pure (.int ((lookupBy (← (← a.eval σ).asInt) l).getD 0))
    | .val _ | .spath .. | .mref _ | .store _ => .error .stuck

def PTerm.eval (σ : State) : PTerm C → Res (Name × List Seg)
  | .root r => pure (r, [])
  | .pv x => aliasPath σ x
  | .field p f => do
    let (r, segs) ← p.eval σ
    pure (r, segs ++ [.field f])
  | .at p i => do
    let (r, segs) ← p.eval σ
    let i ← (← i.eval σ).asInt
    σ.checkIndex r segs i
    pure (r, segs ++ [.at i])
  | .next p => do
    let (r, segs) ← p.eval σ
    match ← σ.findStorage r segs with
    | .array elems _ _ => pure (r, segs ++ [.at elems.length])
    | .prim _ | .struct _ | .map _ _ => .error .stuck

def STerm.eval (σ : State) : STerm C → Res State
  | .storage => pure σ
  | .pv x => do
    match ← σ.getEnv x with
    | .store st => pure { σ with storage := st }
    | .val _ | .spath .. | .mref _ | .ledger _ => .error .stuck
  | .save s p v => do
    let sv ← v.eval σ
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    τ.writeStorage r segs sv
  | .delAt s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    let cur ← τ.findStorage r segs
    τ.saveStorage r segs cur.defaultOf
  | .select s r => do
    let τ ← s.eval σ
    match ← τ.findStorage r [] with
    | .struct fields => pure { τ with storage := fields }
    | .prim _ | .array .. | .map .. => .error .stuck
  | .push s p v => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    pushAt τ .uint r segs fun _ => do pure (← v.eval σ).strip
  | .pushSlot s p E => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    pushAt τ E r segs pure
  | .pop s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    popAt τ false r segs
  | .shrink s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    popAt τ true r segs
  | .extend s p E => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    return (← pushPlaceAt τ E r segs).1

def SValT.eval (σ : State) : SValT C → Res SVal
  | .val t => do pure (← t.eval σ).toSVal
  | .find s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    τ.findStorage r segs
  | .copyMem m i => do
    let τ ← m.eval σ
    copyMem τ (.ref (← i.eval σ))
  | .newArr R n => do pure (newArrVal R (← (← n.eval σ).asInt))

def ITerm.eval (σ : State) : ITerm C → Res Nat
  | .pv x => do
    match ← σ.getEnv x with
    | .mref id => pure id
    | .val _ | .spath .. | .store _ | .ledger _ => .error .stuck
  | .read m a => do
    let τ ← m.eval σ
    (← readAddr τ (← a.eval σ)).asRef
  | .alloc m R => do
    let τ ← m.eval σ
    return (← allocDefault τ R).2
  | .copy m v => do
    let sv ← v.eval σ
    let τ ← m.eval σ
    (← copyStToM τ sv).2.asRef

def MAddr.eval (σ : State) : MAddr C → Res Addr
  | .field i f => do pure (.memoryField (← i.eval σ) f)
  | .at i k => do
    let id ← i.eval σ
    pure (.memoryIndex id (← (← k.eval σ).asInt))

def MTerm.eval (σ : State) : MTerm C → Res State
  | .memory => pure σ
  | .write m a v => do
    let mv ← v.eval σ
    let τ ← m.eval σ
    writeAddr τ mv (← a.eval σ)
  | .addM m R => do
    let τ ← m.eval σ
    return (← allocDefault τ R).1
  | .copySt m v => do
    let sv ← v.eval σ
    let τ ← m.eval σ
    return (← copyStToM τ sv).1

def MValT.eval (σ : State) : MValT C → Res MVal
  | .val t => do pure (← t.eval σ).toMVal
  | .ref i => do pure (.ref (← i.eval σ))

end

/-! ## What a term denotes in the Theory

`Term.denote` reads a formula's terms in the Theory algebra over the storage
node `State.abs σ`, total, as KeY reads them: a read off the end of what is
there is a node, not a halt.  `Term.eval` is the interpreter's reading; the
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
  `PTerm.eval` does.
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

mutual

/-- A value term in the Theory, over `State.abs σ`. -/
def Term.denote (σ : State) : Term C → StValue
  | .lit v => .prim v
  | .pv x => match σ.getEnv x with
    | .ok (.val v) => .prim v
    | _ => .st .mtSt
  | .binop op p a b => Res.toSt (do evalBinop op p (← (a.denote σ).toRes) (b.denote σ).toRes)
  | .unop op p a => Res.toSt (do unopCheck op p (← applyUnOp op (← (a.denote σ).toRes)))
  | .find s p => findSt (s.denote σ) (p.denote σ)
  | .len s p => findSt (s.denote σ) (p.denote σ ++ [lengthSeg])
  | .read m a => Res.toSt ((Term.read m a).eval σ)
  | .ite c a b => match c.denote σ with
    | .prim (.bool true) => a.denote σ
    | .prim (.bool false) => b.denote σ
    | _ => .st .mtSt
  | .mlen m i => Res.toSt ((Term.mlen m i).eval σ)
  | .env k => .prim (.int (σ.envVal k))
  | .net a => match a.denote σ with
    | .prim (.int n) => .prim (.int (σ.getNet n))
    | _ => .st .mtSt
  | .netOf x a => match σ.getEnv x, a.denote σ with
    | .ok (.ledger l), .prim (.int n) => .prim (.int ((lookupBy n l).getD 0))
    | _, _ => .st .mtSt

/-- A path from the storage node; indices are not bounds-checked (KeY's guard). -/
def PTerm.denote (σ : State) : PTerm C → List Seg
  | .root r => [.field r]
  | .pv x => match aliasPath σ x with
    | .ok (r, segs) => rootPath r segs
    | .error _ => []
  | .field p f => p.denote σ ++ [.field f]
  | .at p i => p.denote σ ++ [.at (asInt (i.denote σ))]
  | .next p => p.denote σ ++ [.at (lenAt σ.abs (p.denote σ))]

/-- A storage term in the Theory: the storage node it denotes. -/
def STerm.denote (σ : State) : STerm C → Struct
  | .storage => σ.abs
  | .pv x => match σ.getEnv x with
    | .ok (.store roots) => SVal.abs.fields roots
    | _ => .mtSt
  | .save s p v => copyTo (s.denote σ) (p.denote σ) (v.denote σ)
  | .delAt s p => delAt (s.denote σ) (p.denote σ)
  | .push s p v => pushT (s.denote σ) (p.denote σ) (stripVal (v.denote σ))
  | .pushSlot s p E | .extend s p E =>
      pushSlotT E.isPrimitive (defaultForTy E).abs (s.denote σ) (p.denote σ)
  | .pop s p => popT (s.denote σ) (p.denote σ)
  | .shrink s p => shrinkT (s.denote σ) (p.denote σ)
  | .select s r => asStruct (selectSt (s.denote σ) (.field r))

/-- What a storage `save` writes, in the Theory. -/
def SValT.denote (σ : State) : SValT C → StValue
  | .val t => t.denote σ
  | .find s p => findSt (s.denote σ) (p.denote σ)
  | .copyMem m i => match (SValT.copyMem m i).eval σ with
    | .ok w => w.abs
    | .error _ => .st .mtSt
  | .newArr R n => (newArrVal R (asInt (n.denote σ))).abs

end


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
  /-- `net := store(net, at(r), net(r) ± a)`: the ledger's entry for `r`, in
  KeY's `int`. -/
  | net (r : Term C) (op : IntOp) (a : Term C)
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
    pure { τ with net := setBy addr (op.apply (σ₀.getNet addr) amt) σ₀.net }
  | .saveNet x, τ => pure (τ.setEnv x (.ledger σ₀.net))

/-- The state an update leaves, from `σ`. -/
def Upd.apply (U : Upd C) (σ : State) : Res State :=
  U.foldlM (fun τ e => e.write σ τ) σ

/-! ## States a callee may leave -/

/-- The state after a callback: storage, ledger and funds replaced by what
the callee left (KeY's `{storage := storageSk ‖ net := netSk ‖ selfBalance
:= selfBalanceSk}`), the locals and memory of the caller kept. -/
def Semantics.State.havoc (σ : State) (st : List (Name × SVal)) (nt : List (Int × Int))
    (bal : Int) : State :=
  { σ with storage := st, net := nt, selfBalance := bal }

/-- A callee that changes nothing. -/
@[simp] theorem Semantics.State.havoc_self (σ : State) :
    σ.havoc σ.storage σ.net σ.selfBalance = σ := by
  cases σ; rfl

theorem Semantics.EnvAgreeExcept.havoc {ns : List Var} {σ τ : State} (h : EnvAgreeExcept ns σ τ)
    (st : List (Name × SVal)) (nt : List (Int × Int)) (bal : Int) :
    EnvAgreeExcept ns (σ.havoc st nt bal) (τ.havoc st nt bal) :=
  ⟨rfl, h.heap, h.nextId, rfl, h.env, rfl, h.tx⟩

/-! ## Formulas -/

/-- A formula about programs of the contract `C`. -/
inductive Fml (C : Contract) where
  | tt
  /-- `a = b`, read in the Theory (`Term.denote`): total, so it may hold
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
  /-- `{havoc} φ`: `φ` after any storage, ledger and funds a callee may
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
  | .modal m P φ => m.after (holds · φ) (Prog.run σ P)
  | .havoc φ => ∀ st nt bal, holds (σ.havoc st nt bal) φ
  | .all x p φ => ∀ v, p.admits v → holds (σ.setEnv x (.val v)) φ

/-- Valid: true in every state. -/
def Valid (φ : Fml C) : Prop := ∀ σ, holds σ φ

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

mutual

def Term.vars : Term C → List Var
  | .lit _ => []
  | .pv x => [x]
  | .binop _ _ a b => a.vars ++ b.vars
  | .unop _ _ a => a.vars
  | .find s p | .len s p => s.vars ++ p.vars
  | .read m a => m.vars ++ a.vars
  | .ite c a b => c.vars ++ a.vars ++ b.vars
  | .mlen m i => m.vars ++ i.vars
  | .env _ => []
  | .net a => a.vars
  | .netOf x a => x :: a.vars

def PTerm.vars : PTerm C → List Var
  | .root _ => []
  | .pv x => [x]
  | .field p _ => p.vars
  | .at p i => p.vars ++ i.vars
  | .next p => p.vars

def STerm.vars : STerm C → List Var
  | .storage => []
  | .pv x => [x]
  | .save s p v | .push s p v => s.vars ++ p.vars ++ v.vars
  | .delAt s p | .pushSlot s p _ | .pop s p | .shrink s p | .extend s p _ => s.vars ++ p.vars
  | .select s _ => s.vars

def SValT.vars : SValT C → List Var
  | .val t => t.vars
  | .find s p => s.vars ++ p.vars
  | .copyMem m i => m.vars ++ i.vars
  | .newArr _ n => n.vars

def ITerm.vars : ITerm C → List Var
  | .pv x => [x]
  | .read m a => m.vars ++ a.vars
  | .alloc m _ => m.vars
  | .copy m v => m.vars ++ v.vars

def MAddr.vars : MAddr C → List Var
  | .field i _ => i.vars
  | .at i k => i.vars ++ k.vars

def MTerm.vars : MTerm C → List Var
  | .memory => []
  | .write m a v => m.vars ++ a.vars ++ v.vars
  | .addM m _ => m.vars
  | .copySt m v => m.vars ++ v.vars

def MValT.vars : MValT C → List Var
  | .val t => t.vars
  | .ref i => i.vars

end

def UpdElem.vars : UpdElem C → List Var
  | .val x t => x :: t.vars
  | .path x p => x :: p.vars
  | .mref x i => x :: i.vars
  | .storage s => s.vars
  | .store x s => x :: s.vars
  | .memory m => m.vars
  | .selfBalance _ a => a.vars
  | .net r _ a => r.vars ++ a.vars
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

mutual

theorem Term.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (t : Term C) → Avoids t.vars ns → t.eval σ = t.eval τ
  | .lit _, _ => rfl
  | .pv x, h => by simp only [Term.eval, getEnv_congr hag (h.head)]
  | .binop _ _ a b, h => by
    simp only [Term.eval, a.eval_frame hag h.left, b.eval_frame hag h.right]
  | .unop _ _ a, h => by simp only [Term.eval, a.eval_frame hag h]
  | .find s p, h => by
    simp only [Term.eval, p.eval_frame hag h.right]
    exact ResultsAgree.bindEq (s.eval_frame hag h.left) fun _ _ h' => by
      simp only [findStorage_congr h']
  | .len s p, h => by
    simp only [Term.eval, p.eval_frame hag h.right]
    exact ResultsAgree.bindEq (s.eval_frame hag h.left) fun _ _ h' => by
      simp only [arrayLen_congr h']
  | .read m a, h => by
    simp only [Term.eval, a.eval_frame hag h.right]
    exact ResultsAgree.bindEq (m.eval_frame hag h.left) fun _ _ h' => by
      simp only [readAddr_congr h']
  | .ite c a b, h => by
    simp only [Term.eval, c.eval_frame hag h.left.left, a.eval_frame hag h.left.right,
      b.eval_frame hag h.right]
  | .mlen m i, h => by
    simp only [Term.eval, i.eval_frame hag h.right]
    exact ResultsAgree.bindEq (m.eval_frame hag h.left) fun _ _ h' => by
      simp only [memArrayLen, getObj_congr h']
  | .env k, _ => by simp only [Term.eval, State.envVal_congr hag]
  | .net a, h => by simp only [Term.eval, a.eval_frame hag h, State.getNet, hag.net]
  | .netOf x a, h => by simp only [Term.eval, a.eval_frame hag h.tail, getEnv_congr hag h.head]

theorem PTerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (p : PTerm C) → Avoids p.vars ns → p.eval σ = p.eval τ
  | .root _, _ => rfl
  | .pv x, h => aliasPath_frame hag (h.head)
  | .field p _, h => by simp only [PTerm.eval, p.eval_frame hag h]
  | .at p i, h => by
    simp only [PTerm.eval, p.eval_frame hag h.left, i.eval_frame hag h.right, checkIndex_congr hag]
  | .next p, h => by simp only [PTerm.eval, p.eval_frame hag h, findStorage_congr hag]

theorem STerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (s : STerm C) → Avoids s.vars ns → ResultsAgree ns (s.eval σ) (s.eval τ)
  | .storage, _ => hag
  | .pv x, h => by
    simp only [STerm.eval, getEnv_congr hag (h.head)]
    rcases τ.getEnv x with _ | b
    · exact ResultsAgree.refl _ _
    · cases b
      all_goals first
        | exact ResultsAgree.refl _ _
        | exact ⟨rfl, hag.heap, hag.nextId, hag.net, hag.env, hag.selfBalance, hag.tx⟩
  | .save s p v, h => by
    simp only [STerm.eval, v.eval_frame hag h.right, p.eval_frame hag h.left.right]
    refine bindPureResults_agree _ fun _ => ?_
    refine ResultsAgree.bind (s.eval_frame hag h.left.left) fun _ _ h' => ?_
    agree_run h'
  | .delAt s p, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    simp only [findStorage_congr h']
    agree_run h'
  | .push s p v, h => by
    simp only [STerm.eval, p.eval_frame hag h.left.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left.left) fun _ _ h' => ?_
    refine bindPureResults_agree _ fun _ => pushAt_agree h' _ _ _ fun _ => ?_
    simp only [v.eval_frame hag h.right]
  | .pushSlot s p _, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => pushAt_agree h' _ _ _ fun _ => rfl
  | .pop s p, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    agree_run h'
  | .shrink s p, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    agree_run h'
  | .extend s p _, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    refine bindPureResults_agree _ fun _ => ?_
    exact ResAgree.bindState (pushPlaceAt_agree h' _ _ _) fun _ _ _ h'' => h''
  | .select s r, h => by
    simp only [STerm.eval]
    refine ResultsAgree.bind (s.eval_frame hag h) fun _ τ' h' => ?_
    simp only [findStorage_congr h']
    rcases τ'.findStorage r [] with _ | w
    · exact ResultsAgree.refl _ _
    · cases w
      all_goals first
        | exact ResultsAgree.refl _ _
        | exact ⟨rfl, h'.heap, h'.nextId, h'.net, h'.env, h'.selfBalance, h'.tx⟩

theorem SValT.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (v : SValT C) → Avoids v.vars ns → v.eval σ = v.eval τ
  | .val t, h => by simp only [SValT.eval, t.eval_frame hag h]
  | .find s p, h => by
    simp only [SValT.eval, p.eval_frame hag h.right]
    exact ResultsAgree.bindEq (s.eval_frame hag h.left) fun _ _ h' => by
      simp only [findStorage_congr h']
  | .copyMem m i, h => by
    simp only [SValT.eval, i.eval_frame hag h.right]
    exact ResultsAgree.bindEq (m.eval_frame hag h.left) fun _ _ h' => by
      simp only [copyMem_congr h']
  | .newArr _ n, h => by simp only [SValT.eval, n.eval_frame hag h]

theorem ITerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (i : ITerm C) → Avoids i.vars ns → i.eval σ = i.eval τ
  | .pv x, h => by simp only [ITerm.eval, getEnv_congr hag (h.head)]
  | .read m a, h => by
    simp only [ITerm.eval, a.eval_frame hag h.right]
    exact ResultsAgree.bindEq (m.eval_frame hag h.left) fun _ _ h' => by
      simp only [readAddr_congr h']
  | .alloc m R, h => by
    simp only [ITerm.eval]
    refine ResultsAgree.bindEq (m.eval_frame hag h) fun _ _ h' => ?_
    rcases (allocDefault_agree h' R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
      simp only [h₁, h₂] <;> rfl
  | .copy m v, h => by
    simp only [ITerm.eval, v.eval_frame hag h.right]
    refine congrArg (_ >>= ·) (funext fun sv => ?_)
    refine ResultsAgree.bindEq (m.eval_frame hag h.left) fun _ _ h' => ?_
    rcases (copyStToM_agree h' sv).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
      simp only [h₁, h₂] <;> rfl

theorem MAddr.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (a : MAddr C) → Avoids a.vars ns → a.eval σ = a.eval τ
  | .field i _, h => by simp only [MAddr.eval, i.eval_frame hag h]
  | .at i k, h => by simp only [MAddr.eval, i.eval_frame hag h.left, k.eval_frame hag h.right]

theorem MTerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (m : MTerm C) → Avoids m.vars ns → ResultsAgree ns (m.eval σ) (m.eval τ)
  | .memory, _ => hag
  | .write m a v, h => by
    simp only [MTerm.eval, v.eval_frame hag h.right, a.eval_frame hag h.left.right]
    refine bindPureResults_agree _ fun _ => ?_
    refine ResultsAgree.bind (m.eval_frame hag h.left.left) fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => writeAddr_agree h' _ _
  | .addM m R, h => by
    simp only [MTerm.eval]
    refine ResultsAgree.bind (m.eval_frame hag h) fun _ _ h' => ?_
    exact ResAgree.bindState (allocDefault_agree h' R) fun _ _ _ h'' => h''
  | .copySt m v, h => by
    simp only [MTerm.eval, v.eval_frame hag h.right]
    refine bindPureResults_agree _ fun sv => ?_
    refine ResultsAgree.bind (m.eval_frame hag h.left) fun _ _ h' => ?_
    exact ResAgree.bindState (copyStToM_agree h' sv) fun _ _ _ h'' => h''

theorem MValT.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (v : MValT C) → Avoids v.vars ns → v.eval σ = v.eval τ
  | .val t, h => by simp only [MValT.eval, t.eval_frame hag h]
  | .ref i, h => by simp only [MValT.eval, i.eval_frame hag h]

end

mutual

theorem Term.denote_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (t : Term C) → Avoids t.vars ns → t.denote σ = t.denote τ
  | .lit _, _ => rfl
  | .pv x, h => by simp only [Term.denote, getEnv_congr hag (h.head)]
  | .binop _ _ a b, h => by
    simp only [Term.denote, a.denote_frame hag h.left, b.denote_frame hag h.right]
  | .unop _ _ a, h => by simp only [Term.denote, a.denote_frame hag h]
  | .find s p, h | .len s p, h => by
    simp only [Term.denote, s.denote_frame hag h.left, p.denote_frame hag h.right]
  | .read m a, h => by simp only [Term.denote, (Term.read m a).eval_frame hag h]
  | .ite c a b, h => by
    simp only [Term.denote, c.denote_frame hag h.left.left, a.denote_frame hag h.left.right,
      b.denote_frame hag h.right]
  | .mlen m i, h => by simp only [Term.denote, (Term.mlen m i).eval_frame hag h]
  | .env k, _ => by simp only [Term.denote, State.envVal_congr hag]
  | .net a, h => by simp only [Term.denote, a.denote_frame hag h, State.getNet, hag.net]
  | .netOf x a, h => by
    simp only [Term.denote, a.denote_frame hag h.tail, getEnv_congr hag h.head]

theorem PTerm.denote_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (p : PTerm C) → Avoids p.vars ns → p.denote σ = p.denote τ
  | .root _, _ => rfl
  | .pv x, h => by simp only [PTerm.denote, aliasPath_frame hag (h.head)]
  | .field p _, h => by simp only [PTerm.denote, p.denote_frame hag h]
  | .at p i, h => by
    simp only [PTerm.denote, p.denote_frame hag h.left, i.denote_frame hag h.right]
  | .next p, h => by simp only [PTerm.denote, p.denote_frame hag h, State.abs, hag.storage]

theorem STerm.denote_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (s : STerm C) → Avoids s.vars ns → s.denote σ = s.denote τ
  | .storage, _ => by simp only [STerm.denote, State.abs, hag.storage]
  | .pv x, h => by simp only [STerm.denote, getEnv_congr hag (h.head)]
  | .save s p v, h | .push s p v, h => by
    simp only [STerm.denote, s.denote_frame hag h.left.left, p.denote_frame hag h.left.right,
      v.denote_frame hag h.right]
  | .delAt s p, h | .pushSlot s p _, h | .pop s p, h | .shrink s p, h | .extend s p _, h => by
    simp only [STerm.denote, s.denote_frame hag h.left, p.denote_frame hag h.right]
  | .select s _, h => by simp only [STerm.denote, s.denote_frame hag h]

theorem SValT.denote_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (v : SValT C) → Avoids v.vars ns → v.denote σ = v.denote τ
  | .val t, h => t.denote_frame hag h
  | .find s p, h => by
    simp only [SValT.denote, s.denote_frame hag h.left, p.denote_frame hag h.right]
  | .copyMem m i, h => by simp only [SValT.denote, (SValT.copyMem m i).eval_frame hag h]
  | .newArr _ n, h => by simp only [SValT.denote, n.denote_frame hag h]

end

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
    simp only [UpdElem.write, r.eval_frame h₀ hv.left, a.eval_frame h₀ hv.right, State.getNet,
      h₀.net]
    agree_run h
    exact ⟨h.storage, h.heap, h.nextId, rfl, h.env, h.selfBalance, h.tx⟩
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
    exact m.after_frame (Prog.run_frame hag P h.left) fun _ _ h' => holds_frame φ h.right h'
  | .havoc φ, h, _, _, hag => by
    simp only [holds]
    exact forall_congr' fun st => forall_congr' fun nt => forall_congr' fun bal =>
      holds_frame φ h (hag.havoc st nt bal)
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
    simp only [Loc.lower, PTerm.eval, Loc.resolve, b.lower_eval σ]
  | _, .index _ b i => by
    simp only [Loc.lower, PTerm.eval, Loc.resolve, b.lower_eval σ, i.lower_eval σ]

theorem MPath.lower_eval (σ : State) : {T : Ty} → (p : MPath C T) →
    p.lower.eval σ = (do (← p.mval σ).asRef)
  | _, .var x => by
    simp only [MPath.lower, ITerm.eval, MPath.mval, bind, Except.bind]
    cases σ.getEnv x with
    | error _ => rfl
    | ok b => cases b <;> rfl
  | _, .loc l => by
    simp only [MPath.lower, ITerm.eval, MTerm.eval, MPath.mval, ← l.lower_eval σ, bind_assoc,
      pure_bind]

theorem MLoc.lower_eval (σ : State) : {T : Ty} → (l : MLoc C T) →
    (do readAddr σ (← l.lower.eval σ)) = l.read σ
  | _, .field b f _ => by
    simp only [MLoc.lower, MAddr.eval, MLoc.read, b.lower_eval σ, bind_assoc, pure_bind]
    rfl
  | _, .index _ b i => by
    simp only [MLoc.lower, MAddr.eval, MLoc.read, b.lower_eval σ, i.lower_eval σ, bind_assoc,
      pure_bind]
    rfl

/-- A value's term reads what it does: `alice.age + 1` lowers to
`find(storage, alice.age) + 1`. -/
theorem Val.lower_eval (σ : State) : {p : PrimTy} → (v : Val C p) →
    v.lower.eval σ = v.eval σ
  | _, .simple s => s.lower_eval σ
  | _, .read l => by
    simp only [Val.lower, Term.eval, STerm.eval, Val.eval, l.lower_eval σ, pure_bind]
  | _, .binop _ _ _ a b => by
    simp only [Val.lower, Term.eval, Val.eval, a.lower_eval σ, b.lower_eval σ]
  | _, .unop _ _ _ a => by
    simp only [Val.lower, Term.eval, Val.eval, a.lower_eval σ]
  | _, .ternary c a b => by
    simp only [Val.lower, Term.eval, Val.eval, c.lower_eval σ, a.lower_eval σ, b.lower_eval σ]
  | _, .readMem l => by
    simp only [Val.lower, Term.eval, MTerm.eval, Val.eval, ← l.lower_eval σ, bind_assoc, pure_bind]
  | _, .len b _ => by
    simp only [Val.lower, Term.eval, STerm.eval, Val.eval, b.lower_eval σ, pure_bind]
  | _, .mlen b _ => by
    simp only [Val.lower, Term.eval, MTerm.eval, Val.eval, b.lower_eval σ, bind_assoc, pure_bind]

end

end Solidity
