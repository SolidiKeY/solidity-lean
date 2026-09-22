import Solidity.Update.Bridges

/-!
# Evaluating a taclet's update

`Calculus/Rules.lean` writes each terminal rule's `\replacewith` as a first-order
`UpdTerm` — syntax with no `State` in it.  This module gives that syntax its
meaning, as a `Upd.Par`: one elementary update per component the taclet writes,
each with a *pre-state* reader, which is what makes a KeY parallel update
parallel.

## The readers are the interpreter's

Every reader here is one of `Wp/Terminal/Table.lean`'s — `readVal`,
`placePath`, `locPath`, `readMem`, `rhsSVal`, `rhsMVal`, `binopVal`,
`incDecUpd`, `allocDefault` — or a component projection of one of the
`State` writers (`Upd.saveSt`, `Upd.heapOf`).  Nothing is re-derived.

That is deliberate, and it is what gives `Update/TacletTable.lean` its content.
If the update language had its own arithmetic and its own storage model, a
bridge theorem would be comparing two of my own definitions.  Sharing the
readers means the theorem is about the thing that actually differs: *which*
update shape each rule picked, in what order it reads its operands, and which
guard it put in front.  Where the interpreter and KeY genuinely disagree — the
checked arithmetic of `Sym.combined`, the mapping refusal in `rhsSVal`,
`transfer`'s balance — the disagreement is inherited here rather than hidden,
and `Update/SolcDelta.lean` is the table of it.

## Guards evaluate to `Res Bool`, not `Bool`

`Guard.premises` are read first, in the interpreter's order, purely for their
halt: on `arr[i] = 1 / 0` with `i` out of bounds the right-hand side faults
before the bounds are ever consulted, so the guard must be able to say "stuck"
rather than "false".  Only when every premise has succeeded is the formula
decided.
-/

namespace Solidity
namespace Update

open Semantics Wp Rules

/-! ## Reading a `Sym` -/

/-- The length of a storage array value. -/
def arrayLength : SVal -> Res Value
  | SVal.array elems _ => .ok (Value.int elems.length)
  | _ => .error .stuck

/-- The value at an *l-value*, as `compoundAssignUpd` and `incDecUpd` read it:
a storage place resolves by origin (`locPath`), a memory slot through its
base identity.  Distinct from `readVal`, which resolves a storage root env
first and so follows a local alias. -/
def locVal (s : State) : WrappedExpr -> Res Value
  | WrappedExpr.var Kind.stack _ fld => stackVal s fld.name
  | e@(WrappedExpr.var Kind.storage _ _) =>
      locPath s e >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue
  | e@(WrappedExpr.field Kind.storage _ _ _) =>
      locPath s e >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue
  | e@(WrappedExpr.index Kind.storage _ _ _) =>
      locPath s e >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue
  | WrappedExpr.field Kind.memory _ base f =>
      memBase s base >>= fun id => memFieldVal s id f.name
  | WrappedExpr.index Kind.memory _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        memIndexVal s id i
  | _ => .error .stuck

/-- The value of a *terminal* expression: `Wp.readVal` on a simple place,
extended with the three operator nodes a terminal rule can carry.  `++t` is
read for its *value*; the write-back it also performs is a separate element of
the same parallel update (`UpdElem.bumpOf`), which is how KeY writes it. -/
def readTerm (s : State) : WrappedExpr -> Res Value
  | WrappedExpr.binop op l r => binopVal op l r s
  | WrappedExpr.unop op a => unopVal op a s
  | WrappedExpr.incDec op t => (incDecUpd op t s).map Prod.snd
  | e => readVal s e

/-- A `Sym` in the state its update is applied in. -/
def Sym.eval (s : State) : Sym -> Res Value
  | .read e => readTerm s e
  | .current target => locVal s target
  | .length arr =>
      placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= arrayLength
  | .netOf addr => (readVal s addr >>= Value.asInt).map fun a => Value.int (s.getNet a)
  | .combined op target value =>
      readVal s value >>= fun v => locVal s target >>= fun old =>
        applyBinOp op old v >>= checkArith target.ty
  | .deflt ty => .ok (defaultValue ty)

/-! ## Reading the components an update writes -/

/-- `save(storage, p, v)` at an l-value path: the storage tree the write
installs.  A storage *root* resolves by origin, a nested place by
`placePath` — `locPath`'s split, which is `resolveLoc`'s. -/
def storageSave (s : State) (target : WrappedExpr) (v : SVal) :
    Res (List (Name × SVal)) :=
  locPath s target >>= fun p => Upd.saveSt s p.1 p.2 v

/-- `write(memory, mp, f, v)` / `write(memory, mp, at(i), v)`, as a state. -/
def memWriteIn (s : State) (target : WrappedExpr) (mv : MVal) : Res State :=
  match target with
  | WrappedExpr.field Kind.memory _ base f =>
      memBase s base >>= fun id => writeMemField s id f.name mv
  | WrappedExpr.index Kind.memory _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        writeMemIndex s id i mv
  | _ => .error .stuck

/-! ## `memory := …`

A memory update is a *term* (`Rules.MemTerm`), so evaluating it is one
recursion rather than one function per shape.  `memEval` returns the state the
term leaves **and** the root its allocator minted, if it has one: that pair is
what lets `{mv := freshId(m)}` and `{memory := m}` agree on which root without
either re-deriving it, because they are two projections of one evaluation of
one term.  KeY shares the schema variable `freshIdp`; this shares the subterm.

Note that the root is *not* the pre-state counter.  `Semantics.copyStToM`
copies a struct's fields before allocating the struct itself, so a `Person`
declaration mints its members first and the root last. -/

/-- The state a memory term leaves, and the root it allocated. -/
def memEval (s : State) : MemTerm -> Res (State × Option Nat)
  | .cur => .ok (s, none)
  | .addM m ty =>
      memEval s m >>= fun x =>
        match ty with
        | Ty.ref ref => (allocDefault x.1 ref).map fun y => (y.1, some y.2)
        | _ => .error .stuck
  -- `copySt` allocates the object it copies into (see `Rules.allocTerm`), and
  -- a *memory* source allocates nothing at all: an alias shares the identity.
  | .copySt m _ src =>
      memEval s m >>= fun x =>
        match src.kind with
        | Kind.memory =>
            readMem x.1 src >>= fun mv =>
              match mv with
              | MVal.ref id => .ok (x.1, some id)
              | _ => .error .stuck
        | Kind.storage =>
            placePath x.1 src >>= fun p =>
              x.1.findStorage p.1 p.2 >>= fun sv =>
                copyStToM x.1 sv >>= fun y =>
                  match y.2 with
                  | MVal.ref id => .ok (y.1, some id)
                  | _ => .error .stuck
        | Kind.stack => .error .stuck
  | .write m target v =>
      memEval s m >>= fun x =>
        (match v with
          | .sym t => (Sym.eval x.1 t).map fun w => (x.1, w.toMVal)
          | .image src => rhsMVal x.1 src
          | .fresh =>
              match x.2 with
              | some id => .ok (x.1, MVal.ref id)
              | none => .error .stuck
          | .defVal ty =>
              match ty with
              | Ty.prim PrimTy.bool => .ok (x.1, MVal.bool false)
              | Ty.prim PrimTy.uint => .ok (x.1, MVal.int 0)
              | Ty.prim PrimTy.int => .ok (x.1, MVal.int 0)
              | Ty.ref _ => .error .stuck) >>= fun y =>
          (memWriteIn y.1 target y.2).map fun t => (t, x.2)

/-- `x := t`. -/
def bindRhs (r : BindRhs) (s : State) : Res Binding :=
  match r with
  | .val t => (Sym.eval s t).map Binding.val
  | .path src => (placePath s src).map fun p => Binding.spath p.1 p.2
  | .pushSlot place =>
      match place with
      | WrappedExpr.pushPlace arr =>
          placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
            match cur with
            | SVal.array elems _ => .ok (Binding.spath p.1 (p.2 ++ [Seg.at elems.length]))
            | _ => .error .stuck
      | _ => .error .stuck
  | .mref src =>
      readMem s src >>= fun mv =>
        match mv with
        | MVal.ref id => .ok (Binding.mref id)
        | _ => .error .stuck
  | .freshId m =>
      memEval s m >>= fun x =>
        match x.2 with
        | some id => .ok (Binding.mref id)
        | none => .error .stuck

/-! ## `storage := …`

A storage update is a *term* (`Rules.StTerm`), so evaluating it is one
recursion rather than one function per shape — the same shape `memEval` has
on the memory side.  Every subterm is read in the state the update is
*applied* in, as KeY reads them: only the writes compose, so the recursion
threads the storage component and hands each target and value the pre-state.

`push` and `pop` have no arm here.  They are nested writes —
`save(save(storage, consr(arr, at(ℓ)), se), consr(arr, size), ℓ + 1)` and
`save(delAt(storage, consr(arr, at(ℓ - 1))), consr(arr, size), ℓ - 1)` — and
`Semantics.SVal.save` is what makes them denote: a write one past the end
appends, and a `size` write truncates, handing the cleared tail back as the
recycled slots `Semantics.pushSlot` deals out. -/

/-- The storage image of a `save`'s value slot. -/
def stVal (s : State) : StVal -> Res SVal
  | .sym t => (Sym.eval s t).map Value.toSVal
  -- `find(storage, src)` and `copyMem(mtSt, memory, src)` are one function
  -- here: `rhsSVal` picks between them by the source's kind, which is the
  -- sort the two KeY terms differ in.
  | .find src => rhsSVal s src
  | .copyMem src => rhsSVal s src
  | .pushed (some src) => rhsSVal s src
  | .pushed none => .error .stuck

/-- `save(st, p, v)` / `store(st, f, v)`, with the path and the value read in
`pre` and the write applied to the storage `g` the inner term left. -/
def storageSaveOn (pre : State) (g : List (Name × SVal)) (target : WrappedExpr)
    (v : SVal) : Res (List (Name × SVal)) :=
  locPath pre target >>= fun p => Upd.saveSt { pre with storage := g } p.1 p.2 v

/-- `storageSave` through the calculus's writer: the shape a terminal rule's
update has. -/
def storageSaveExt (s : State) (target : WrappedExpr) (v : SVal) :
    Res (List (Name × SVal)) :=
  locPath s target >>= fun p => Upd.saveSt s p.1 p.2 v

/-- `delAt(st, p)`: the value at `p` cleared in place, or — at an array index
one past the end — the recycled slot a bare `arr.push()` appends.  KeY writes
`delAt(storage, consr(arr, at(n)))` for both, and they are the same write:
`defaultOf` is idempotent, so clearing the slot a `pop` handed back is what
makes its mapping members survive into the next `push`. -/
def delAtOn (pre : State) (g : List (Name × SVal)) (target : WrappedExpr) :
    Res (List (Name × SVal)) :=
  -- An update's index is a *term*, not a program expression: `pop` clears
  -- `consr(arr, at(ℓ - 1))`, and `ℓ - 1` is arithmetic on the extent that
  -- `simpleInt` -- which answers for `sp[ie]`, where the rules have already
  -- frozen the index into a variable -- is stuck on.  So the index is read
  -- with `readTerm`, the reader a `Sym` uses; on a frozen index the two agree.
  let resolved : Res (State × Name × List Seg) :=
    match target with
    | WrappedExpr.index _ _ base ix =>
        placePath pre base >>= fun p =>
          readTerm pre ix >>= Value.asInt >>= fun i =>
            .ok (pre, p.1, p.2 ++ [Seg.at i])
    | _ => deletePath pre target
  resolved >>= fun x =>
    let s' := { x.1 with storage := g }
    s'.findStorage x.2.1 x.2.2 >>= fun cur =>
      (s'.saveStorage x.2.1 x.2.2 cur.defaultOf).map State.storage

/-- `save(st, consr(arr, size), n)`: the extent write of a push or a pop.
`lenTarget` is the `arr.length` the rule wrote, so its path already ends in
the `size` segment.  Growing is already done -- `pushAt` appended -- so it is
a no-op; shrinking truncates, and the cleared tail becomes the recycled
slots.  This is the write `SVal.saveExt` has and `SVal.save` does not. -/
def setSizeOn (pre : State) (g : List (Name × SVal)) (lenTarget : WrappedExpr)
    (n : Sym) : Res (List (Name × SVal)) :=
  Sym.eval pre n >>= fun v =>
    locPath pre lenTarget >>= fun p =>
      Upd.saveStExt { pre with storage := g } p.1 p.2 v.toSVal

/-- `save(st, consr(arr, at(ℓ)), v)` at `ℓ = size`: the slot a push appends.
`slot` is the `arr[arr.length]` or `arr.push()` the rule wrote; `deletePath`
resolves both, and the array is its path less the last segment.  `none` is the
bare push, whose slot is the one a `pop` cleared and gave back
(`Semantics.pushSlot`) -- KeY's `delAt` there, and the clear that lets a
mapping member survive into the next push. -/
def pushAtOn (pre : State) (g : List (Name × SVal)) (slot : WrappedExpr)
    (v : Option StVal) : Res (List (Name × SVal)) :=
  -- The array, not the slot: the written index is `arr.length` by
  -- construction, so it is *the extent* and never evaluated as an index --
  -- `simpleInt` would be stuck on it, and KeY does not read it either.
  let arr := match slot with
    | WrappedExpr.index _ _ base _ => base
    | WrappedExpr.pushPlace base => base
    | e => e
  let s' := { pre with storage := g }
  placePath pre arr >>= fun p => s'.findStorage p.1 p.2 >>= fun cur =>
    match cur with
    | SVal.array elems shadow =>
        (match v with
          | none => .ok (pushSlot slot.ty shadow).1
          | some y => stVal pre y) >>= fun newElem =>
          Upd.saveStExt s' p.1 (p.2 ++ [Seg.at elems.length]) newElem
    | _ => .error .stuck

/-- `storage := …`. -/
def storageRhs (t : StTerm) (s : State) : Res (List (Name × SVal)) :=
  match t with
  | .cur => .ok s.storage
  | .save u target v =>
      storageRhs u s >>= fun g => stVal s v >>= storageSaveOn s g target
  | .delAt u target =>
      storageRhs u s >>= fun g => delAtOn s g target
  | .setSize u lenTarget n =>
      storageRhs u s >>= fun g => setSizeOn s g lenTarget n
  | .pushAt u slot v =>
      storageRhs u s >>= fun g => pushAtOn s g slot v

/-- The recursion's base case writes into the state it was handed, so the
record update it introduces is the identity.  The merge tactics unfold
`storageSaveOn`, so they need this to get back to the plain writer. -/
@[simp] theorem storageSaveOn_self (s : State) (target : WrappedExpr) (v : SVal) :
    storageSaveOn s s.storage target v = storageSave s target v := rfl

/-- A write on the program variable itself is the plain write: the
recursion's base case hands back the pre-state's storage, and the target and
value were being read there anyway.  This is the shape every terminal rule's
update has, so it is what the soundness proofs unfold. -/
@[simp] theorem storageRhs_save_cur (s : State) (target : WrappedExpr) (v : StVal) :
    storageRhs (.save .cur target v) s = stVal s v >>= storageSave s target := rfl

@[simp] theorem storageRhs_delAt_cur (s : State) (target : WrappedExpr) :
    storageRhs (.delAt .cur target) s = delAtOn s s.storage target := rfl

/-- `memory := …`: the heap-and-counter pair the calculus writes as one
(`Upd.Elem.heap`), because an allocation moves both. -/
def heapRhs (t : MemTerm) (s : State) : Res (List (Nat × MObj) × Nat) :=
  (memEval s t).map fun x => (x.1.heap, x.1.nextId)

/-- `{selfBalance := selfBalance - se || net := storeSt(net, at(a), …)}`. -/
def transferRhs (recipient amount : WrappedExpr) (s : State) :
    Res (List (Int × Int) × Int) :=
  simpleInt s recipient >>= fun addr => simpleInt s amount >>= fun amt =>
    if amt < 0 then .error .stuck
    else .ok ((s.setNet addr (s.getNet addr - amt)).net, s.selfBalance - amt)

/-- The one elementary update that writes a value to a target, wherever it
lives: the semantic twin of `Rules.writeBack`. -/
def writeBackPar (target : WrappedExpr) (t : Sym) : Upd.Par :=
  match target.kind with
  | Kind.stack => [Upd.Elem.env (varName target) (bindRhs (.val t))]
  | Kind.storage => [Upd.Elem.storage (storageRhs (.save .cur target (.sym t)))]
  | Kind.memory => [Upd.Elem.heap (heapRhs (.write .cur target (.sym t)))]

/-- An elementary update as the parallel update it names.  Three constructors
expand to a *pair*, because KeY writes them as one: allocating and binding a
memory declaration or a root delete writes `memory` and the name together, and
`transfer` writes `net` and `selfBalance` together. -/
def elemPar : UpdElem -> Upd.Par
  | .bind n rhs => [Upd.Elem.env n (bindRhs rhs)]
  | .storage u => [Upd.Elem.storage (storageRhs u)]
  | .heap t => [Upd.Elem.heap (heapRhs t)]
  | .bumpOf e =>
      match e with
      | WrappedExpr.incDec op t =>
          writeBackPar t (Sym.combined op.binOp t (WrappedExpr.intLit t.ty 1))
      | _ => [Upd.Elem.env "" fun _ => .error .stuck]
  | .transfer recipient amount => [Upd.Elem.net (transferRhs recipient amount)]
  -- `havoc` has no evaluator: `CallbackSemantics.ExecC` is its meaning, and
  -- that is a relation, not a state function.
  | .havoc => [Upd.Elem.env "" fun _ => .error .stuck]

/-- A whole `\replacewith` update. -/
def UpdTerm.toPar (u : UpdTerm) : Upd.Par := List.flatMap elemPar u

/-- …as an `Upd`. -/
def UpdTerm.toUpd (u : UpdTerm) : Upd := Upd.Par.toUpd (UpdTerm.toPar u)

/-! ## Guards -/

/-- Resolve a memory place far enough to fault where the interpreter faults:
the base identity, and the index if there is one.  The bounds test itself is
the guard's formula, not this. -/
def readMemPath (s : State) : WrappedExpr -> Res (Nat × Option Int)
  | WrappedExpr.var _ _ fld => (memRef s fld.name).map fun id => (id, none)
  | WrappedExpr.field _ _ base _ => (memBase s base).map fun id => (id, none)
  | WrappedExpr.index _ _ base ix =>
      memBase s base >>= fun id => (simpleInt s ix).map fun i => (id, some i)
  | _ => .error .stuck

/-- A premise, read for its halt.  An allocating premise threads the state it
produces, so that a bounds test after a copy sees the copy's heap. -/
def Premise.run (p : Premise) (s : State) : Res State :=
  match p with
  | .read t => (Sym.eval s t).map fun _ => s
  | .resolve target =>
      match target.kind with
      | Kind.storage => (placePath s target).map fun _ => s
      | Kind.memory => (readMemPath s target).map fun _ => s
      | Kind.stack => .ok s
  | .image src => (rhsMVal s src).map Prod.fst

/-- The bounds test of the index access `e` performs, in `s`.  A mapping
receiver has no length, and no bounds goal: `true`. -/
def inBoundsOf (s : State) : WrappedExpr -> Res Bool
  | WrappedExpr.incDec _ t => inBoundsOf s t
  | WrappedExpr.index Kind.storage _ arr ix =>
      simpleInt s ix >>= fun i =>
        placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
          match cur with
          | SVal.array elems _ => .ok (decide (0 ≤ i ∧ i.toNat < elems.length))
          | SVal.map _ _ => .ok true
          | _ => .error .stuck
  | WrappedExpr.index Kind.memory _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        s.getObj id >>= fun obj =>
          match obj with
          | MObj.array elems => .ok (decide (0 ≤ i ∧ i.toNat < elems.length))
          | MObj.struct _ => .error .stuck
  | _ => .error .stuck

/-- A guard's formula. -/
def SideFormula.eval (s : State) : SideFormula -> Res Bool
  | .const b => .ok b
  | .neg φ => (SideFormula.eval s φ).map not
  | .holds c =>
      readVal s c >>= fun v =>
        match v with
        | Value.bool b => .ok b
        | Value.int _ => .error .stuck
  | .inBounds e => inBoundsOf s e
  | .nonEmpty arr =>
      placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
        match cur with
        | SVal.array elems _ => .ok (decide (0 < elems.length))
        | _ => .error .stuck
  | .nonZero e => (readVal s e >>= Value.asInt).map fun i => decide (i ≠ 0)
  | .rhsNonZero e =>
      match e with
      | WrappedExpr.binop _ l r =>
          readVal s l >>= fun _ =>
            (readVal s r >>= Value.asInt).map fun i => decide (i ≠ 0)
      | _ => .error .stuck
  | .funded amount =>
      (readVal s amount >>= Value.asInt) >>= fun v =>
        if v < 0 then .error .stuck else .ok (decide (v ≤ s.selfBalance))
  -- `cinv` is uninterpreted: the goals that carry it are never executed.
  | .cinv => .error .stuck

def runPremises : List Premise -> State -> Res State
  | [], s => .ok s
  | p :: rest, s => Premise.run p s >>= runPremises rest

/-- Read the premises in order, then decide the formula. -/
def Guard.eval (g : Guard) (s : State) : Res Bool :=
  runPremises g.premises s >>= fun s' => SideFormula.eval s' g.formula

/-! ## Executing a rule's goals -/

/-- The state a rule's goals produce, under a modality: among the goals whose
`mode` applies and whose residual still has a program, the first whose guard
holds.  A guard that halts is the halt; a rule none of whose applicable goals
continues does not continue — which is `revert`, and is exactly what the
`revert` twins and `assertSimple`'s violated branch mean. -/
def goalsExec (sm : SolidityModality) : List RuleGoal -> State -> Res State
  | [], _ => .error .revert
  | g :: rest, s =>
      if sm.appliesCaseMode g.mode = true then
        match g.residual with
        | RuleResidual.prog upd _ =>
            Guard.eval g.guard s >>= fun b =>
              if b then UpdTerm.toUpd upd s else goalsExec sm rest s
        | RuleResidual.reverting =>
            Guard.eval g.guard s >>= fun b =>
              if b then .error .revert else goalsExec sm rest s
        | RuleResidual.obligation _ _ => goalsExec sm rest s
      else goalsExec sm rest s

end Update
end Solidity
