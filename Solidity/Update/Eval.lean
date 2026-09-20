import Solidity.Update.Bridges

/-!
# Evaluating a taclet's update

`Rules.lean` writes each terminal rule's `\replacewith` as a first-order
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

/-- `arr.push(…)`: the element is read first, then appended.  `none` is
`arr.push()`, which appends the slot a `pop` gave back (`Semantics.pushSlot`),
cleared — KeY's `delAt(storage, at(n))` — or the element type's default where
the array has never been that long. -/
def pushStorage (arr : WrappedExpr) (value : Option WrappedExpr) (s : State) :
    Res (List (Name × SVal)) :=
  placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
    match cur, arr.ty with
    | SVal.array elems shadow, Ty.ref (RefTy.array elemTy) =>
        (match value with
          | none => .ok (pushSlot elemTy shadow).1
          | some rhs => rhsSVal s rhs) >>= fun newElem =>
          Upd.saveSt s p.1 p.2
            (SVal.array (elems ++ [newElem]) (pushSlot elemTy shadow).2)
    | _, _ => .error .stuck

/-- `storage := …`. -/
def storageRhs (u : StorageUpd) (s : State) : Res (List (Name × SVal)) :=
  match u with
  | .save target t => Sym.eval s t >>= fun v => storageSave s target v.toSVal
  | .copy target src => rhsSVal s src >>= fun v => storageSave s target v
  | .copyFromMem target src => rhsSVal s src >>= fun v => storageSave s target v
  | .push arr value => pushStorage arr value s
  | .pushPlace place =>
      match place with
      | WrappedExpr.pushPlace arr => pushStorage arr none s
      | _ => .error .stuck
  | .pop arr =>
      placePath s arr >>= fun p => s.findStorage p.1 p.2 >>= fun cur =>
        match cur with
        | SVal.array elems shadow =>
            match elems.reverse with
            | [] => .error .revert
            | last :: restRev =>
                Upd.saveSt s p.1 p.2
                  (SVal.array restRev.reverse (last.defaultOf :: shadow))
        | _ => .error .stuck
  | .clear target =>
      deletePath s target >>= fun x =>
        x.1.findStorage x.2.1 x.2.2 >>= fun cur =>
          (x.1.saveStorage x.2.1 x.2.2 cur.defaultOf).map State.storage

/-- `memory := …`: the heap-and-counter pair the calculus writes as one
(`Upd.Elem.heap`), because an allocation moves both. -/
def heapRhs (t : MemTerm) (s : State) : Res (List (Nat × MObj) × Nat) :=
  (memEval s t).map fun x => (x.1.heap, x.1.nextId)

/-- `delete m.f` / `delete m[se]` (and the heap half of a root delete). -/
def memDeleteHeap (target : WrappedExpr) (s : State) :
    Res (List (Nat × MObj) × Nat) :=
  match target with
  | WrappedExpr.var _ ty _ =>
      match ty with
      | Ty.ref ref => (allocDefault s ref).map fun x => (x.1.heap, x.1.nextId)
      | _ => .error .stuck
  | e@(WrappedExpr.field _ _ base f) =>
      memBase s base >>= fun id =>
        match e.ty with
        | Ty.bool => Upd.heapOf (writeMemField s id f.name (MVal.bool false))
        | Ty.uint => Upd.heapOf (writeMemField s id f.name (MVal.int 0))
        | Ty.int => Upd.heapOf (writeMemField s id f.name (MVal.int 0))
        | Ty.ref ref =>
            allocDefault s ref >>= fun x =>
              Upd.heapOf (writeMemField x.1 id f.name (MVal.ref x.2))
  | e@(WrappedExpr.index _ _ base ix) =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        match e.ty with
        | Ty.bool => Upd.heapOf (writeMemIndex s id i (MVal.bool false))
        | Ty.uint => Upd.heapOf (writeMemIndex s id i (MVal.int 0))
        | Ty.int => Upd.heapOf (writeMemIndex s id i (MVal.int 0))
        | Ty.ref ref =>
            allocDefault s ref >>= fun x =>
              Upd.heapOf (writeMemIndex x.1 id i (MVal.ref x.2))
  | _ => .error .stuck

/-- …and the rebinding half, for a memory *root* target only. -/
def memDeleteBind (target : WrappedExpr) (s : State) : Res Binding :=
  match target with
  | WrappedExpr.var _ ty _ =>
      match ty with
      | Ty.ref ref => (allocDefault s ref).map fun x => Binding.mref x.2
      | _ => .error .stuck
  | _ => .error .stuck

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
  | Kind.storage => [Upd.Elem.storage (storageRhs (.save target t))]
  | Kind.memory => [Upd.Elem.heap (heapRhs (.write .cur target (.sym t)))]

/-- An elementary update as the parallel update it names.  Three constructors
expand to a *pair*, because KeY writes them as one: allocating and binding a
memory declaration or a root delete writes `memory` and the name together, and
`transfer` writes `net` and `selfBalance` together. -/
def elemPar : UpdElem -> Upd.Par
  | .bind n rhs => [Upd.Elem.env n (bindRhs rhs)]
  | .storage u => [Upd.Elem.storage (storageRhs u)]
  | .heap t => [Upd.Elem.heap (heapRhs t)]
  | .memDelete target =>
      match target with
      | WrappedExpr.var _ _ fld =>
          [Upd.Elem.heap (memDeleteHeap target),
            Upd.Elem.env fld.name (memDeleteBind target)]
      | _ => [Upd.Elem.heap (memDeleteHeap target)]
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
