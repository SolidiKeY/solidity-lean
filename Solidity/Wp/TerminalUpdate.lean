import Solidity.Semantics
import Solidity.Rules

/-!
# The state update of each terminal rule

A *terminal* rule of the calculus has an empty residual: it does not rewrite the
program, it *changes the state* — KeY's `\replacewith` installs an update
(`x := selectSt(storage, p)`, `storage := save(storage, p, v)`, …).  This
module writes that update down, one function per rule family, in the
interpreter's own state vocabulary (`findStorage`/`saveStorage`/`setEnv`/
`alloc`/`setNet`/`copyStToM`/…) but **never** through the interpreter's
evaluators (`execStmt`, `execAssign`, `evalValue`, `resolveS`,
`resolveLoc`, `readM`, `rhsToSVal`, `readLoc`, `writeLoc` do not occur
here, with one documented exception, `storagePlaceAliasUpd`).  The bridge
theorems in `Wp/Terminal/` then prove, *under each rule's guard*,

    execStmt s stmt = terminalUpdate r stmt s

— which is what makes the update a theorem about the rule and not a
restatement of the interpreter.

Design facts the definitions mirror exactly (they have to, for the
equation to be unconditional):

* a *simple* expression is a variable, a `bool` literal or an `int`
  literal (`WrappedExpr.simple`), so every terminal place is `p`, `p.f` or
  `p[se]` and the vocabulary is first-order;
* the interpreter evaluates an assignment's right-hand side **before**
  resolving its target (solc order), and every update binds in that
  order — otherwise the two sides could disagree on which of two faults
  wins;
* a storage variable resolves *env first* (a `Binding.spath` alias),
  then by its `global` origin (`varPath`, as `resolveS`), whereas an
  assignment/compound target that is a storage *root* resolves by origin
  only (`locPath`, as `resolveLoc`); both readers are carried;
* `isStack lhs` admits non-variable stack places, on which the
  interpreter is stuck before it reads the right-hand side
  (`execAssignNested`); `assignStack` has the same `stuck` arm.

`Res State` carries the KeY case splits: an out-of-bounds index reverts
(`SVal.find`/`SVal.save`), a zero divisor reverts (`applyBinOp`),
overflow reverts (`checkArith`), an uncovered `transfer` reverts, and an
ill-typed state is `stuck` at the same point the interpreter is.
-/

namespace Solidity
namespace Wp

open Semantics

/-! ## Readers -/

/-- The value bound to a stack variable. -/
def stackVal (s : State) (n : Name) : Res Value :=
  match lookupBy n s.env with
  | some (Binding.val v) => .ok v
  | _ => .error .stuck

/-- The identity bound to a memory variable. -/
def memRef (s : State) (n : Name) : Res Nat :=
  match lookupBy n s.env with
  | some (Binding.mref id) => .ok id
  | _ => .error .stuck

/-- The storage path a storage variable denotes: env first (a local
`Binding.spath` alias), then the global root — `resolveS`'s order. -/
def varPath (s : State) (fld : Field) : Res (Name × List Seg) :=
  match lookupBy fld.name s.env with
  | some (Binding.spath root segs) => .ok (root, segs)
  | some _ => .error .stuck
  | none =>
      if fld.origin = some StorageOrigin.global then .ok (fld.name, [])
      else .error .stuck

/-- The value of a simple expression: a literal, a stack variable, or a
storage variable read through its path. -/
def simpleVal (s : State) : WrappedExpr -> Res Value
  | WrappedExpr.bool b => .ok (Value.bool b)
  | WrappedExpr.intLit _ v => .ok (Value.int v)
  | WrappedExpr.var Kind.stack _ fld => stackVal s fld.name
  | WrappedExpr.var Kind.storage _ fld =>
      varPath s fld >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue
  | _ => .error .stuck

def simpleInt (s : State) (e : WrappedExpr) : Res Int :=
  simpleVal s e >>= Value.asInt

/-- The path of a storage place: the root through `varPath` (env-first, as
`resolveS`), then one segment per `.f` / `[se]` step.

**Recursive in the base**, so a *deep* path (`alice.account.balance`) has a
value and not just the one-level shapes a terminal rule's guard admits.  On
those shapes -- `simplePathB`, `Wp/Terminal/Vocab.lean` -- the unfolding is
unchanged, which is why every `_update` and bridge theorem keeps its
statement.  What the recursion buys is the *merged* update of a derivation:
the calculus writes `{storage := save(storage, alice·account·balance, 10)}`
after composing `{sp := alice·account}` into the write, and a reader stuck on
that path would make the merged line the always-stuck update rather than the
composite it claims to be (`Update/Step.lean`). -/
def placePath (s : State) : WrappedExpr -> Res (Name × List Seg)
  | WrappedExpr.var _ _ fld => varPath s fld
  | WrappedExpr.field _ _ base f =>
      placePath s base >>= fun p => .ok (p.1, p.2 ++ [Seg.field f.name])
  | WrappedExpr.index _ _ base ix =>
      placePath s base >>= fun p =>
        simpleInt s ix >>= fun i => .ok (p.1, p.2 ++ [Seg.at i])
  | _ => .error .stuck

/-- The path of a storage *l-value* as `resolveLoc` addresses it: a root
resolves by origin only (a non-global root is an alias binding, on which
reads and writes are stuck); nested places go through `placePath`. -/
def locPath (s : State) : WrappedExpr -> Res (Name × List Seg)
  | WrappedExpr.var Kind.storage _ fld =>
      if fld.origin = some StorageOrigin.global then .ok (fld.name, [])
      else .error .stuck
  | e => placePath s e

/-- The identity a simple memory base denotes (`resolveMBase` on a simple
expression: a memory variable; a literal is stuck). -/
def memBase (s : State) : WrappedExpr -> Res Nat
  | WrappedExpr.var _ _ m => memRef s m.name
  | _ => .error .stuck

/-- The slot read of a simple memory place `m`, `m.f`, `m[se]`
(`readM`). -/
def readMem (s : State) : WrappedExpr -> Res MVal
  | WrappedExpr.var _ _ fld => (memRef s fld.name).map MVal.ref
  | WrappedExpr.field _ _ base f =>
      memBase s base >>= fun id => s.getObj id >>= fun obj =>
        match obj with
        | MObj.struct fields =>
            match lookupBy f.name fields with
            | some v => .ok v
            | none => .error .stuck
        | _ => .error .stuck
  | WrappedExpr.index _ _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        s.getObj id >>= fun obj =>
          match obj with
          | MObj.array elems =>
              if h : 0 ≤ i ∧ i.toNat < elems.length then
                .ok (elems.get ⟨i.toNat, h.2⟩)
              else .error .revert
          | _ => .error .stuck
  | _ => .error .stuck

/-- The value of a terminal-rule operand: a simple expression, or a
simple-path storage/memory place read through `find`/`read`.  Pure by
construction (no state result). -/
def readVal (s : State) : WrappedExpr -> Res Value
  | WrappedExpr.bool b => .ok (Value.bool b)
  | WrappedExpr.intLit _ v => .ok (Value.int v)
  | WrappedExpr.var Kind.stack _ fld => stackVal s fld.name
  | e@(WrappedExpr.var Kind.storage _ _) =>
      placePath s e >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue
  | e@(WrappedExpr.field Kind.storage _ _ _) =>
      placePath s e >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue
  | e@(WrappedExpr.index Kind.storage _ _ _) =>
      placePath s e >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue
  | e@(WrappedExpr.field Kind.memory _ _ _) => readMem s e >>= MVal.asValue
  | e@(WrappedExpr.index Kind.memory _ _ _) => readMem s e >>= MVal.asValue
  | _ => .error .stuck

def readInt (s : State) (e : WrappedExpr) : Res Int :=
  readVal s e >>= Value.asInt

/-- The storage image of a terminal right-hand side (`rhsToSVal`):
`store` for a primitive, `select` for a mapping-free storage source,
`copyMem` for a memory source. -/
def rhsSVal (s : State) (rhs : WrappedExpr) : Res SVal :=
  if rhs.ty.isPrimitive then (readVal s rhs).map Value.toSVal
  else
    match rhs.kind with
    | Kind.storage =>
        if tyHasMapping rhs.ty then .error .stuck
        else placePath s rhs >>= fun p => s.findStorage p.1 p.2
    | Kind.memory => readMem s rhs >>= fun mv => copyMem s mv
    | Kind.stack => .error .stuck

/-- The memory image of a terminal right-hand side (`rhsToMVal`); a
storage source deep-copies and therefore allocates. -/
def rhsMVal (s : State) (rhs : WrappedExpr) : Res (State × MVal) :=
  if rhs.ty.isPrimitive then (readVal s rhs).map fun v => (s, v.toMVal)
  else
    match rhs.kind with
    | Kind.memory => (readMem s rhs).map fun mv => (s, mv)
    | Kind.storage =>
        placePath s rhs >>= fun p =>
          s.findStorage p.1 p.2 >>= fun sv => copyStToM s sv
    | Kind.stack => .error .stuck

/-- The primitive value in a memory struct slot, at an already-resolved
identity: KeY `read(mem, mv, f)` as a *value*.  Separate from `readMem`
because the arithmetic rules resolve the base once and then read and write
through it, exactly as the interpreter resolves an l-value once. -/
def memFieldVal (s : State) (id : Nat) (f : Name) : Res Value :=
  s.getObj id >>= fun obj =>
    match obj with
    | MObj.struct fields =>
        match lookupBy f fields with
        | some v => v.asValue
        | none => .error .stuck
    | MObj.array _ => .error .stuck

/-- The primitive value in a memory array slot (out of bounds reverts):
`read(mem, mv, at(i))`. -/
def memIndexVal (s : State) (id : Nat) (i : Int) : Res Value :=
  s.getObj id >>= fun obj =>
    match obj with
    | MObj.array elems =>
        if h : 0 ≤ i ∧ i.toNat < elems.length then
          (elems.get ⟨i.toNat, h.2⟩).asValue
        else .error .revert
    | MObj.struct _ => .error .stuck

/-- Write a memory struct member. -/
def writeMemField (s : State) (id : Nat) (f : Name) (mv : MVal) : Res State :=
  s.getObj id >>= fun obj =>
    match obj with
    | MObj.struct fields => .ok (s.setObj id (MObj.struct (setBy f mv fields)))
    | MObj.array _ => .error .stuck

/-- Write a memory array slot (out of bounds reverts). -/
def writeMemIndex (s : State) (id : Nat) (i : Int) (mv : MVal) : Res State :=
  s.getObj id >>= fun obj =>
    match obj with
    | MObj.array elems =>
        if 0 ≤ i ∧ i.toNat < elems.length then
          .ok (s.setObj id (MObj.array (elems.set i.toNat mv)))
        else .error .revert
    | MObj.struct _ => .error .stuck

/-- The path a push place `arr.push()` denotes: extend the array by the
recycled slot *now* (this is a state change) and address the new last slot
(`resolveS`'s `pushPlace` arm). -/
def pushPath (s : State) (target : WrappedExpr) :
    Res (State × Name × List Seg) :=
  placePath s target >>= fun p =>
    s.findStorage p.1 p.2 >>= fun arr =>
      match arr, target.ty with
      | SVal.array elems shadow, Ty.ref (RefTy.array elemTy) =>
          s.saveStorage p.1 p.2
              (SVal.array (elems ++ [(pushSlot elemTy shadow).1])
                (pushSlot elemTy shadow).2)
            >>= fun s' => .ok (s', p.1, p.2 ++ [Seg.at elems.length])
      | _, _ => .error .stuck

/-- The path of a simple `delete` target: a simple place, or a push place. -/
def deletePath (s : State) : WrappedExpr -> Res (State × Name × List Seg)
  | WrappedExpr.pushPlace t => pushPath s t
  | e => (placePath s e).map fun p => (s, p)

/-- The default a value-typed declaration binds. -/
def defaultValue : Ty -> Value
  | Ty.bool => Value.bool false
  | _ => Value.int 0

/-! ## Operators -/

/-- `se1 op se2` with the short-circuit and checked-arithmetic gates
(KeY `<op>Assignment` plus `applyBinOp`'s zero-divisor revert and
`checkArith`'s overflow revert). -/
def binopVal (op : BinOp) (l r : WrappedExpr) (s : State) : Res Value :=
  readVal s l >>= fun lv =>
    match op, lv with
    | BinOp.and, Value.bool false => .ok (Value.bool false)
    | BinOp.or, Value.bool true => .ok (Value.bool true)
    | _, _ =>
        readVal s r >>= fun rv =>
          applyBinOp op lv rv >>= checkArith (op.retTy l.ty)

def unopVal (op : UnOp) (arg : WrappedExpr) (s : State) : Res Value :=
  readVal s arg >>= fun v => applyUnOp op v >>= fun w =>
    match op, arg.ty with
    | UnOp.neg, Ty.int => checkArith Ty.int w
    | _, _ => .ok w

/-- `++t` / `t--` on a stack variable, a global storage root, or a simple
storage place: read once, `checkArith` at the target's type, write once;
returns the expression's value (pre or post). -/
def incDecUpd (op : IncDec) (target : WrappedExpr) (s : State) :
    Res (State × Value) :=
  let bump (old : Value) : Res Value :=
    old.asInt >>= fun n =>
      checkArith target.ty
        (Value.int (if op.isIncrement then n + 1 else n - 1))
  match target with
  | WrappedExpr.var Kind.stack _ fld =>
      stackVal s fld.name >>= fun old => bump old >>= fun nv =>
        .ok (s.setEnv fld.name (Binding.val nv), if op.isPre then nv else old)
  | e@(WrappedExpr.var Kind.storage _ _) =>
      locPath s e >>= fun p =>
        s.findStorage p.1 p.2 >>= SVal.asValue >>= fun old =>
          bump old >>= fun nv =>
            s.saveStorage p.1 p.2 nv.toSVal >>= fun s' =>
              .ok (s', if op.isPre then nv else old)
  | e@(WrappedExpr.field Kind.storage _ _ _) =>
      locPath s e >>= fun p =>
        s.findStorage p.1 p.2 >>= SVal.asValue >>= fun old =>
          bump old >>= fun nv =>
            s.saveStorage p.1 p.2 nv.toSVal >>= fun s' =>
              .ok (s', if op.isPre then nv else old)
  | e@(WrappedExpr.index Kind.storage _ _ _) =>
      locPath s e >>= fun p =>
        s.findStorage p.1 p.2 >>= SVal.asValue >>= fun old =>
          bump old >>= fun nv =>
            s.saveStorage p.1 p.2 nv.toSVal >>= fun s' =>
              .ok (s', if op.isPre then nv else old)
  -- The memory twins: `read(mem, mv, f)` / `read(mem, mv, at(i))` in place
  -- of `find(storage, ...)`, `write` in place of `save` (the calculus's
  -- `memoryFieldIncrement`).  The base identity is resolved twice, once for
  -- the read and once for the write; under the rules' guards the base and
  -- the index are simple, so both resolutions are the same pure lookup.
  | WrappedExpr.field Kind.memory _ base f =>
      memBase s base >>= fun id =>
        memFieldVal s id f.name >>= fun old =>
          bump old >>= fun nv =>
            writeMemField s id f.name nv.toMVal >>= fun s' =>
              .ok (s', if op.isPre then nv else old)
  | WrappedExpr.index Kind.memory _ base ix =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        memIndexVal s id i >>= fun old =>
          bump old >>= fun nv =>
            writeMemIndex s id i nv.toMVal >>= fun s' =>
              .ok (s', if op.isPre then nv else old)
  | _ => .error .stuck

/-! ## Per-shape updates -/

/-- Bind a stack variable to the value a computation produces.  Any
other stack-kind place is stuck *before* the right-hand side is touched
(`execAssignNested`). -/
def assignStack (lhs : PlaceExpr) (rv : State -> Res (State × Value))
    (s : State) : Res State :=
  match lhs.expr with
  | WrappedExpr.var Kind.stack _ fld =>
      rv s >>= fun sv => .ok (sv.1.setEnv fld.name (Binding.val sv.2))
  | _ => .error .stuck

/-- `x = se`, `x = p.f`, `x = p[se]`, `x = m.f`, …: a pure read, then a
stack bind (KeY `x := selectSt(…)` / `x := read(…)`). -/
def assignStackRead (lhs : PlaceExpr) (rhs : WrappedExpr) :
    State -> Res State :=
  assignStack lhs fun s => (readVal s rhs).map fun v => (s, v)

/-- Every storage-target assignment among the terminal rules.  Right-hand
side first, then the target path; a global root is written
(`storage := save(storage, root, v)`), a local root is *re-bound* to the
right-hand side's path, a nested place is written at its path. -/
def storageAssignUpd (lhs : PlaceExpr) (rhs : WrappedExpr) (s : State) :
    Res State :=
  match lhs.expr with
  | WrappedExpr.var Kind.storage _ fld =>
      if fld.origin = some StorageOrigin.global then
        rhsSVal s rhs >>= fun sv => s.saveStorage fld.name [] sv
      else
        placePath s rhs >>= fun p =>
          .ok (s.setEnv fld.name (Binding.spath p.1 p.2))
  | e@(WrappedExpr.field Kind.storage _ _ _) =>
      rhsSVal s rhs >>= fun sv =>
        placePath s e >>= fun p => s.saveStorage p.1 p.2 sv
  | e@(WrappedExpr.index Kind.storage _ _ _) =>
      rhsSVal s rhs >>= fun sv =>
        placePath s e >>= fun p => s.saveStorage p.1 p.2 sv
  | _ => .error .stuck

/-- `x = se1 op se2`. -/
def binopAssignUpd (op : BinOp) (lhs : PlaceExpr) (rhs : WrappedExpr) :
    State -> Res State :=
  match rhs with
  | WrappedExpr.binop _ l r =>
      assignStack lhs fun s => (binopVal op l r s).map fun v => (s, v)
  | _ => fun _ => .error .stuck

/-- `x = op se`. -/
def unopAssignUpd (op : UnOp) (lhs : PlaceExpr) (rhs : WrappedExpr) :
    State -> Res State :=
  match rhs with
  | WrappedExpr.unop _ a =>
      assignStack lhs fun s => (unopVal op a s).map fun v => (s, v)
  | _ => fun _ => .error .stuck

/-- `x = ++t` / `x = t--`. -/
def incDecAssignUpd (op : IncDec) (lhs : PlaceExpr) (rhs : WrappedExpr) :
    State -> Res State :=
  match rhs with
  | WrappedExpr.incDec _ t => assignStack lhs (incDecUpd op t)
  | _ => fun _ => .error .stuck

/-- `t op= se` on a stack variable, a global root, or a simple storage
place: right-hand side first, one resolution of the target, `checkArith`
at the target's type. -/
def compoundAssignUpd (op : BinOp) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (s : State) : Res State :=
  readVal s rhs >>= fun v =>
    match lhs.expr with
    | WrappedExpr.var Kind.stack _ fld =>
        stackVal s fld.name >>= fun old =>
          applyBinOp op old v >>= checkArith lhs.expr.ty >>= fun nv =>
            .ok (s.setEnv fld.name (Binding.val nv))
    | e@(WrappedExpr.var Kind.storage _ _) =>
        locPath s e >>= fun p =>
          s.findStorage p.1 p.2 >>= SVal.asValue >>= fun old =>
            applyBinOp op old v >>= checkArith lhs.expr.ty >>= fun nv =>
              s.saveStorage p.1 p.2 nv.toSVal
    | e@(WrappedExpr.field Kind.storage _ _ _) =>
        locPath s e >>= fun p =>
          s.findStorage p.1 p.2 >>= SVal.asValue >>= fun old =>
            applyBinOp op old v >>= checkArith lhs.expr.ty >>= fun nv =>
              s.saveStorage p.1 p.2 nv.toSVal
    | e@(WrappedExpr.index Kind.storage _ _ _) =>
        locPath s e >>= fun p =>
          s.findStorage p.1 p.2 >>= SVal.asValue >>= fun old =>
            applyBinOp op old v >>= checkArith lhs.expr.ty >>= fun nv =>
              s.saveStorage p.1 p.2 nv.toSVal
    -- The memory twins (the calculus's `memoryFieldOpAssign`,
    -- `memoryFieldDivAssign`, `memoryIndexArrayOpAssign`): heap read and
    -- write in place of `find`/`save`.  There is no memory *root* arm — a
    -- memory root is an identity, not a value cell.
    | WrappedExpr.field Kind.memory _ base f =>
        memBase s base >>= fun id =>
          memFieldVal s id f.name >>= fun old =>
            applyBinOp op old v >>= checkArith lhs.expr.ty >>= fun nv =>
              writeMemField s id f.name nv.toMVal
    | WrappedExpr.index Kind.memory _ base ix =>
        memBase s base >>= fun id => simpleInt s ix >>= fun i =>
          memIndexVal s id i >>= fun old =>
            applyBinOp op old v >>= checkArith lhs.expr.ty >>= fun nv =>
              writeMemIndex s id i nv.toMVal
    | _ => .error .stuck

/-- `++t;` as a statement: the value is discarded. -/
def incDecStmtUpd (op : IncDec) (e : WrappedExpr) (s : State) : Res State :=
  match e with
  | WrappedExpr.incDec _ t => (incDecUpd op t s).map Prod.fst
  | _ => .error .stuck

/-- `T x;` for a value type: bind the type's default. -/
def stackDeclSkipUpd (ty : Ty) (name : Name) (s : State) : Res State :=
  .ok (s.setEnv name (Binding.val (defaultValue ty)))

/-- `T storage p;` without initializer: no effect. -/
def storageDeclSkipUpd (_ : Ty) (_ : Name) (s : State) : Res State :=
  .ok s

/-- The scratch storage alias `sp` bound by the unfold rules.  **The one
arm that keeps an interpreter function**: `captureStoragePath` may hoist
an *impure* path (`people[f()]`), whose resolution runs the interpreter;
on a pure path this is `placePath` (`storagePlaceAliasUpd_pure`). -/
def storagePlaceAliasUpd (name : Name) (init : WrappedExpr) (s : State) :
    Res State :=
  resolveS s init >>= fun x => .ok (x.1.setEnv name (Binding.spath x.2.1 x.2.2))

/-- `T memory m;` (fresh default allocation) and `T memory m = rhs;`
(alias a memory source, deep-copy a storage source). -/
def memoryDeclUpd (ty : Ty) (name : Name) (init : Option WrappedExpr)
    (s : State) : Res State :=
  match init with
  | none =>
      match ty with
      | Ty.ref ref =>
          allocDefault s ref >>= fun x =>
            .ok (x.1.setEnv name (Binding.mref x.2))
      | _ => .error .stuck
  | some rhs =>
      match rhs.kind with
      | Kind.memory =>
          readMem s rhs >>= fun mv =>
            match mv with
            | MVal.ref id => .ok (s.setEnv name (Binding.mref id))
            | _ => .error .stuck
      | Kind.storage =>
          placePath s rhs >>= fun p =>
            s.findStorage p.1 p.2 >>= fun sv =>
              copyStToM s sv >>= fun x =>
                match x.2 with
                | MVal.ref id => .ok (x.1.setEnv name (Binding.mref id))
                | _ => .error .stuck
      | Kind.stack => .error .stuck

/-- `delete p` on a simple storage place (or a push place): write the
current value's default (`SVal.defaultOf`) at its path. -/
def storageDeleteUpd (target : PlaceExpr) (s : State) : Res State :=
  deletePath s target.expr >>= fun x =>
    x.1.findStorage x.2.1 x.2.2 >>= fun cur =>
      x.1.saveStorage x.2.1 x.2.2 cur.defaultOf

/-- `delete m` (fresh default identity) / `delete m.f` / `delete m[se]`
(the slot's default, allocating for a reference type). -/
def memoryDeleteUpd (target : PlaceExpr) (s : State) : Res State :=
  match target.expr with
  | WrappedExpr.var _ ty fld =>
      match ty with
      | Ty.ref ref =>
          allocDefault s ref >>= fun x =>
            .ok (x.1.setEnv fld.name (Binding.mref x.2))
      | _ => .error .stuck
  | e@(WrappedExpr.field _ _ base f) =>
      memBase s base >>= fun id =>
        match e.ty with
        | Ty.bool => writeMemField s id f.name (MVal.bool false)
        | Ty.uint => writeMemField s id f.name (MVal.int 0)
        | Ty.int => writeMemField s id f.name (MVal.int 0)
        | Ty.ref ref =>
            allocDefault s ref >>= fun x =>
              writeMemField x.1 id f.name (MVal.ref x.2)
  | e@(WrappedExpr.index _ _ base ix) =>
      memBase s base >>= fun id => simpleInt s ix >>= fun i =>
        match e.ty with
        | Ty.bool => writeMemIndex s id i (MVal.bool false)
        | Ty.uint => writeMemIndex s id i (MVal.int 0)
        | Ty.int => writeMemIndex s id i (MVal.int 0)
        | Ty.ref ref =>
            allocDefault s ref >>= fun x =>
              writeMemIndex x.1 id i (MVal.ref x.2)
  | _ => .error .stuck

/-- `arr.push()` / `arr.push(se)`: extend the array by the recycled slot or
by the right-hand side's storage image. -/
def pushUpd (target : PlaceExpr) (value : Option WrappedExpr) (s : State) :
    Res State :=
  placePath s target.expr >>= fun p =>
    s.findStorage p.1 p.2 >>= fun arr =>
      match arr, target.expr.ty with
      | SVal.array elems shadow, Ty.ref (RefTy.array elemTy) =>
          (match value with
            | none => .ok (pushSlot elemTy shadow).1
            | some rhs => rhsSVal s rhs) >>= fun newElem =>
            s.saveStorage p.1 p.2
              (SVal.array (elems ++ [newElem]) (pushSlot elemTy shadow).2)
      | _, _ => .error .stuck

/-- `arr.pop()`: clear the last slot and give it back, then shorten; an
empty array reverts. -/
def popUpd (target : PlaceExpr) (s : State) : Res State :=
  placePath s target.expr >>= fun p =>
    s.findStorage p.1 p.2 >>= fun arr =>
      match arr with
      | SVal.array elems shadow =>
          match elems.reverse with
          | [] => .error .revert
          | last :: restRev =>
              s.saveStorage p.1 p.2
                (SVal.array restRev.reverse (last.defaultOf :: shadow))
      | _ => .error .stuck

/-- `p = arr.push()` for a storage-local root `p`: extend the array with
the element type's default and bind `p` to the new slot's path. -/
def pushBindUpd (lhs : PlaceExpr) (rhs : WrappedExpr) (s : State) :
    Res State :=
  match lhs.expr, rhs with
  | WrappedExpr.var Kind.storage _ fld, WrappedExpr.pushPlace target =>
      pushPath s target >>= fun x =>
        .ok (x.1.setEnv fld.name (Binding.spath x.2.1 x.2.2))
  | _, _ => .error .stuck

/-- Every memory-target assignment among the terminal rules: a memory
root aliases a memory source or deep-copies a storage source; a nested
place takes the right-hand side's memory image (right-hand side first,
which may allocate), then writes the slot. -/
def memoryAssignUpd (lhs : PlaceExpr) (rhs : WrappedExpr) (s : State) :
    Res State :=
  match lhs.expr with
  | WrappedExpr.var Kind.memory _ fld =>
      match rhs.kind with
      | Kind.memory =>
          readMem s rhs >>= fun mv =>
            match mv with
            | MVal.ref id => .ok (s.setEnv fld.name (Binding.mref id))
            | _ => .error .stuck
      | Kind.storage =>
          placePath s rhs >>= fun p =>
            s.findStorage p.1 p.2 >>= fun sv =>
              copyStToM s sv >>= fun x =>
                match x.2 with
                | MVal.ref id => .ok (x.1.setEnv fld.name (Binding.mref id))
                | _ => .error .stuck
      | Kind.stack => .error .stuck
  | WrappedExpr.field Kind.memory _ base f =>
      rhsMVal s rhs >>= fun x =>
        memBase x.1 base >>= fun id => writeMemField x.1 id f.name x.2
  | WrappedExpr.index Kind.memory _ base ix =>
      rhsMVal s rhs >>= fun x =>
        memBase x.1 base >>= fun id =>
          simpleInt x.1 ix >>= fun i => writeMemIndex x.1 id i x.2
  | _ => .error .stuck

/-- `a.transfer(v)`: a negative amount is stuck, an uncovered amount
reverts, otherwise debit the balance and the ledger. -/
def transferUpd (recipient amount : WrappedExpr) (s : State) : Res State :=
  simpleInt s recipient >>= fun addr => simpleInt s amount >>= fun amt =>
    if amt < 0 then .error .stuck
    else if s.selfBalance < amt then .error .revert
    else .ok { s.setNet addr (s.getNet addr - amt) with
               selfBalance := s.selfBalance - amt }

/-- `assert(se)` / `require(se)`: continue on `true`, revert on `false`. -/
def assertUpd (c : WrappedExpr) (s : State) : Res State :=
  readVal s c >>= fun v =>
    match v with
    | Value.bool true => .ok s
    | Value.bool false => .error .revert
    | _ => .error .stuck

def revertUpd (_ : Option WrappedExpr) (_ : State) : Res State :=
  .error .revert

/-! ## Lifting a per-shape update to a statement update

The wrong statement shape is stuck; the bridge theorems are only ever
applied under the rule's guard, which fixes the shape. -/

def onAssign (f : PlaceExpr -> WrappedExpr -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.assign lhs rhs, s => f lhs rhs s
  | _, _ => .error .stuck

def onCompound (f : PlaceExpr -> WrappedExpr -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.compoundAssign _ lhs rhs, s => f lhs rhs s
  | _, _ => .error .stuck

def onExpr (f : WrappedExpr -> State -> Res State) : Stmt -> State -> Res State
  | Stmt.expr e, s => f e s
  | _, _ => .error .stuck

def onStackDecl (f : Ty -> Name -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.stackDecl ty name none, s => f ty name s
  | _, _ => .error .stuck

def onStorageDecl (f : Ty -> Name -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.storageDecl ty name none, s => f ty name s
  | _, _ => .error .stuck

def onAlias (f : Name -> WrappedExpr -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.storagePlaceAlias _ name init, s => f name init s
  | _, _ => .error .stuck

def onMemoryDecl (f : Ty -> Name -> Option WrappedExpr -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.memoryDecl ty name init, s => f ty name init s
  | _, _ => .error .stuck

def onDelete (f : PlaceExpr -> State -> Res State) : Stmt -> State -> Res State
  | Stmt.delete target, s => f target s
  | _, _ => .error .stuck

def onPush (f : PlaceExpr -> Option WrappedExpr -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.push target value, s => f target value s
  | _, _ => .error .stuck

def onPop (f : PlaceExpr -> State -> Res State) : Stmt -> State -> Res State
  | Stmt.pop target, s => f target s
  | _, _ => .error .stuck

def onAssert (f : WrappedExpr -> State -> Res State) : Stmt -> State -> Res State
  | Stmt.assertStmt c, s => f c s
  | _, _ => .error .stuck

def onRequire (f : WrappedExpr -> State -> Res State) : Stmt -> State -> Res State
  | Stmt.requireStmt c, s => f c s
  | _, _ => .error .stuck

def onTransfer (f : WrappedExpr -> WrappedExpr -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.transfer r a, s => f r a s
  | _, _ => .error .stuck

def onRevert (f : Option WrappedExpr -> State -> Res State) :
    Stmt -> State -> Res State
  | Stmt.revert msg, s => f msg s
  | _, _ => .error .stuck

/-! ## The table -/

/-- The terminal table: `some` exactly for the terminal rules of the calculus (empty
residual), `none` for every unfold/capture rule and for
`transferWithCallback` (an alternative-list rule whose meaning is
`CallbackSemantics.ExecC`, not a state update).  Many rules share one
function — that *is* the content: KeY splits one update by static type
and modality (array vs mapping index, box vs diamond, store vs
copy-source), the interpreter dispatches on the runtime node and `Res`
carries the split. -/
def terminalUpdate? : RuleName -> Option (Stmt -> State -> Res State)
  -- storage reads to a stack variable / memory reads to a stack variable
  | .storageRootReadSelect | .storageFieldReadFind
  | .storageIndexReadArrayFindBox | .storageIndexReadArrayFindDiamond
  | .storageIndexReadMappingFind
  | .memoryFieldReadHeap | .memoryIndexReadHeapBox | .memoryIndexReadHeapDiamond
  | .localValueAssign => some (onAssign assignStackRead)
  -- storage reads to a local root (rebind) / to a global root / storage writes
  | .storageFieldReadBindLocalRoot | .storageIndexReadArrayBindLocalRootBox
  | .storageIndexReadArrayBindLocalRootDiamond | .storageIndexReadMappingBindLocalRoot
  | .storageLocalRootRebind
  | .storageFieldReadStoreRoot | .storageIndexReadArrayStoreRootBox
  | .storageIndexReadArrayStoreRootDiamond | .storageIndexReadMappingStoreRoot
  | .storageRootWriteStore | .storageRootWriteCopySource
  | .memoryToStorageStoreRoot
  | .storageFieldWriteSave | .storageFieldWriteCopySource
  | .memoryToStorageFieldCopyRoot
  | .storageIndexWriteArraySaveBox | .storageIndexWriteArraySaveDiamond
  | .storageIndexWriteMappingSave
  | .storageIndexWriteArrayCopySourceBox | .storageIndexWriteArrayCopySourceDiamond
  | .storageIndexWriteMappingCopySource
  | .memoryToStorageIndexMappingCopyRoot
  | .memoryToStorageIndexArrayCopyRootBox
  | .memoryToStorageIndexArrayCopyRootDiamond =>
      some (onAssign storageAssignUpd)
  -- stack value rules
  | .binopAssignment op => some (onAssign (binopAssignUpd op))
  | .unopAssignment op => some (onAssign (unopAssignUpd op))
  | .localAssignIncDec op | .storageRootIncDecAssignment op
  | .storageFieldIncDecAssignment op | .storageIndexIncDecAssignment op
  | .memoryFieldIncDecAssignment op | .memoryIndexIncDecAssignment op =>
      some (onAssign (incDecAssignUpd op))
  -- compound assignment and inc/dec statements
  | .localCompoundAssign op | .storageRootCompoundAssign op
  | .storageFieldCompoundAssign op | .storageIndexCompoundAssign op
  | .memoryFieldCompoundAssign op | .memoryIndexCompoundAssign op =>
      some (onCompound (compoundAssignUpd op))
  | .localIncDec op | .storageRootIncDec op | .storageFieldIncDec op
  | .storageIndexIncDec op | .memoryFieldIncDec op
  | .memoryIndexIncDec op => some (onExpr (incDecStmtUpd op))
  -- declarations
  | .valueDeclSkip => some (onStackDecl stackDeclSkipUpd)
  | .storageLocalDeclSkip => some (onStorageDecl storageDeclSkipUpd)
  | .storagePlaceAlias => some (onAlias storagePlaceAliasUpd)
  | .memoryDeclFreshAlloc | .storageToMemoryDeclCopyField
  | .storageToMemoryDeclCopyRoot => some (onMemoryDecl memoryDeclUpd)
  -- delete
  | .storageDeleteSimpleTarget => some (onDelete storageDeleteUpd)
  | .memoryDeleteSimpleTarget => some (onDelete memoryDeleteUpd)
  -- push / pop
  | .storagePushValueSave | .storagePushValueCopySource
  | .storagePushLengthSave => some (onPush pushUpd)
  | .storagePopSaveBox | .storagePopSaveDiamond => some (onPop popUpd)
  | .storageLocalRootPushBind => some (onAssign pushBindUpd)
  -- memory targets
  | .memoryRootAlias | .memoryStorageCopy
  | .memoryFieldWriteStore | .memoryFieldWriteCopy
  | .memoryIndexWriteStoreBox | .memoryIndexWriteStoreDiamond
  | .memoryIndexWriteCopyBox | .memoryIndexWriteCopyDiamond
  | .memoryFieldReadAliasRoot | .memoryIndexReadAliasRootBox
  | .memoryIndexReadAliasRootDiamond => some (onAssign memoryAssignUpd)
  -- control
  | .revertBox | .revertDiamond => some (onRevert revertUpd)
  | .assertSimple => some (onAssert assertUpd)
  | .requireSimple => some (onRequire assertUpd)
  | .transferNoCallback => some (onTransfer transferUpd)
  | _ => none

/-- A rule is in the terminal table. -/
abbrev hasUpdate (r : RuleName) : Bool := (terminalUpdate? r).isSome

/-- Total wrapper: the update, or stuck when the rule has none. -/
def terminalUpdate (r : RuleName) (stmt : Stmt) (s : State) : Res State :=
  match terminalUpdate? r with
  | some f => f stmt s
  | none => .error .stuck

end Wp
end Solidity
