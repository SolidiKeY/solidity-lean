import Solidity.Calculus.Fml
import Solidity.Syntax.Elab

/-!
# Terms read by name, resolved where they stand

The notation's front end (`dl!{ … }`'s readers, `Calculus/SurfaceNotation.lean`;
a specification's clauses, `Calculus/SurfaceSpec.lean`; `st!{ … }` and
`pt!{ … }`) reads a term before it knows the context the term stands in: a
local is a name.  So it reads a term as what it is in every named context
(`NTm`): the scoped term `Tm C Γ.ctx s` at `Γ : NCtx`, its locals the newest
of their names there, or the reason it is none.  This is `NRead`
(`Calculus/NotationResolve.lean`) for terms: nothing untyped is built.

* **A local** is the newest local of its name, which must be of the kind its
  sort says: at the value sort a `.val`, at the path sort an alias, a
  storage term `old` (`LTy.old`), an identity a memory local, and the
  ledger `x` of `x[a]` (`netOf`) an `LTy.oldNet`.
* **Its key** is its text by name, `Tm.keyStr`'s of the scoped term it
  names (`Calculus/Chains.lean`): a written line past the program is
  compared by it, read where no context declares the locals it names.

`NUpdElem` is an update's element over such terms, which
`Upd.resolveN` declares or assigns where it stands.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 IntOp)

variable {C : Contract}

/-! ## Names in a named context -/

/-- The newest local named `x`, of whatever type. -/
def NCtx.findAny (x : Var) : (Γ : NCtx) → Except String ((t : LTy) × Idx Γ.ctx t)
  | [] => .error s!"unknown name {x}"
  | (y, u) :: Γ =>
    if y = x then .ok ⟨u, .here⟩
    else do
      let ⟨t, i⟩ ← NCtx.findAny x Γ
      pure ⟨t, .there i⟩

/-- `x` read as `what`, where it is a local of type `t`. -/
def kindError {α : Type} (x : Var) (t : LTy) (what : String) : Except String α :=
  .error s!"`{x}` is declared as {t.toStr}, read as {what}"

/-! ## Terms by name -/

/-- **A term whose locals are names**: its text (`key`, as `Tm.keyStr`
writes the term it names) and the scoped term it is at each named context
(`resolve`). -/
structure NTm (C : Contract) (s : Srt) where
  key : String
  resolve : (Γ : NCtx) → Except String (Tm C Γ.ctx s)

namespace NTm

/-- A stack local. -/
def pvV (x : Var) : NTm C .val where
  key := reprStr x
  resolve Γ := do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .val _, i => pure (.pvV i)
    | t, _ => kindError x t "a value"

/-- A storage alias. -/
def pvP (x : Var) : NTm C .path where
  key := reprStr x
  resolve Γ := do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .alias _, i => pure (.pvP i)
    | t, _ => kindError x t "a storage alias"

/-- A storage variable, KeY's `old`. -/
def pvS (x : Var) : NTm C .st where
  key := reprStr x
  resolve Γ := do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .old, i => pure (.pvS i)
    | t, _ => kindError x t "a storage"

/-- A memory local. -/
def pvI (x : Var) : NTm C .ident where
  key := reprStr x
  resolve Γ := do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .mem _, i => pure (.pvI i)
    | t, _ => kindError x t "a memory reference"

/-- `x[a]`: what the ledger bound at `x` holds for `a`. -/
def netOf (x : Var) (a : NTm C .val) : NTm C .val where
  key := s!"({reprStr x})[{a.key}]"
  resolve Γ := do
    let a' ← a.resolve Γ
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .oldNet, i => pure (.netOf i a')
    | t, _ => kindError x t "a ledger"

def app0 {s : Srt} (o : Op0 s) : NTm C s where
  key := reprStr o
  resolve _ := pure (.app0 o)

def app1 {a s : Srt} (o : Op1 a s) (x : NTm C a) : NTm C s where
  key := s!"{reprStr o}({x.key})"
  resolve Γ := do
    let x' ← x.resolve Γ
    if h : o.named = false then pure (.app1 o h x') else .error "a named symbol"

def app2 {a b s : Srt} (o : Op2 a b s) (x : NTm C a) (y : NTm C b) : NTm C s where
  key := s!"{reprStr o}({x.key}, {y.key})"
  resolve Γ := do pure (.app2 o (← x.resolve Γ) (← y.resolve Γ))

def app3 {a b c s : Srt} (o : Op3 a b c s) (x : NTm C a) (y : NTm C b) (z : NTm C c) :
    NTm C s where
  key := s!"{reprStr o}({x.key}, {y.key}, {z.key})"
  resolve Γ := do pure (.app3 o (← x.resolve Γ) (← y.resolve Γ) (← z.resolve Γ))

/-- A scoped term read at the names `ns`, by name: what it is wherever its
locals' names stand. -/
def ofTm {Δ : Ctx} (ns : List Var) : {s : Srt} → Tm C Δ s → NTm C s
  | _, .pvV i => pvV (i.name ns)
  | _, .pvP i => pvP (i.name ns)
  | _, .pvS i => pvS (i.name ns)
  | _, .pvI i => pvI (i.name ns)
  | _, .netOf i a => netOf (i.name ns) (ofTm ns a)
  | _, .app0 o => app0 o
  | _, .app1 o _ x => app1 o (ofTm ns x)
  | _, .app2 o x y => app2 o (ofTm ns x) (ofTm ns y)
  | _, .app3 o x y z => app3 o (ofTm ns x) (ofTm ns y) (ofTm ns z)

end NTm

/-- A value term by name. -/
abbrev NTerm (C : Contract) := NTm C .val
/-- A storage path by name. -/
abbrev NPTerm (C : Contract) := NTm C .path
/-- A storage by name. -/
abbrev NSTerm (C : Contract) := NTm C .st
/-- What a storage `save` writes, by name. -/
abbrev NSValT (C : Contract) := NTm C .sv
/-- A memory identity by name. -/
abbrev NITerm (C : Contract) := NTm C .ident
/-- A member or an element of a memory object, by name. -/
abbrev NMAddr (C : Contract) := NTm C .addr
/-- A memory by name. -/
abbrev NMTerm (C : Contract) := NTm C .mem
/-- What a memory `write` writes, by name. -/
abbrev NMValT (C : Contract) := NTm C .mv

/-! The symbols, by the names of `Update.lean`'s. -/

section Ctors

def NTerm.lit (v : Semantics.Value) : NTerm C := .app0 (.lit v)
def NTerm.pv (x : Var) : NTerm C := .pvV x
def NTerm.binop (op : BinOp) (p : PrimTy) (a b : NTerm C) : NTerm C := .app2 (.binop op p) a b
def NTerm.unop (op : UnOp) (p : PrimTy) (a : NTerm C) : NTerm C := .app1 (.unop op p) a
def NTerm.find (s : NSTerm C) (p : NPTerm C) : NTerm C := .app2 .find s p
def NTerm.len (s : NSTerm C) (p : NPTerm C) : NTerm C := .app2 .len s p
def NTerm.read (m : NMTerm C) (a : NMAddr C) : NTerm C := .app2 .read m a
def NTerm.ite (c a b : NTerm C) : NTerm C := .app3 .ite c a b
def NTerm.mlen (m : NMTerm C) (i : NITerm C) : NTerm C := .app2 .mlen m i
def NTerm.env (k : EnvKey) : NTerm C := .app0 (.env k)
def NTerm.net (a : NTerm C) : NTerm C := .app1 .net a
def NTerm.netOf (x : Var) (a : NTerm C) : NTerm C := NTm.netOf x a
def NTerm.delValue (t : NTerm C) : NTerm C := .app1 .delValue t
def NTerm.wt (vs : List (Name × Ty)) (s : NSTerm C) : NTerm C := .app1 (.wt vs) s

def NPTerm.root (r : Name) : NPTerm C := .app0 (.root r)
def NPTerm.pv (x : Var) : NPTerm C := .pvP x
def NPTerm.field (p : NPTerm C) (f : Name) : NPTerm C := .app1 (.field f) p
def NPTerm.at (p : NPTerm C) (i : NTerm C) : NPTerm C := .app2 .at p i
def NPTerm.next (p : NPTerm C) : NPTerm C := .app1 .next p
def NPTerm.nextIn (s : NSTerm C) (p : NPTerm C) : NPTerm C := .app2 .nextIn s p
def NPTerm.atIn (s : NSTerm C) (p : NPTerm C) (i : NTerm C) : NPTerm C := .app3 .atIn s p i

def NSTerm.storage : NSTerm C := .app0 .storage
def NSTerm.mtSt (vs : List (Name × Ty)) : NSTerm C := .app0 (.mtSt vs)
def NSTerm.pv (x : Var) : NSTerm C := .pvS x
def NSTerm.save (s : NSTerm C) (p : NPTerm C) (v : NSValT C) : NSTerm C := .app3 .save s p v
def NSTerm.delAt (s : NSTerm C) (p : NPTerm C) : NSTerm C := .app2 .delAt s p
def NSTerm.push (s : NSTerm C) (p : NPTerm C) (v : NSValT C) : NSTerm C := .app3 .push s p v
def NSTerm.pushSlot (s : NSTerm C) (p : NPTerm C) (E : Ty) : NSTerm C := .app2 (.pushSlot E) s p
def NSTerm.pop (s : NSTerm C) (p : NPTerm C) : NSTerm C := .app2 .pop s p
def NSTerm.shrink (s : NSTerm C) (p : NPTerm C) : NSTerm C := .app2 .shrink s p
def NSTerm.extend (s : NSTerm C) (p : NPTerm C) (E : Ty) : NSTerm C := .app2 (.extend E) s p
def NSTerm.select (s : NSTerm C) (r : Name) : NSTerm C := .app1 (.select r) s

def NSValT.val (t : NTerm C) : NSValT C := .app1 .sval t
def NSValT.find (s : NSTerm C) (p : NPTerm C) : NSValT C := .app2 .sfind s p
def NSValT.copyMem (m : NMTerm C) (i : NITerm C) : NSValT C := .app2 .copyMem m i
def NSValT.newArr (R : RefTy) (n : NTerm C) : NSValT C := .app1 (.newArr R) n

def NITerm.pv (x : Var) : NITerm C := .pvI x
def NITerm.read (m : NMTerm C) (a : NMAddr C) : NITerm C := .app2 .iread m a
def NITerm.alloc (m : NMTerm C) (R : RefTy) : NITerm C := .app1 (.alloc R) m
def NITerm.copy (m : NMTerm C) (v : NSValT C) : NITerm C := .app2 .copy m v

def NMAddr.field (i : NITerm C) (f : Name) : NMAddr C := .app1 (.mfield f) i
def NMAddr.at (i : NITerm C) (k : NTerm C) : NMAddr C := .app2 .mat i k

def NMTerm.memory : NMTerm C := .app0 .memory
def NMTerm.write (m : NMTerm C) (a : NMAddr C) (v : NMValT C) : NMTerm C := .app3 .write m a v
def NMTerm.addM (m : NMTerm C) (R : RefTy) : NMTerm C := .app1 (.addM R) m
def NMTerm.copySt (m : NMTerm C) (v : NSValT C) : NMTerm C := .app2 .copySt m v

def NMValT.val (t : NTerm C) : NMValT C := .app1 .mval t
def NMValT.ref (i : NITerm C) : NMValT C := .app1 .ref i

end Ctors

/-! ## Updates by name -/

/-- One elementary update, its terms by name: `Upd.resolveN` declares or
assigns its target where it stands. -/
inductive NUpdElem (C : Contract) where
  /-- `v := t` -/
  | val (x : Var) (t : NTerm C)
  /-- `lsv := p` -/
  | path (x : Var) (p : NPTerm C)
  /-- `lsv := unset` (`storageLocalDeclSkip`). -/
  | unset (x : Var)
  /-- `mv := i` -/
  | mref (x : Var) (i : NITerm C)
  /-- `storage := s` -/
  | storage (s : NSTerm C)
  /-- `old := s` -/
  | store (x : Var) (s : NSTerm C)
  /-- `memory := m` -/
  | memory (m : NMTerm C)
  /-- `selfBalance := selfBalance ± a` -/
  | selfBalance (op : IntOp) (a : NTerm C)
  /-- `net := store(net, at(r), net(r) ± a)` -/
  | net (r : NTerm C) (op : IntOp) (a : NTerm C)
  /-- `net := if(r = this) then net else store(net, at(r), net(r) - a)` -/
  | pay (r a : NTerm C)
  /-- `oldNet := net` -/
  | saveNet (x : Var)
  /-- `oldNet := mtSt` -/
  | saveNetMt (x : Var)
  /-- `net := store(mtSt, at(r), a)` -/
  | netMt (r a : NTerm C)
  /-- `selfBalance := a` -/
  | setBalance (a : NTerm C)

/-- An element as text, as `UpdElem.keyStr` writes the scoped one. -/
def NUpdElem.keyStr : NUpdElem C → String
  | .val x t => s!"{reprStr x} := {t.key}"
  | .path x t => s!"{reprStr x} := {t.key}"
  | .mref x t => s!"{reprStr x} := {t.key}"
  | .store x t => s!"{reprStr x} := {t.key}"
  | .unset x => s!"{reprStr x} := unset"
  | .saveNet x => s!"{reprStr x} := net"
  | .saveNetMt x => s!"{reprStr x} := mtNet"
  | .storage t => s!"storage := {t.key}"
  | .memory t => s!"memory := {t.key}"
  | .selfBalance op a => s!"selfBalance {reprStr op} {a.key}"
  | .net r op a => s!"net {r.key} {reprStr op} {a.key}"
  | .pay r a => s!"pay {r.key} {a.key}"
  | .netMt r a => s!"netMt {r.key} {a.key}"
  | .setBalance a => s!"setBalance {a.key}"

/-- The local an element sets, if it sets one. -/
def NUpdElem.setsLocal? : NUpdElem C → Option Var
  | .val x _ | .path x _ | .unset x | .mref x _ | .store x _ | .saveNet x | .saveNetMt x => some x
  | _ => none

/-- Whether a local of type `t` is what the element sets. -/
def NUpdElem.fits : NUpdElem C → LTy → Bool
  | .val .., .val _ | .path .., .alias _ | .unset _, .alias _ | .mref .., .mem _
  | .store .., .old | .saveNet _, .oldNet | .saveNetMt _, .oldNet => true
  | _, _ => false

/-- The type of the local an element sets, when nothing else says: a
storage's `old`, a ledger's `oldNet`, a value's `uint`. -/
def NUpdElem.ownTy? : NUpdElem C → Option LTy
  | .val .. => some (.val .uint)
  | .store .. => some .old
  | .saveNet _ | .saveNetMt _ => some .oldNet
  | _ => none

end Solidity
