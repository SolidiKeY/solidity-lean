import Solidity.Calculus.Lower
import Solidity.Syntax.Elab

/-!
# Terms read by name, resolved where they stand

The notation's front end (`dl!{ … }`'s readers, `Calculus/SurfaceNotation.lean`;
a specification's clauses, `Calculus/SurfaceSpec.lean`; `st!{ … }` and
`pt!{ … }`) reads a term before it knows the context the term stands in: a
local is a name.  So it reads a term as what it is in every named context
(`NTm`): the scoped term at `Γ : NCtx`, its locals the newest of their
names there, or the reason it is none.  This is `NRead`
(`Calculus/NotationResolve.lean`) for terms: nothing untyped is built.

**Typed where it resolves** (W9.8.3b).  A term's sort carries its Solidity
type (`Srt`, `Signature.lean`), and the type of a name is known only where
it resolves: `x` is a `uint` or a `bool` by the local it names, `p.f` a path
to what `p`'s struct declares.  So a term by name is indexed by its sort's
*kind* only (`SrtK`: value, path, storage, …, what the reader's position
says), and resolution is bidirectional:

* `resolve` *synthesizes*: the sort and the scoped term at it
  (`Resolved`, `(s : Srt) × Tm C Γ.ctx s`).  A symbol is picked by its
  arguments' sorts (`find(s, p)` is `Op2.find` over a storage and
  `Op2.findIn` under a `select`), and its proofs (`rootType`, `fieldType`,
  `accepts`, `mapFree`, an `IndexTy`) are found then: a contract lookup by
  `match h : … with`, a Boolean side condition by `if h : … = true`, in the
  compiled reader, at compile time;
* `check` *checks* against an expected sort: synthesis compared (`Srt` is
  decidable), or the term's own `checkAt?`: a numeral takes the type it is
  checked at (`x + 1` at `x`'s type, `save(s, p, 1)` at `p`'s), and
  synthesizes a `uint`.

An argument of known sort is checked; of an operand pair (`a = b`, `a + b`,
`c ? a : b`) the side that is no numeral synthesizes and the other is
checked.  A mismatch names the term as it was written (`text`): "`alice.age`
is a `uint`, used as a `bool`".

* **A local** is the newest local of its name, which must be of the kind its
  sort says: at the value sort a `.val`, at the path sort an alias, a
  storage term `old` (`LTy.old`), an identity a memory local, and the
  ledger `x` of `x[a]` (`netOf`) an `LTy.oldNet`.
* **Its key** is its text by name, `Tm.keyStr`'s of the scoped term it
  names: a written line past the program is compared by it, read where no
  context declares the locals it names.  A symbol's key is its untyped
  namesake's (`OpN.key`: `findIn` is `find`, `member f` is `root f`), with
  no Solidity type in it, since a key is computed before anything resolves.
  KeY's `int` is told apart by name (`NTm.isK`: a ledger read, a KeY `int`
  local, arithmetic over one), so its symbols keep their own keys
  (`zlit n`, `zbin +`, `zcmp ==`) and a widening its `toInt(…)` (`keyK`).
* **KeY's `int`** (`Srt.kint`, kind `.val`): a term of fixed type `uint`
  (a local, a read, `msg.value`) beside one is widened (`widen`,
  `resolvePairV`), a numeral checked at it is a KeY literal, and a free
  parameter is never widened: the reader makes it a KeY `int` where only
  such arithmetic reads it (`RawFml.kintParams`).

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

/-- A name as an error message writes it (`se1` for a fresh one, whatever
the file's `FreshNames`). -/
def Var.text : Var → String
  | .user s => s
  | .fresh b k => s!"{b}{k}"

/-! ## Sorts' kinds and their text -/

/-- A sort with its types forgotten: what the reader's position says of a
term before it resolves.  Under `select` a storage is `st` and a path
`path`. -/
inductive SrtK where
  | val | path | st | sv | ident | addr | mem | mv
  deriving DecidableEq, Repr

/-- The kind of a sort. -/
@[reducible] def Srt.kind : Srt → SrtK
  | .val _ => .val
  | .path _ | .spath .. => .path
  | .st | .sts _ => .st
  | .sv _ => .sv
  | .ident _ => .ident
  | .addr _ => .addr
  | .mem => .mem
  | .mv _ => .mv
  | .kint => .val

/-- A sort as an error message names it. -/
def Srt.describe : Srt → String
  | .val p => s!"a `{p.toStr}`"
  | .path T => s!"a path to a `{T}`"
  | .st => "a storage"
  | .sv T => s!"a storage value of type `{T}`"
  | .ident R => s!"a memory `{Ty.ref R}`"
  | .addr T => s!"a memory location of type `{T}`"
  | .mem => "a memory"
  | .mv T => s!"a memory value of type `{T}`"
  | .sts s => s!"the members of a `{s}` (a `select`)"
  | .spath s T => s!"a path from a member of `{s}` to a `{T}`"
  | .kint => "a KeY `int`"

/-- A value of a primitive type as text. -/
def PrimTy.showD : (p : PrimTy) → p.Denote → String
  | .bool, b => toString (show Bool from b)
  | .uint, v => toString (v : {n : Int // PrimTy.uint.inRange n = true}).1
  | .int, v => toString (v : {n : Int // PrimTy.int.inRange n = true}).1

/-! ## The symbols' keys

A symbol's name in a key: its untyped namesake's, with the data it was
written with (a root's name, an operator) and no type. -/

def Op0.key {s : Srt} : Op0 C s → String
  | @Op0.lit _ p v => s!"lit {p.showD v}"
  | .env k => s!"env {k.toStr}"
  | .root r _ => s!"root {r}"
  | .storage => "storage"
  | .memory => "memory"
  | .mtSt => "mtSt"
  | .member _ f _ => s!"root {f}"
  | .zlit n => s!"zlit {n}"

def Op1.key {a s : Srt} : Op1 C a s → String
  | .unop op _ => s!"unop {op.sym}"
  | .net => "net"
  | .delValue => "delValue"
  | @Op1.field _ _ f _ _ => s!"field {f}"
  | .next => "next"
  | .sval => "sval"
  | @Op1.newArr _ R _ => s!"newArr {Ty.ref R}"
  | .alloc R _ => s!"alloc {Ty.ref R}"
  | @Op1.mfield _ _ f _ _ => s!"mfield {f}"
  | .addM R _ => s!"addM {Ty.ref R}"
  | .mval => "mval"
  | .ref => "ref"
  | .wt => "wt"
  | .cleanTail => "cleanTail"
  | .select r _ => s!"select {r}"
  | @Op1.selectIn _ _ _ f _ => s!"select {f}"
  | @Op1.fieldIn _ _ _ f _ _ => s!"field {f}"
  | .toInt => "toInt"
  -- the source's type is its term's: only the destination's is written
  | @Op1.fixedCopy _ _ _ R _ => s!"fixedCopy {Ty.ref R}"

def Op2.key {a b s : Srt} : Op2 C a b s → String
  | .binop op _ => s!"binop {op.sym}"
  | .find | .findIn => "find"
  | .len => "len"
  | .read => "read"
  | .mlen => "mlen"
  | .at _ => "at"
  | .nextIn => "nextIn"
  | .delAt | .delAtIn => "delAt"
  | .pushSlot => "pushSlot"
  | .pop => "pop"
  | .shrink => "shrink"
  | .extend => "extend"
  | .sfind | .sfindIn => "sfind"
  | .copyMem => "copyMem"
  | .iread => "iread"
  | .copy _ => "copy"
  | .mat _ => "mat"
  | .copySt _ => "copySt"
  | .zbin op _ => s!"zbin {op.sym}"
  | .zcmp op _ => s!"zcmp {op.sym}"

def Op3.key {a b c s : Srt} : Op3 C a b c s → String
  | .ite => "ite"
  | .save | .saveIn => "save"
  | .push => "push"
  | .atIn _ => "atIn"
  | .write => "write"
  | .modular op => op.toStr

/-- A term as text, its positions named by `ns`: the key a line is compared
by (`Calculus/Chains.lean`'s `Fml.lineKey`). -/
def Tm.keyStr {Γ : Ctx} (ns : List Var) : {s : Srt} → Tm C Γ s → String
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i => reprStr (i.name ns)
  | _, .netOf i a => s!"({reprStr (i.name ns)})[{Tm.keyStr ns a}]"
  | _, .app0 o => o.key
  | _, .app1 o x => s!"{o.key}({Tm.keyStr ns x})"
  | _, .app2 o x y => s!"{o.key}({Tm.keyStr ns x}, {Tm.keyStr ns y})"
  | _, .app3 o x y z => s!"{o.key}({Tm.keyStr ns x}, {Tm.keyStr ns y}, {Tm.keyStr ns z})"
  | _, .pvZ i => reprStr (i.name ns)

/-! ## Terms by name -/

/-- What a term resolves to at `Γ`: its sort and the scoped term at it. -/
abbrev Resolved (C : Contract) (Γ : NCtx) := (s : Srt) × Tm C Γ.ctx s

/-- **A term whose locals are names**, at a sort of kind `k`: its key (as
`Tm.keyStr` writes the term it names), its text (for errors), the term it
synthesizes at each named context (`resolve`), and, for a term whose sort
the context fixes (a numeral), how it is checked (`checkAt?`). -/
structure NTm (C : Contract) (k : SrtK) where
  key : String
  text : String
  resolve : (Γ : NCtx) → Except String (Resolved C Γ)
  checkAt? : Option ((s : Srt) → (Γ : NCtx) → Except String (Tm C Γ.ctx s)) := none
  /-- Whether it synthesizes a KeY `int`, read by name (a ledger read, a
  KeY `int` local, arithmetic over one), so a key is known before the term
  resolves. -/
  isK : Bool := false
  /-- Its key where it is checked at a KeY `int`, if not `keyK`'s default. -/
  keyKO : Option String := none

/-- A term's key where it is checked at a KeY `int`: its own if it is one, a
numeral's literal at the sort (`zlit n`), else widened (`toInt(…)`). -/
def NTm.keyK {k : SrtK} (t : NTm C k) : String :=
  t.keyKO.getD (if t.isK then t.key else s!"toInt({t.key})")

/-- `t` is of sort `s'`, used at `s`. -/
def sortError {α : Type} (t : String) (s' s : Srt) : Except String α :=
  .error s!"`{t}` is {s'.describe}, used as {s.describe}"

/-- `t` is of sort `s'`, used as `what`. -/
def useError {α : Type} (t : String) (s' : Srt) (what : String) : Except String α :=
  .error s!"`{t}` is {s'.describe}, used as {what}"

namespace NTm

variable {k : SrtK}

/-- A term of sort `s'` used at `s`: itself, a `uint` of fixed type (a
local, a read, `msg.value`: what synthesizes) used as a KeY `int` widened
(`Op1.toInt`: solkey's `msgValue` and ledger are KeY `int`s), else the
mismatch. -/
def widen (text : String) {Γ : Ctx} : (s' s : Srt) → Tm C Γ s' → Except String (Tm C Γ s)
  | .val .uint, .kint, x => pure (.app1 .toInt x)
  | .sv (.ref (.fixed E n)), .sv (.ref R), x =>
    if h : RefTy.fixed E n = R then pure (h ▸ x)
    else match FixedCopy.ofTarget E n R with
      | some shape => pure (.app1 (.fixedCopy shape) x)
      | none => sortError text (.sv (.ref (.fixed E n))) (.sv (.ref R))
  | s', s, x => if h : s' = s then pure (h ▸ x) else sortError text s' s

/-- `t` at the sort `s`: synthesized and compared (a `uint` widened to an
`int`, `widen`), or checked by its own `checkAt?`. -/
def check (t : NTm C k) (s : Srt) (Γ : NCtx) : Except String (Tm C Γ.ctx s) :=
  match t.checkAt? with
  | some f => f s Γ
  | none => do
    let ⟨s', x⟩ ← t.resolve Γ
    widen t.text s' s x

/-- A term at a value sort of a Solidity type, and its type. -/
def resolveVal (t : NTm C .val) (Γ : NCtx) :
    Except String ((p : PrimTy) × Tm C Γ.ctx (.val p)) := do
  match ← t.resolve Γ with
  | ⟨.val p, x⟩ => pure ⟨p, x⟩
  | ⟨s, _⟩ => useError t.text s "a value of a Solidity type"

/-- A value's sort: a Solidity type's (`val p`) or KeY's `int`. -/
inductive VSort where
  | prim (p : PrimTy)
  | kint
  deriving DecidableEq

/-- A value sort as an error message names it. -/
def VSort.toStr : VSort → String
  | .prim p => p.toStr
  | .kint => "KeY `int`"

/-- The sort a value sort is. -/
@[reducible] def VSort.srt : VSort → Srt
  | .prim p => .val p
  | .kint => .kint

/-- A term at a value sort, a Solidity type's or KeY's `int`. -/
def resolveV (t : NTm C .val) (Γ : NCtx) :
    Except String ((v : VSort) × Tm C Γ.ctx v.srt) := do
  match ← t.resolve Γ with
  | ⟨.val p, x⟩ => pure ⟨.prim p, x⟩
  | ⟨.kint, x⟩ => pure ⟨.kint, x⟩
  | ⟨s, _⟩ => useError t.text s "a value"

/-- Two values at one sort: the side that is no numeral synthesizes it
(the first if neither or both are), the other is checked at it; a side of
fixed type `uint` beside a KeY `int` is widened (`widen`). -/
def resolvePairV (a b : NTm C .val) (Γ : NCtx) :
    Except String ((v : VSort) × Tm C Γ.ctx v.srt × Tm C Γ.ctx v.srt) := do
  if a.checkAt?.isSome && b.checkAt?.isNone then
    let ⟨v, b'⟩ ← b.resolveV Γ
    pure ⟨v, ← a.check v.srt Γ, b'⟩
  else
    let ⟨v, a'⟩ ← a.resolveV Γ
    if b.checkAt?.isSome then return ⟨v, a', ← b.check v.srt Γ⟩
    let ⟨q, b'⟩ ← b.resolve Γ
    match v, a', q, b' with
    | .prim .uint, a', .kint, b' => pure ⟨.kint, .app1 .toInt a', b'⟩
    | v, a', q, b' => pure ⟨v, a', ← widen b.text q v.srt b'⟩

/-- Two values at one Solidity type (`resolvePairV`, a KeY `int` refused). -/
def resolvePair (a b : NTm C .val) (Γ : NCtx) :
    Except String ((p : PrimTy) × Tm C Γ.ctx (.val p) × Tm C Γ.ctx (.val p)) := do
  match ← resolvePairV a b Γ with
  | ⟨.prim p, a', b'⟩ => pure ⟨p, a', b'⟩
  | ⟨.kint, _, _⟩ => useError s!"{a.text}, {b.text}" .kint "a value of a Solidity type"

/-- A term that synthesizes: no `checkAt?`. -/
def syn (key text : String) (resolve : (Γ : NCtx) → Except String (Resolved C Γ)) : NTm C k :=
  { key, text, resolve }

/-- A stack local, or a KeY `int` one (`isK`: what the reader's scope says
of the name). -/
def pvV (x : Var) (isK : Bool := false) : NTm C .val :=
  { key := reprStr x, text := x.text, isK
    resolve := fun Γ => do
      let ⟨t, i⟩ ← Γ.findAny x
      match t, i with
      | .val p, i => pure ⟨.val p, .pvV i⟩
      | .kint, i => pure ⟨.kint, .pvZ i⟩
      | t, _ => kindError x t "a value" }

/-- A storage alias. -/
def pvP (x : Var) : NTm C .path :=
  syn (reprStr x) x.text fun Γ => do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .alias R, i => pure ⟨.path (.ref R), .pvP i⟩
    | t, _ => kindError x t "a storage alias"

/-- A storage variable, KeY's `old`. -/
def pvS (x : Var) : NTm C .st :=
  syn (reprStr x) x.text fun Γ => do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .old, i => pure ⟨.st, .pvS i⟩
    | t, _ => kindError x t "a storage"

/-- A memory local. -/
def pvI (x : Var) : NTm C .ident :=
  syn (reprStr x) x.text fun Γ => do
    let ⟨t, i⟩ ← Γ.findAny x
    match t, i with
    | .mem R, i => pure ⟨.ident R, .pvI i⟩
    | t, _ => kindError x t "a memory reference"

/-- `x[a]`: what the ledger bound at `x` holds for `a`. -/
def netOf (x : Var) (a : NTm C .val) : NTm C .val :=
  { key := s!"({reprStr x})[{a.key}]", text := s!"net({x.text}, {a.text})", isK := true
    resolve := fun Γ => do
      let a' ← a.check (.val .uint) Γ
      let ⟨t, i⟩ ← Γ.findAny x
      match t, i with
      | .oldNet, i => pure ⟨.kint, .netOf i a'⟩
      | t, _ => kindError x t "a ledger" }

/-- A symbol of a sort its constructor fixes, its arguments checked. -/
def app0 {s : Srt} (o : Op0 C s) (text : String) : NTm C s.kind :=
  { (syn o.key text fun _ => pure ⟨s, .app0 o⟩ : NTm C s.kind) with isK := s == .kint }

/-- An argument's key at the sort it is checked at: a KeY `int`'s
`keyK`. -/
def keyAt {k : SrtK} (x : NTm C k) (a : Srt) : String := if a == .kint then x.keyK else x.key

def app1 {a s : Srt} (o : Op1 C a s) (x : NTm C a.kind) (text : String) : NTm C s.kind :=
  { (syn s!"{o.key}({x.keyAt a})" text (fun Γ => do pure ⟨s, .app1 o (← x.check a Γ)⟩) :
      NTm C s.kind) with
    isK := s == .kint }

def app2 {a b s : Srt} (o : Op2 C a b s) (x : NTm C a.kind) (y : NTm C b.kind) (text : String) :
    NTm C s.kind :=
  { (syn s!"{o.key}({x.keyAt a}, {y.keyAt b})" text (fun Γ => do
      pure ⟨s, .app2 o (← x.check a Γ) (← y.check b Γ)⟩) : NTm C s.kind) with
    isK := s == .kint }

def app3 {a b c s : Srt} (o : Op3 C a b c s) (x : NTm C a.kind) (y : NTm C b.kind)
    (z : NTm C c.kind) (text : String) : NTm C s.kind :=
  { (syn s!"{o.key}({x.keyAt a}, {y.keyAt b}, {z.keyAt c})" text (fun Γ => do
      pure ⟨s, .app3 o (← x.check a Γ) (← y.check b Γ) (← z.check c Γ)⟩) : NTm C s.kind) with
    isK := s == .kint }

/-- A scoped term read at the names `ns`, by name: what it is wherever its
locals' names stand (its text its key). -/
def ofTm {Δ : Ctx} (ns : List Var) : {s : Srt} → Tm C Δ s → NTm C s.kind
  | _, .pvV i => pvV (i.name ns)
  | _, .pvZ i => pvV (i.name ns) (isK := true)
  | _, .pvP i => pvP (i.name ns)
  | _, .pvS i => pvS (i.name ns)
  | _, .pvI i => pvI (i.name ns)
  | _, .netOf i a => netOf (i.name ns) (ofTm ns a)
  | _, .app0 o => app0 o o.key
  | _, t@(.app1 o x) => app1 o (ofTm ns x) (Tm.keyStr ns t)
  | _, t@(.app2 o x y) => app2 o (ofTm ns x) (ofTm ns y) (Tm.keyStr ns t)
  | _, t@(.app3 o x y z) => app3 o (ofTm ns x) (ofTm ns y) (ofTm ns z) (Tm.keyStr ns t)

end NTm

/-- A value term by name. -/
abbrev NTerm (C : Contract) := NTm C .val
/-- A storage path by name (under a `select` too). -/
abbrev NPTerm (C : Contract) := NTm C .path
/-- A storage by name (a `select` too). -/
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

/-! ## Types the symbols read off their arguments -/

/-- How a reference type is indexed (`Loc.index`'s `IndexTy`): a mapping
by its primitive key, an array by a `uint`. -/
def RefTy.indexTy? : (R : RefTy) → Option ((k : PrimTy) × (V : Ty) × IndexTy R k V)
  | .mapping k V => some ⟨k, V, .map⟩
  | .array E => some ⟨.uint, E, .arr .dyn⟩
  | .fixed E _ => some ⟨.uint, E, .arr .fixed⟩
  | _ => none

/-- An array type's element (`ArrTy`). -/
def RefTy.arrTy? : (R : RefTy) → Option ((E : Ty) × ArrTy R E)
  | .array E => some ⟨E, .dyn⟩
  | .fixed E _ => some ⟨E, .fixed⟩
  | _ => none

/-- A literal of type `p`, written `text`. -/
def numLit (text : String) (n : Int) : (p : PrimTy) → Except String p.Denote
  | .bool => .error s!"`{text}` is a number, used as a `bool`"
  | .uint => if h : PrimTy.uint.inRange n = true then pure (PrimTy.ofLit .uint n h)
      else .error s!"`{text}` is out of the range of a `uint`"
  | .int => if h : PrimTy.int.inRange n = true then pure (PrimTy.ofLit .int n h)
      else .error s!"`{text}` is out of the range of an `int`"

namespace NTm

/-- An index at its key type. -/
def idxAt (i : NTm C .val) (Γ : NCtx) (k : PrimTy) : Except String (Tm C Γ.ctx (.val k)) :=
  i.check (.val k) Γ

/-- The struct `s`'s member `f`, at its type. -/
def fieldOf (s f : Name) (text : String) :
    Except String ((T : Ty) × PLift (C.fieldType s f = some T)) :=
  if h : (C.fieldType s f).isSome then pure ⟨_, ⟨(Option.some_get h).symm⟩⟩
  else .error s!"`{text}`: `{s}` has no member `{f}`"

/-- A storage path to a dynamic array, and its element type. -/
def arrayPath (p : NTm C .path) (Γ : NCtx) :
    Except String ((E : Ty) × Tm C Γ.ctx (.path (.ref (.array E)))) := do
  match ← p.resolve Γ with
  | ⟨.path (.ref (.array E)), p'⟩ => pure ⟨E, p'⟩
  | ⟨s, _⟩ => useError p.text s "a path to a dynamic array (a push or a pop)"

/-- A storage, not under a `select`. -/
def topStorage (s : NTm C .st) (Γ : NCtx) : Except String (Tm C Γ.ctx .st) := s.check .st Γ

end NTm

/-! The symbols, by the names of `Update.lean`'s: each picks its typed
symbol by its arguments' sorts. -/

section Ctors

open NTm (syn)

/-- A literal of type `p`. -/
def NTerm.lit {p : PrimTy} (v : p.Denote) : NTerm C := NTm.app0 (.lit v) (p.showD v)

/-- A numeral: a `uint`, or the type it is checked at (a negative one an
`int`, a specification's `-1`). -/
def NTerm.num (n : Int) : NTerm C :=
  { key := s!"lit {n}", text := toString n
    resolve := fun _ => do
      let p : PrimTy := if n < 0 then .int else .uint
      pure ⟨.val p, .app0 (.lit (← numLit (toString n) n p))⟩
    checkAt? := some fun s _ => match s with
      | .val p => do pure (.app0 (.lit (← numLit (toString n) n p)))
      | .kint => pure (.app0 (.zlit n))
      | s => .error s!"`{n}` is a number, used as {s.describe}"
    keyKO := some s!"zlit {n}" }

def NTerm.bool (b : Bool) : NTerm C := NTerm.lit (p := .bool) b
def NTerm.pv (x : Var) : NTerm C := .pvV x

/-- `a ⊕ b`, at the operands' type: on KeY's `int` (unbounded, `zbin`, or a
comparison `zcmp`) where an operand is one. -/
def NTerm.binop (op : BinOp) (a b : NTerm C) : NTerm C :=
  let k := a.isK || b.isK
  { key := if k then s!"{if op.zCmp then "zcmp" else "zbin"} {op.sym}({a.keyK}, {b.keyK})"
      else s!"binop {op.sym}({a.key}, {b.key})"
    text := s!"{a.text} {op.sym} {b.text}"
    isK := k && !op.zCmp
    resolve := fun Γ => do
      match ← NTm.resolvePairV a b Γ with
      | ⟨.prim p, a', b'⟩ =>
        if h : op.accepts p = true then pure ⟨_, .app2 (.binop op h) a' b'⟩
        else .error s!"`{op.sym}` does not apply to a `{p.toStr}` (`{a.text}`)"
      | ⟨.kint, a', b'⟩ =>
        if h : op.zArith = true then pure ⟨_, .app2 (.zbin op h) a' b'⟩
        else if h : op.zCmp = true then pure ⟨_, .app2 (.zcmp op h) a' b'⟩
        else .error s!"`{op.sym}` does not apply to a KeY `int` (`{a.text}`)" }

/-- `⊖ a`, at the operand's type. -/
def NTerm.unop (op : UnOp) (a : NTerm C) : NTerm C :=
  syn s!"unop {op.sym}({a.key})" (op.show a.text) fun Γ => do
    let ⟨p, a'⟩ ← a.resolveVal Γ
    if h : op.accepts p = true then pure ⟨_, .app1 (.unop op h) a'⟩
    else .error s!"`{op.sym}` does not apply to a `{p.toStr}` (`{a.text}`)"

/-- `find(s, p)`, under a `select` too; a bare path in a value position is
`find(storage, p)`, written as the path. -/
def NTerm.find (s : NSTerm C) (p : NPTerm C) : NTerm C :=
  syn s!"find({s.key}, {p.key})"
    (if s.key == "storage" then p.text else s!"find({s.text}, {p.text})") fun Γ => do
    match ← s.resolve Γ, ← p.resolve Γ with
    | ⟨.st, s'⟩, ⟨.path (.prim _), p'⟩ => pure ⟨_, .app2 .find s' p'⟩
    | ⟨.sts S, s'⟩, ⟨.spath S' (.prim _), p'⟩ =>
      if h : S' = S then by subst h; exact pure ⟨_, .app2 .findIn s' p'⟩
      else .error s!"`{p.text}` is a path under `{S'}`, read under `{S}`"
    | ⟨.st, _⟩, ⟨σ, _⟩ | ⟨.sts _, _⟩, ⟨σ, _⟩ => useError p.text σ "a path to a value"
    | ⟨σ, _⟩, _ => useError s.text σ "a storage"

def NTerm.len (s : NSTerm C) (p : NPTerm C) : NTerm C :=
  syn s!"len({s.key}, {p.key})" s!"{p.text}.length" fun Γ => do
    let s' ← s.topStorage Γ
    let ⟨_, p'⟩ ← p.arrayPath Γ
    pure ⟨_, .app2 .len s' p'⟩

def NTerm.read (m : NMTerm C) (a : NMAddr C) : NTerm C :=
  syn s!"read({m.key}, {a.key})" (if m.key == "memory" then a.text else s!"read({m.text}, {a.text})")
    fun Γ => do
    let m' ← m.check .mem Γ
    match ← a.resolve Γ with
    | ⟨.addr (.prim _), a'⟩ => pure ⟨_, .app2 .read m' a'⟩
    | ⟨σ, _⟩ => useError a.text σ "a memory location of a value"

def NTerm.ite (c a b : NTerm C) : NTerm C :=
  syn s!"ite({c.key}, {a.key}, {b.key})" s!"{c.text} ? {a.text} : {b.text}" fun Γ => do
    let c' ← c.check (.val .bool) Γ
    let ⟨_, a', b'⟩ ← NTm.resolvePair a b Γ
    pure ⟨_, .app3 .ite c' a' b'⟩

def NTerm.mlen (m : NMTerm C) (i : NITerm C) : NTerm C :=
  syn s!"mlen({m.key}, {i.key})" s!"{i.text}.length" fun Γ => do
    let m' ← m.check .mem Γ
    match ← i.resolve Γ with
    | ⟨.ident (.array _), i'⟩ => pure ⟨_, .app2 .mlen m' i'⟩
    | ⟨σ, _⟩ => useError i.text σ "a memory array"

def NTerm.env (k : EnvKey) : NTerm C := NTm.app0 (.env k) k.toStr
def NTerm.net (a : NTerm C) : NTerm C := NTm.app1 .net a s!"net({a.text})"
def NTerm.netOf (x : Var) (a : NTerm C) : NTerm C := NTm.netOf x a

def NTerm.delValue (t : NTerm C) : NTerm C :=
  syn s!"delValue({t.key})" s!"delValue({t.text})" fun Γ => do
    let ⟨_, t'⟩ ← t.resolveVal Γ
    pure ⟨_, .app1 .delValue t'⟩

def NTerm.wt (s : NSTerm C) : NTerm C := NTm.app1 .wt s s!"wt({s.text})"
def NTerm.cleanTail (s : NSTerm C) : NTerm C := NTm.app1 .cleanTail s s!"cleanTail({s.text})"

/-- A root of the contract. -/
def NPTerm.root (r : Name) : NPTerm C :=
  syn s!"root {r}" r fun _ =>
    match h : C.rootType r with
    | some _ => pure ⟨_, .app0 (.root r h)⟩
    | none => .error s!"`{r}` is no state variable of the contract"

/-- The member `f` of the struct `s`, a root under `select`. -/
def NPTerm.member (s f : Name) : NPTerm C :=
  syn s!"root {f}" f fun _ =>
    match h : C.fieldType s f with
    | some _ => pure ⟨_, .app0 (.member s f h)⟩
    | none => .error s!"`{f}`: `{s}` has no member `{f}`"

def NPTerm.pv (x : Var) : NPTerm C := .pvP x

/-- `p.f`, under a `select` too. -/
def NPTerm.field (p : NPTerm C) (f : Name) : NPTerm C :=
  syn s!"field {f}({p.key})" s!"{p.text}.{f}" fun Γ => do
    match ← p.resolve Γ with
    | ⟨.path (.ref (.struct s)), p'⟩ =>
      let ⟨_, ⟨h⟩⟩ ← NTm.fieldOf (C := C) s f s!"{p.text}.{f}"
      pure ⟨_, .app1 (.field h) p'⟩
    | ⟨.spath S (.ref (.struct s)), p'⟩ =>
      let ⟨_, ⟨h⟩⟩ ← NTm.fieldOf (C := C) s f s!"{p.text}.{f}"
      pure ⟨_, .app1 (.fieldIn (s := S) h) p'⟩
    | ⟨σ, _⟩ => useError p.text σ "a path to a struct"

/-- `p[i]`. -/
def NPTerm.at (p : NPTerm C) (i : NTerm C) : NPTerm C :=
  syn s!"at({p.key}, {i.key})" s!"{p.text}[{i.text}]" fun Γ => do
    match ← p.resolve Γ with
    | ⟨.path (.ref R), p'⟩ =>
      let some ⟨k, _, it⟩ := R.indexTy? | useError p.text (.path (.ref R)) "an array or a mapping"
      pure ⟨_, .app2 (.at it) p' (← i.idxAt Γ k)⟩
    | ⟨σ, _⟩ => useError p.text σ "a path to an array or a mapping"

/-- `p[p.length]`, the slot past the end. -/
def NPTerm.next (p : NPTerm C) : NPTerm C :=
  syn s!"next({p.key})" s!"{p.text}[{p.text}.length]" fun Γ => do
    let ⟨_, p'⟩ ← p.arrayPath Γ
    pure ⟨_, .app1 .next p'⟩

def NPTerm.nextIn (s : NSTerm C) (p : NPTerm C) : NPTerm C :=
  syn s!"nextIn({s.key}, {p.key})" s!"{p.text}[{p.text}.length]@{s.text}" fun Γ => do
    let s' ← s.topStorage Γ
    let ⟨_, p'⟩ ← p.arrayPath Γ
    pure ⟨_, .app2 .nextIn s' p'⟩

def NPTerm.atIn (s : NSTerm C) (p : NPTerm C) (i : NTerm C) : NPTerm C :=
  syn s!"atIn({s.key}, {p.key}, {i.key})" s!"{p.text}[{i.text}]@{s.text}" fun Γ => do
    let s' ← s.topStorage Γ
    match ← p.resolve Γ with
    | ⟨.path (.ref R), p'⟩ =>
      let some ⟨k, _, it⟩ := R.indexTy? | useError p.text (.path (.ref R)) "an array or a mapping"
      pure ⟨_, .app3 (.atIn it) s' p' (← i.idxAt Γ k)⟩
    | ⟨σ, _⟩ => useError p.text σ "a path to an array or a mapping"

def NSTerm.storage : NSTerm C := NTm.app0 .storage "storage"
def NSTerm.mtSt : NSTerm C := NTm.app0 .mtSt "mtSt"
def NSTerm.pv (x : Var) : NSTerm C := .pvS x

/-- `save(s, p, v)`, under a `select` too; `v` checked at `p`'s type. -/
def NSTerm.save (s : NSTerm C) (p : NPTerm C) (v : NSValT C) : NSTerm C :=
  syn s!"save({s.key}, {p.key}, {v.key})" s!"save({s.text}, {p.text}, {v.text})" fun Γ => do
    match ← s.resolve Γ, ← p.resolve Γ with
    | ⟨.st, s'⟩, ⟨.path T, p'⟩ => pure ⟨_, .app3 .save s' p' (← v.check (.sv T) Γ)⟩
    | ⟨.sts S, s'⟩, ⟨.spath S' T, p'⟩ =>
      if h : S' = S then by subst h; exact do pure ⟨_, .app3 .saveIn s' p' (← v.check (.sv T) Γ)⟩
      else .error s!"`{p.text}` is a path under `{S'}`, written under `{S}`"
    | ⟨.st, _⟩, ⟨σ, _⟩ | ⟨.sts _, _⟩, ⟨σ, _⟩ => useError p.text σ "a storage path"
    | ⟨σ, _⟩, _ => useError s.text σ "a storage"

/-- `delAt(s, p)`, under a `select` too. -/
def NSTerm.delAt (s : NSTerm C) (p : NPTerm C) : NSTerm C :=
  syn s!"delAt({s.key}, {p.key})" s!"delAt({s.text}, {p.text})" fun Γ => do
    match ← s.resolve Γ, ← p.resolve Γ with
    | ⟨.st, s'⟩, ⟨.path _, p'⟩ => pure ⟨_, .app2 .delAt s' p'⟩
    | ⟨.sts S, s'⟩, ⟨.spath S' _, p'⟩ =>
      if h : S' = S then by subst h; exact pure ⟨_, .app2 .delAtIn s' p'⟩
      else .error s!"`{p.text}` is a path under `{S'}`, deleted under `{S}`"
    | ⟨.st, _⟩, ⟨σ, _⟩ | ⟨.sts _, _⟩, ⟨σ, _⟩ => useError p.text σ "a storage path"
    | ⟨σ, _⟩, _ => useError s.text σ "a storage"

/-- A push, `v` at the array's element type. -/
def NSTerm.push (s : NSTerm C) (p : NPTerm C) (v : NSValT C) : NSTerm C :=
  syn s!"push({s.key}, {p.key}, {v.key})" s!"push({s.text}, {p.text}, {v.text})" fun Γ => do
    let s' ← s.topStorage Γ
    let ⟨E, p'⟩ ← p.arrayPath Γ
    pure ⟨_, .app3 .push s' p' (← v.check (.sv E) Γ)⟩

/-- An array operation on a storage and a dynamic array's path. -/
def NSTerm.arrOp (name : String)
    (o : {E : Ty} → Op2 C .st (.path (.ref (.array E))) .st) (s : NSTerm C) (p : NPTerm C) :
    NSTerm C :=
  syn s!"{name}({s.key}, {p.key})" s!"{name}({s.text}, {p.text})" fun Γ => do
    let s' ← s.topStorage Γ
    let ⟨_, p'⟩ ← p.arrayPath Γ
    pure ⟨_, .app2 o s' p'⟩

def NSTerm.pushSlot (s : NSTerm C) (p : NPTerm C) : NSTerm C := NSTerm.arrOp "pushSlot" .pushSlot s p
def NSTerm.pop (s : NSTerm C) (p : NPTerm C) : NSTerm C := NSTerm.arrOp "pop" .pop s p
def NSTerm.shrink (s : NSTerm C) (p : NPTerm C) : NSTerm C := NSTerm.arrOp "shrink" .shrink s p
def NSTerm.extend (s : NSTerm C) (p : NPTerm C) : NSTerm C := NSTerm.arrOp "extend" .extend s p

/-- `select(s, r)`: the struct at the root `r`, or at the member `r` under
another `select`. -/
def NSTerm.select (s : NSTerm C) (r : Name) : NSTerm C :=
  syn s!"select {r}({s.key})" s!"select({s.text}, {r})" fun Γ => do
    match ← s.resolve Γ with
    | ⟨.st, s'⟩ =>
      match h : C.rootType r with
      | some (.ref (.struct _)) => pure ⟨_, .app1 (.select r h) s'⟩
      | _ => .error s!"`select(…, {r})`: `{r}` is no struct state variable"
    | ⟨.sts S, s'⟩ =>
      match h : C.fieldType S r with
      | some (.ref (.struct _)) => pure ⟨_, .app1 (.selectIn h) s'⟩
      | _ => .error s!"`select(…, {r})`: `{S}` has no struct member `{r}`"
    | ⟨σ, _⟩ => useError s.text σ "a storage"

/-- A value written to storage: checked at the value's type. -/
def NSValT.val (t : NTerm C) : NSValT C :=
  { key := s!"sval({t.key})", text := t.text
    resolve := fun Γ => do
      let ⟨_, t'⟩ ← t.resolveVal Γ
      pure ⟨_, .app1 .sval t'⟩
    checkAt? := some fun s Γ => match s with
      | .sv (.prim p) => do pure (.app1 .sval (← t.check (.val p) Γ))
      | s => do
        let ⟨p, _⟩ ← t.resolveVal Γ
        sortError t.text (.sv (.prim p)) s }

/-- `sfind(s, p)`, written `find(s, p)` where a storage value stands. -/
def NSValT.find (s : NSTerm C) (p : NPTerm C) : NSValT C :=
  syn s!"sfind({s.key}, {p.key})" s!"find({s.text}, {p.text})" fun Γ => do
    match ← s.resolve Γ, ← p.resolve Γ with
    | ⟨.st, s'⟩, ⟨.path _, p'⟩ => pure ⟨_, .app2 .sfind s' p'⟩
    | ⟨.sts S, s'⟩, ⟨.spath S' _, p'⟩ =>
      if h : S' = S then by subst h; exact pure ⟨_, .app2 .sfindIn s' p'⟩
      else .error s!"`{p.text}` is a path under `{S'}`, read under `{S}`"
    | ⟨.st, _⟩, ⟨σ, _⟩ | ⟨.sts _, _⟩, ⟨σ, _⟩ => useError p.text σ "a storage path"
    | ⟨σ, _⟩, _ => useError s.text σ "a storage"

def NSValT.copyMem (m : NMTerm C) (i : NITerm C) : NSValT C :=
  syn s!"copyMem({m.key}, {i.key})" s!"copyMem({m.text}, {i.text})" fun Γ => do
    let m' ← m.check .mem Γ
    match ← i.resolve Γ with
    | ⟨.ident _, i'⟩ => pure ⟨_, .app2 .copyMem m' i'⟩
    | ⟨σ, _⟩ => useError i.text σ "a memory reference"

def NSValT.newArr (R : RefTy) (n : NTerm C) : NSValT C :=
  syn s!"newArr {Ty.ref R}({n.key})" s!"newArr({Ty.ref R}, {n.text})" fun Γ => do
    if h : R.newArrOk = true then pure ⟨_, .app1 (.newArr h) (← n.check (.val .uint) Γ)⟩
    else .error s!"`newArr({Ty.ref R}, …)`: `{Ty.ref R}` is not allocated by `new`"

/-- A fixed array viewed at the destination type `R` it is copied to
(`Op1.fixedCopy`), written `fixedCopy(R, v)`: each conversion says its
destination, so a composed one (`uint[2]` to `uint[4]` to `uint[]`) reads
back as it was. -/
def NSValT.fixedCopy (R : RefTy) (v : NSValT C) : NSValT C :=
  syn s!"fixedCopy {Ty.ref R}({v.key})" s!"fixedCopy({Ty.ref R}, {v.text})" fun Γ => do
    match ← v.resolve Γ with
    | ⟨.sv (.ref (.fixed E n)), v'⟩ =>
      match FixedCopy.ofTarget E n R with
      | some c => pure ⟨_, .app1 (.fixedCopy c) v'⟩
      | none => .error s!"`fixedCopy({Ty.ref R}, …)`: a `{Ty.ref (.fixed E n)}` is not copied to a \
          `{Ty.ref R}`"
    | ⟨σ, _⟩ => useError v.text σ "a fixed-size array"

def NITerm.pv (x : Var) : NITerm C := .pvI x

/-- A reference read out of memory (`iread`). -/
def NITerm.read (m : NMTerm C) (a : NMAddr C) : NITerm C :=
  syn s!"iread({m.key}, {a.key})" (if m.key == "memory" then a.text else s!"read({m.text}, {a.text})")
    fun Γ => do
    let m' ← m.check .mem Γ
    match ← a.resolve Γ with
    | ⟨.addr (.ref _), a'⟩ => pure ⟨_, .app2 .iread m' a'⟩
    | ⟨σ, _⟩ => useError a.text σ "a memory location of a reference"

def NITerm.alloc (m : NMTerm C) (R : RefTy) : NITerm C :=
  syn s!"alloc {Ty.ref R}({m.key})" s!"freshId(addM({m.text}, {Ty.ref R}))" fun Γ => do
    if h : (Ty.ref R).mapFree = true then pure ⟨_, .app1 (.alloc R h) (← m.check .mem Γ)⟩
    else .error s!"`addM(m, {Ty.ref R})`: a mapping is not allocated in memory"

def NITerm.copy (m : NMTerm C) (v : NSValT C) : NITerm C :=
  syn s!"copy({m.key}, {v.key})" s!"freshId(copySt({m.text}, {v.text}))" fun Γ => do
    let m' ← m.check .mem Γ
    match ← v.resolve Γ with
    | ⟨.sv (.ref R), v'⟩ =>
      if h : (Ty.ref R).mapFree = true then pure ⟨_, .app2 (.copy h) m' v'⟩
      else .error s!"`{v.text}`: a `{Ty.ref R}` holds a mapping, which is not copied to memory"
    | ⟨σ, _⟩ => useError v.text σ "a storage value of a reference type"

/-- `i.f`, a member of a memory struct. -/
def NMAddr.field (i : NITerm C) (f : Name) : NMAddr C :=
  syn s!"mfield {f}({i.key})" s!"{i.text}.{f}" fun Γ => do
    match ← i.resolve Γ with
    | ⟨.ident (.struct s), i'⟩ =>
      let ⟨_, ⟨h⟩⟩ ← NTm.fieldOf (C := C) s f s!"{i.text}.{f}"
      pure ⟨_, .app1 (.mfield h) i'⟩
    | ⟨σ, _⟩ => useError i.text σ "a memory struct"

/-- `i[k]`, an element of a memory array. -/
def NMAddr.at (i : NITerm C) (k : NTerm C) : NMAddr C :=
  syn s!"mat({i.key}, {k.key})" s!"{i.text}[{k.text}]" fun Γ => do
    match ← i.resolve Γ with
    | ⟨.ident R, i'⟩ =>
      let some ⟨_, a⟩ := R.arrTy? | useError i.text (.ident R) "a memory array"
      pure ⟨_, .app2 (.mat a) i' (← k.check (.val .uint) Γ)⟩
    | ⟨σ, _⟩ => useError i.text σ "a memory array"

def NMTerm.memory : NMTerm C := NTm.app0 .memory "memory"

/-- `write(m, a, v)`, `v` checked at `a`'s type. -/
def NMTerm.write (m : NMTerm C) (a : NMAddr C) (v : NMValT C) : NMTerm C :=
  syn s!"write({m.key}, {a.key}, {v.key})" s!"write({m.text}, {a.text}, {v.text})" fun Γ => do
    let m' ← m.check .mem Γ
    match ← a.resolve Γ with
    | ⟨.addr T, a'⟩ => pure ⟨_, .app3 .write m' a' (← v.check (.mv T) Γ)⟩
    | ⟨σ, _⟩ => useError a.text σ "a memory location"

def NMTerm.addM (m : NMTerm C) (R : RefTy) : NMTerm C :=
  syn s!"addM {Ty.ref R}({m.key})" s!"addM({m.text}, {Ty.ref R})" fun Γ => do
    if h : (Ty.ref R).mapFree = true then pure ⟨_, .app1 (.addM R h) (← m.check .mem Γ)⟩
    else .error s!"`addM(m, {Ty.ref R})`: a mapping is not allocated in memory"

def NMTerm.copySt (m : NMTerm C) (v : NSValT C) : NMTerm C :=
  syn s!"copySt({m.key}, {v.key})" s!"copySt({m.text}, {v.text})" fun Γ => do
    let m' ← m.check .mem Γ
    match ← v.resolve Γ with
    | ⟨.sv T, v'⟩ =>
      if h : T.mapFree = true then pure ⟨_, .app2 (.copySt h) m' v'⟩
      else .error s!"`{v.text}`: a `{T}` holds a mapping, which is not copied to memory"
    | ⟨σ, _⟩ => useError v.text σ "a storage value"

/-- A value written to memory: checked at the location's type. -/
def NMValT.val (t : NTerm C) : NMValT C :=
  { key := s!"mval({t.key})", text := t.text
    resolve := fun Γ => do
      let ⟨_, t'⟩ ← t.resolveVal Γ
      pure ⟨_, .app1 .mval t'⟩
    checkAt? := some fun s Γ => match s with
      | .mv (.prim p) => do pure (.app1 .mval (← t.check (.val p) Γ))
      | s => do
        let ⟨p, _⟩ ← t.resolveVal Γ
        sortError t.text (.mv (.prim p)) s }

def NMValT.ref (i : NITerm C) : NMValT C :=
  syn s!"ref({i.key})" i.text fun Γ => do
    match ← i.resolve Γ with
    | ⟨.ident _, i'⟩ => pure ⟨_, .app1 .ref i'⟩
    | ⟨σ, _⟩ => useError i.text σ "a memory reference"

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
  | .val .., .val _ | .val .., .kint | .path .., .alias _ | .unset _, .alias _ | .mref .., .mem _
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
