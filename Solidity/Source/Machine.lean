import Solidity.Source.Value
import Solidity.Source.World
import Solidity.Source.Elaborated

/-!
# The source machine: state, locals and storage access (S02)

What S02's expression semantics and S03's statement semantics run on,
over S04.01–S04.03's state:

- `Env.layout`: the declaration layout read off the environment (struct
  members in memory, enum sizes, underlying types);
- `Env.cellTy`: the logical storage layout, the type each `SPath` holds.  A
  value-type variable or element holds its value; a dynamic array, `bytes`
  or `string` holds its length at its own path and its elements at
  `index` steps below; a struct its members at `field` steps; a mapping
  its values at `key` steps (the key's contents).  Paths that name an
  aggregate hold nothing (`tuple []`, which has no value).  This is the
  logical aliasing of G04 Q2; the physical packing is not observable;
- `Locals D Γ`: the values of a body's locals, intrinsic in their types;
- `St E`: the journaled world and transient storage (`ExecState`), the
  frame's memory (`Heap`), the observable events so far (G01 `Event`), the
  logs (an excluded observation, kept so that they roll back), and the
  function frame whose modifiers are running;
- `EM E Γ`: the evaluation monad, locals and state threaded, a `Halt`
  keeping the state (events already emitted stay emitted);
- the storage, memory and conversion operations every expression form
  uses: typed reads (`readAt`), journaled writes refused in a static frame
  (`writeCell`), copies from storage to memory (`loadMem`) and back
  (`storeData`), deletion (`deleteStor`), zeroed memory objects
  (`zeroData`).
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes Event Outcome Pipeline Strategy Fixed)

/-! ## Layouts -/

/-- The declaration layout of an environment. -/
def Env.layout (E : Env) : Layout where
  fields d := ((E.structFields d .memory).getD []).map Prod.snd
  enumSize d :=
    match E.declOf .enum d with
    | some ⟨.enum, _, _, _, .enum _ _ rest⟩ => rest.length + 1
    | _ => 0
  underlying d :=
    match E.declOf .udvt d with
    | some ⟨.udvt, _, _, _, .udvt _ el⟩ => el.ty .memory
    | _ => .bool

/-- The declared type of a state variable named by a path's root. -/
def Env.rootTy (E : Env) (root : DeclName) : Option STy :=
  (E.declOf .stateVar root).bind (·.varTy E)

/-- Whether a state variable is `transient`. -/
def Decl.isTransient (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar _ _ _ _ tr _ _ => tr
  | _, _, _ => false

/-- The type below a step. -/
def Env.stepTy (E : Env) : STy → Step → Option STy
  | .array _ τ _, .index _ => some τ
  | .bytes _, .index _ | .string _, .index _ => some (.fixedBytes 1 (by decide))
  | .struct _ d, .field i => E.fieldTy? d .storage i
  | .mapping _ v, .key _ => some v
  | _, _ => none

/-- The declared type at a path. -/
def Env.pathTy (E : Env) (p : SPath) : Option STy :=
  p.steps.foldl (fun o s => o.bind (E.stepTy · s)) (E.rootTy p.root)

/-- What a storage cell of declared type `τ` holds: the value, or the
length of a dynamic array, `bytes` or `string`, or nothing. -/
def STy.cell : STy → STy
  | .array _ _ none | .bytes _ | .string _ => .int IntTy.u256
  | τ => if τ.isValue then τ else .tuple []

/-- **The logical storage layout**: the type each path holds. -/
def Env.cellTy (E : Env) (p : SPath) : STy := ((E.pathTy p).map STy.cell).getD (.tuple [])

/-- The layout of every instance's storage and transient storage. -/
abbrev Env.lay (E : Env) : Address → SPath → STy := fun _ => E.cellTy

/-! ## Locals -/

/-- The values of a context's locals. -/
inductive Locals (D : Layout) : RCtx → Type where
  | nil : Locals D []
  | cons {τ : STy} {Γ : RCtx} (v : Val D τ) (rest : Locals D Γ) : Locals D (τ :: Γ)

/-- Values of a list of types (parameters, returns). -/
inductive Vals (D : Layout) : List STy → Type where
  | nil : Vals D []
  | cons {τ : STy} {τs : List STy} (v : Val D τ) (rest : Vals D τs) : Vals D (τ :: τs)

namespace Locals

variable {D : Layout}

def get : {Γ : RCtx} → {τ : STy} → Locals D Γ → Idx Γ τ → Val D τ
  | _, _, .cons v _, .here => v
  | _, _, .cons _ r, .there i => r.get i

def set : {Γ : RCtx} → {τ : STy} → Locals D Γ → Idx Γ τ → Val D τ → Locals D Γ
  | _, _, .cons _ r, .here, v => .cons v r
  | _, _, .cons x r, .there i, v => .cons x (r.set i v)

/-- The locals without the `k` innermost. -/
def drop : (k : Nat) → {Γ : RCtx} → Locals D Γ → Locals D (Γ.drop k)
  | 0, _, l => l
  | _ + 1, _, .nil => .nil
  | k + 1, _, .cons _ r => r.drop k

/-- **The end of a scope**: the locals of an enclosing context `Γ`, which
the inner context `Γ'` extends. -/
def restore {Γ' : RCtx} (l : Locals D Γ') (Γ : RCtx) : R (Locals D Γ) :=
  if h : Γ'.drop (Γ'.length - Γ.length) = Γ then pure (h ▸ l.drop (Γ'.length - Γ.length))
  else stuck "scope"

/-- The `k`-th local at type `τ`. -/
def getAt : (k : Nat) → {Γ : RCtx} → Locals D Γ → (τ : STy) → R (Val D τ)
  | 0, _, .cons (τ := σ) v _, τ => if h : σ = τ then pure (h ▸ v) else stuck "local type"
  | k + 1, _, .cons _ r, τ => r.getAt k τ
  | _, _, .nil, _ => stuck "no local"

/-- Writing the `k`-th local at type `τ`. -/
def setAt : (k : Nat) → {Γ : RCtx} → Locals D Γ → {τ : STy} → Val D τ → R (Locals D Γ)
  | 0, _, .cons (τ := σ) _ r, τ, v => if h : τ = σ then pure (.cons (h ▸ v) r) else stuck "local type"
  | k + 1, _, .cons x r, _, v => do pure (.cons x (← r.setAt k v))
  | _, _, .nil, _, _ => stuck "no local"

/-- The `k` innermost locals of `a` over the others of `b` (via-IR
modifier slots: current returns, original parameters). -/
def mix : (k : Nat) → {Γ : RCtx} → Locals D Γ → Locals D Γ → Locals D Γ
  | 0, _, _, b => b
  | _ + 1, _, .nil, _ => .nil
  | k + 1, _, .cons x r, .cons _ r' => .cons x (mix k r r')

end Locals

/-- Values pushed onto locals, the first innermost-last: parameters in
order, then the next. -/
def Vals.onto {D : Layout} : {τs : List STy} → Vals D τs → {Γ : RCtx} → Locals D Γ →
    Locals D (τs.reverseAux Γ)
  | _, .nil, _, l => l
  | _, .cons v vs, _, l => vs.onto (.cons v l)

/-! ## State -/

/-- **The machine state**: world, transient storage and journal; the
frame's memory; the events and logs so far; the locals of the function
whose modifiers run. -/
structure St (E : Env) where
  ex : ExecState E.layout E.lay E.lay
  heap : Heap E.layout
  /-- The observable events, oldest first. -/
  events : List Event
  /-- Emitted logs (an excluded observation, G00), newest first. -/
  logs : List (Address × Bytes)
  fnLocals : Σ Γ : RCtx, Locals E.layout Γ

/-- **A call frame's context**. -/
structure Fr where
  this : Address
  sender : Address
  value : Word
  static : Bool
  /-- The most derived contract of `this` (virtual dispatch). -/
  contract : String
  checked : Bool := true
  depth : Nat := 0

/-- **What every execution reads**: the program, the pipeline, the fixed
parameters (hash, precompiles, ledger, creation addresses), the session's
opening balances and callee strategy, and the block's timestamp. -/
structure Glob (E : Env) where
  prog : Program E
  pipeline : Pipeline
  fixed : Fixed
  balance0 : Address → Word
  /-- Whether an account outside the system has code after a history. -/
  hasCode : List Event → Address → Bool
  callee : Strategy
  timestamp : Word

/-- **The evaluation monad**: locals and state threaded; a halt keeps the
state. -/
abbrev EM (E : Env) (Γ : RCtx) := ExceptT Halt (StateM (Locals E.layout Γ × St E))

namespace EM

variable {E : Env} {Γ : RCtx}

def halt {α : Type} (h : Halt) : EM E Γ α := throw h

def lift {α : Type} (r : R α) : EM E Γ α :=
  match r with
  | .ok a => pure a
  | .error h => throw h

def st : EM E Γ (St E) := do return (← get).2
def setSt (s : St E) : EM E Γ Unit := modify fun x => (x.1, s)
def modSt (f : St E → St E) : EM E Γ Unit := modify fun x => (x.1, f x.2)
def locals : EM E Γ (Locals E.layout Γ) := do return (← get).1
def setLocals (l : Locals E.layout Γ) : EM E Γ Unit := modify fun x => (l, x.2)

/-- Running a computation over other locals: its result and final locals,
the state passed through (a halt keeps the state). -/
def sub {Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') (m : EM E Γ' α) :
    EM E Γ (α × Locals E.layout Γ') :=
  ExceptT.mk fun (l, s) =>
    match (m.run (l', s)) with
    | (.ok a, (l'', s')) => (.ok (a, l''), (l, s'))
    | (.error h, (_, s')) => (.error h, (l, s'))

/-- Catching a halt. -/
def attempt {α : Type} (m : EM E Γ α) : EM E Γ (Except Halt α) :=
  ExceptT.mk fun x =>
    match m.run x with
    | (r, x') => (.ok r, x')

end EM

open EM

variable {E : Env}

/-- A plain `Val` from a run-time value. -/
def getV {Γ : RCtx} {τ : STy} (v : RVal E.layout τ) : EM E Γ (Val E.layout τ) := lift v.get

/-- Run-time values as values. -/
def RVals.toVals {D : Layout} : {τs : List STy} → RVals D τs → R (Vals D τs)
  | _, .nil => pure .nil
  | _, .cons v vs => do pure (.cons (← v.get) (← vs.toVals))

/-- Values as run-time values. -/
def Vals.toR {D : Layout} : {τs : List STy} → Vals D τs → RVals D τs
  | _, .nil => .nil
  | _, .cons v vs => .cons (.val v) vs.toR

/-! ## Storage -/

/-- The path of a state variable. -/
def Decl.path (d : Decl) : SPath := ⟨⟨d.scope, d.name⟩, []⟩

/-- A path one step down. -/
def SPath.go (p : SPath) (s : Step) : SPath := ⟨p.root, p.steps ++ [s]⟩

/-- Whether a path is in transient storage. -/
def Env.transientRoot (E : Env) (p : SPath) : Bool :=
  ((E.declOf .stateVar p.root).map Decl.isTransient).getD false

/-- **Reading a cell**: the written value, or its type's default. -/
def readCell {Γ : RCtx} (F : Fr) (p : SPath) : EM E Γ (Val E.layout (E.cellTy p)) := do
  let s ← st
  let o :=
    if E.transientRoot p then (s.ex.transient.cells F.this).read p
    else (s.ex.world.accounts F.this).storage.read p
  match o with
  | some v => pure v
  | none => halt (.stuck "storage cell without a value")

/-- A typed read of a cell. -/
def readAt {Γ : RCtx} (F : Fr) (p : SPath) (τ : STy) : EM E Γ (Val E.layout τ) := do
  let v ← readCell F p
  if h : E.cellTy p = τ then pure (h ▸ v) else halt (.stuck "storage cell type")

/-- An operation on the state, refused (a revert with no data) in a static
frame. -/
def applyOp {Γ : RCtx} (F : Fr) (o : Op E.layout E.lay E.lay) : EM E Γ Unit := do
  if F.static then halt (.revert [])
  modSt fun s => { s with ex := s.ex.apply o }

/-- **Writing a cell** (`none` resets it to the default), journaled. -/
def setCell {Γ : RCtx} (F : Fr) (p : SPath) (o : Option (Val E.layout (E.cellTy p))) : EM E Γ Unit :=
  if E.transientRoot p then applyOp F (.transient F.this fun st => st.set p o)
  else applyOp F (.account F.this fun a => { a with storage := a.storage.set p o })

/-- A typed write of a cell. -/
def writeAt {Γ : RCtx} {τ : STy} (F : Fr) (p : SPath) (v : Val E.layout τ) : EM E Γ Unit :=
  if h : τ = E.cellTy p then setCell F p (some (h ▸ v)) else halt (.stuck "storage cell type")

/-- The length of a dynamic array, `bytes` or `string` in storage. -/
def readLen {Γ : RCtx} (F : Fr) (p : SPath) : EM E Γ Nat := do
  match ← readAt F p (.int IntTy.u256) with
  | .int v _ => pure v.toNat

/-- Writing a length. -/
def writeLen {Γ : RCtx} (F : Fr) (p : SPath) (n : Nat) : EM E Γ Unit := do
  writeAt F p (intWrap (D := E.layout) IntTy.u256 n)

/-! ## Memory -/

/-- The object at an address, at its own type. -/
def heapObj {Γ : RCtx} (a : Nat) : EM E Γ (Σ τ, Data E.layout τ) := do
  match (← st).heap.get a with
  | some x => pure x
  | none => halt (.stuck "dangling memory reference")

/-- The object at an address at type `τ`. -/
def heapAt {Γ : RCtx} (a : Nat) (τ : STy) : EM E Γ (Data E.layout τ) := do
  let ⟨σ, x⟩ ← heapObj a
  if h : σ = τ then pure (h ▸ x) else halt (.stuck "memory object type")

/-- The bytes of a `bytes` or `string` object (either reading). -/
def heapBytes {Γ : RCtx} (a : Nat) : EM E Γ (List UInt8) := do
  match ← heapObj a with
  | ⟨_, .bytes bs⟩ | ⟨_, .string bs⟩ => pure bs
  | _ => halt (.stuck "not a bytes object")

/-- Replacing the object at an address (at its own type). -/
def heapPut {Γ : RCtx} (a : Nat) (x : Σ τ, Data E.layout τ) : EM E Γ Unit := do
  let s ← st
  if h : s.heap.ty a = some x.1 then setSt { s with heap := s.heap.write a x.2 h }
  else halt (.stuck "memory write type")

/-- **Allocation** of a new object. -/
def alloc {Γ : RCtx} {τ : STy} (x : Data E.layout τ) : EM E Γ Nat := do
  let s ← st
  let (h, a) := s.heap.alloc ⟨τ, x⟩
  setSt { s with heap := h }
  pure a

/-- A `memory` reference to a new object. -/
def allocRef {Γ : RCtx} {τ : STy} (x : Data E.layout τ) : EM E Γ (Val E.layout τ) := do
  let a ← alloc x
  if h : τ.loc? = some .memory then pure (.memRef h a) else halt (.stuck "memory reference type")

/-- A `storage` reference to a path. -/
def storRef {Γ : RCtx} (τ : STy) (p : SPath) : EM E Γ (Val E.layout τ) :=
  if h : τ.loc? = some .storage then pure (.storRef h p) else halt (.stuck "storage reference type")

/-- An array's elements from a function of positions. -/
def finCons {α : Type} {k : Nat} (x : α) (f : Fin k → α) : Fin (k + 1) → α :=
  fun i => if h : i.val = 0 then x else f ⟨i.val - 1, by have := i.isLt; omega⟩

/-- The `i`-th element of a list of fields. -/
def DataList.nth {D : Layout} : {τs : List STy} → DataList D τs → (i : Nat) → (τ : STy) → R (Data D τ)
  | _, .nil, _, _ => stuck "no field"
  | _, .cons (τ := σ) x _, 0, τ => if h : σ = τ then pure (h ▸ x) else stuck "field type"
  | _, .cons _ r, i + 1, τ => r.nth i τ

/-- Replacing the `i`-th field. -/
def DataList.setNth {D : Layout} : {τs : List STy} → DataList D τs → (i : Nat) → {τ : STy} → Data D τ →
    R (DataList D τs)
  | _, .nil, _, _, _ => stuck "no field"
  | _, .cons (τ := σ) _ r, 0, τ, y => if h : τ = σ then pure (.cons (h ▸ y) r) else stuck "field type"
  | _, .cons x r, i + 1, _, y => do pure (.cons x (← r.setNth i y))

/-- A value stored inside a memory aggregate as an element. -/
def Data.asVal {D : Layout} {τ : STy} : Data D τ → R (Val D τ)
  | .val v => pure v
  | _ => stuck "inline aggregate element"

mutual

/-- **A zeroed memory object** of type `τ` (nested aggregates allocated
and pointed to): a declaration without an initializer, `delete`. -/
def zeroData {Γ : RCtx} : Nat → (τ : STy) → EM E Γ (Data E.layout τ)
  | 0, _ => halt .timeout
  | n + 1, τ =>
    match τ with
    | .bytes _ => pure (.bytes [])
    | .string _ => pure (.string [])
    | .array _ σ none => pure (.array 0 (fun _ h => nomatch h) Fin.elim0)
    | .array _ σ (some m) => do
      let xs ← zeroElems n σ m
      pure (.array m (fun _ h => by cases h; rfl) xs)
    | .struct _ d => do pure (.struct (← zeroFields n (E.layout.fields d)))
    | τ => do pure (.val (← zeroVal n τ))

/-- A zeroed element: a value, or a pointer to a new zeroed object. -/
def zeroVal {Γ : RCtx} : Nat → (τ : STy) → EM E Γ (Val E.layout τ)
  | 0, _ => halt .timeout
  | n + 1, τ =>
    match Val.default E.layout τ with
    | some v => pure v
    | none => do
      if τ.loc? = some .memory then allocRef (← zeroData n τ)
      else halt (.stuck "no default value")

def zeroElems {Γ : RCtx} : Nat → (σ : STy) → (m : Nat) → EM E Γ (Fin m → Data E.layout σ)
  | 0, _, _ => halt .timeout
  | _, _, 0 => pure Fin.elim0
  | n + 1, σ, m + 1 => do
    let x ← zeroVal n σ
    let f ← zeroElems n σ m
    pure (finCons (.val x) f)

def zeroFields {Γ : RCtx} : Nat → (τs : List STy) → EM E Γ (DataList E.layout τs)
  | 0, _ => halt .timeout
  | _, [] => pure .nil
  | n + 1, τ :: τs => do
    let x ← zeroVal n τ
    pure (.cons (.val x) (← zeroFields n τs))

end

/-- Whether a type is held by reference (its value a pointer). -/
def STy.byRef (τ : STy) : Bool := τ.loc?.isSome

mutual

/-- **Copying from storage to memory**: the contents at path `p` as a
memory object of type `τ`, nested aggregates allocated. -/
def loadMem {Γ : RCtx} (F : Fr) : Nat → (τ : STy) → SPath → EM E Γ (Data E.layout τ)
  | 0, _, _ => halt .timeout
  | n + 1, τ, p =>
    match τ with
    | .bytes _ => do pure (.bytes (← loadBytes F n p 0 (← readLen F p)))
    | .string _ => do pure (.string (← loadBytes F n p 0 (← readLen F p)))
    | .array _ σ none => do
      let len ← readLen F p
      pure (.array len (fun _ h => nomatch h) (← loadElems F n σ p 0 len))
    | .array _ σ (some m) => do
      pure (.array m (fun _ h => by cases h; rfl) (← loadElems F n σ p 0 m))
    | .struct _ d => do pure (.struct (← loadFields F n (E.layout.fields d) p 0))
    | .mapping _ _ => halt (.stuck "a mapping is not copied")
    | τ => do pure (.val (← readAt F p τ))

/-- An element: a value read, or a pointer to a new copy. -/
def loadElem {Γ : RCtx} (F : Fr) : Nat → (τ : STy) → SPath → EM E Γ (Val E.layout τ)
  | 0, _, _ => halt .timeout
  | n + 1, τ, p =>
    if τ.byRef then do allocRef (← loadMem F n τ p) else readAt F p τ

def loadElems {Γ : RCtx} (F : Fr) : Nat → (σ : STy) → SPath → Nat → (m : Nat) →
    EM E Γ (Fin m → Data E.layout σ)
  | 0, _, _, _, _ => halt .timeout
  | _, _, _, _, 0 => pure Fin.elim0
  | n + 1, σ, p, i, m + 1 => do
    let x ← loadElem F n σ (p.go (.index i))
    let f ← loadElems F n σ p (i + 1) m
    pure (finCons (.val x) f)

def loadFields {Γ : RCtx} (F : Fr) : Nat → (τs : List STy) → SPath → Nat → EM E Γ (DataList E.layout τs)
  | 0, _, _, _ => halt .timeout
  | _, [], _, _ => pure .nil
  | n + 1, τ :: τs, p, i => do
    let x ← loadElem F n τ (p.go (.field i))
    pure (.cons (.val x) (← loadFields F n τs p (i + 1)))

def loadBytes {Γ : RCtx} (F : Fr) : Nat → SPath → Nat → Nat → EM E Γ (List UInt8)
  | 0, _, _, _ => halt .timeout
  | _, _, _, 0 => pure []
  | n + 1, p, i, k + 1 => do
    match ← readAt F (p.go (.index i)) (.fixedBytes 1 (by decide)) with
    | .fixedBytes bs _ => pure ((bs.headD 0) :: (← loadBytes F n p (i + 1) k))

end

mutual

/-- **Deleting storage**: every value below `p` reset to its default
(mappings are not cleared, as in solc). -/
def deleteStor {Γ : RCtx} (F : Fr) : Nat → (τ : STy) → SPath → EM E Γ Unit
  | 0, _, _ => halt .timeout
  | n + 1, τ, p =>
    match τ with
    | .bytes _ | .string _ => do
      deleteRange F n (.fixedBytes 1 (by decide)) p 0 (← readLen F p)
      setCell F p none
    | .array _ σ none => do
      deleteRange F n σ p 0 (← readLen F p)
      setCell F p none
    | .array _ σ (some m) => deleteRange F n σ p 0 m
    | .struct _ d => deleteFields F n (((E.structFields d .storage).getD []).map Prod.snd) p 0
    | .mapping _ _ => pure ()
    | _ => setCell F p none

def deleteRange {Γ : RCtx} (F : Fr) : Nat → (σ : STy) → SPath → Nat → Nat → EM E Γ Unit
  | 0, _, _, _, _ => halt .timeout
  | _, _, _, _, 0 => pure ()
  | n + 1, σ, p, i, k + 1 => do
    deleteStor F n σ (p.go (.index i))
    deleteRange F n σ p (i + 1) k

def deleteFields {Γ : RCtx} (F : Fr) : Nat → List STy → SPath → Nat → EM E Γ Unit
  | 0, _, _, _ => halt .timeout
  | _, [], _, _ => pure ()
  | n + 1, τ :: τs, p, i => do
    deleteStor F n τ (p.go (.field i))
    deleteFields F n τs p (i + 1)

end

mutual

/-- **Copying into storage**: the contents `x` (of a memory or literal
type `σ`) written below the storage path `p` of type `τ`; elements past a
shorter new length are deleted, as solc does. -/
def storeData {Γ : RCtx} (F : Fr) : Nat → (τ : STy) → SPath → {σ : STy} → Data E.layout σ → EM E Γ Unit
  | 0, _, _, _, _ => halt .timeout
  | n + 1, τ, p, _, x =>
    match τ, x with
    | .bytes _, .bytes bs | .bytes _, .string bs | .string _, .bytes bs | .string _, .string bs => do
      let old ← readLen F p
      storeBytes F n p 0 bs
      deleteRange F n (.fixedBytes 1 (by decide)) p bs.length (old - bs.length)
      writeLen F p bs.length
    | .array _ τe none, .array len _ xs => do
      let old ← readLen F p
      storeElems F n τe p 0 len xs
      deleteRange F n τe p len (old - len)
      writeLen F p len
    | .array _ τe (some _), .array len _ xs => storeElems F n τe p 0 len xs
    | .struct _ d, .struct fs => storeFields F n (((E.structFields d .storage).getD []).map Prod.snd) p 0 fs
    | τ, .val v => storeVal F n τ p v
    | _, _ => halt (.stuck "copy into storage")

/-- An element: a value written, or the object a pointer names copied. -/
def storeVal {Γ : RCtx} (F : Fr) : Nat → (τ : STy) → SPath → {σ : STy} → Val E.layout σ → EM E Γ Unit
  | 0, _, _, _, _ => halt .timeout
  | n + 1, τ, p, _, v =>
    match v with
    | .memRef _ a => do
      let ⟨_, y⟩ ← heapObj a
      storeData F n τ p y
    | .storRef _ q => do
      if q = p then pure ()
      else storeData F n τ p (← loadMem F n (τ.withLoc .memory) q)
    | v => writeAt F p v

def storeElems {Γ : RCtx} (F : Fr) : Nat → (τ : STy) → SPath → Nat → (len : Nat) → {σ : STy} →
    (Fin len → Data E.layout σ) → EM E Γ Unit
  | 0, _, _, _, _, _, _ => halt .timeout
  | _, _, _, _, 0, _, _ => pure ()
  | n + 1, τ, p, i, len + 1, _, xs => do
    storeData F n τ (p.go (.index i)) (xs ⟨0, by omega⟩)
    storeElems F n τ p (i + 1) len (fun j => xs ⟨j.val + 1, by omega⟩)

def storeFields {Γ : RCtx} (F : Fr) : Nat → List STy → SPath → Nat → {σs : List STy} →
    DataList E.layout σs → EM E Γ Unit
  | 0, _, _, _, _, _ => halt .timeout
  | _, [], _, _, _, _ => pure ()
  | _, _ :: _, _, _, _, .nil => pure ()
  | n + 1, τ :: τs, p, i, _, .cons x xs => do
    storeData F n τ (p.go (.field i)) x
    storeFields F n τs p (i + 1) xs

def storeBytes {Γ : RCtx} (F : Fr) : Nat → SPath → Nat → List UInt8 → EM E Γ Unit
  | 0, _, _, _ => halt .timeout
  | _, _, _, [] => pure ()
  | n + 1, p, i, b :: bs => do
    writeAt F (p.go (.index i)) (Val.fixedBytes (D := E.layout) (n := 1) (h := by decide) [b] rfl)
    storeBytes F n p (i + 1) bs

end

end Solidity.Source
