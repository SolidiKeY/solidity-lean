import Solidity.Semantics.Agree

/-!
# Terms, updates, formulas

After a rule fires, the calculus talks about *terms* of the logic, not about
program expressions (mini-solkey's `Ch05_Logic`).  The sorts are KeY's:

* `Term` — a value: a constant, a stack local, `a + b`, `find(s, p)`,
  `read(m, a)`, the length of an array;
* `PTerm` — a storage path: a state variable, an alias, `p.f`, `p[i]`;
* `STerm` — a storage: the program variable `storage`, `save(s, p, v)`,
  `delAt(s, p)`, a push and a pop (KeY's nested `save`s over `size`);
* `ITerm`, `MAddr`, `MTerm` — a memory identity, a member or element of one,
  a memory: `memory`, `write(m, a, v)`, `addM(m)`, `copySt(m, v)`.

**Updates are terms.**  `{storage := save(storage, alice.age, 3)}` is a list
of elementary updates, applied in parallel: every right-hand side is read in
the state the update is applied in.  Nothing runs when a rule produces one.

A formula is first-order (`=`, `¬`, `∧`, `→`) plus `{U} φ` and the two
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

/-- A storage path. -/
inductive PTerm (C : Contract) where
  | root (r : Name)
  | pv (x : Var)
  | field (p : PTerm C) (f : Name)
  | at (p : PTerm C) (i : Term C)

/-- A storage. -/
inductive STerm (C : Contract) where
  | storage
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
  /-- The extent write of `lsv = p.push()`: `save(s, p.length, p.length + 1)`. -/
  | extend (s : STerm C) (p : PTerm C) (E : Ty)

/-- What a storage `save` writes: a value, a subtree read out of a storage,
or a memory object copied back (`copyMem(mtSt, m, i)`). -/
inductive SValT (C : Contract) where
  | val (t : Term C)
  | find (s : STerm C) (p : PTerm C)
  | copyMem (m : MTerm C) (i : ITerm C)

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
    | .array _ => .error .stuck
  | .memoryIndex id i => do
    match ← σ.getObj id with
    | .array elems =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then pure (elems.get ⟨i.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .stuck

/-- A write at a memory address. -/
def writeAddr (σ : State) (mv : MVal) : Addr → Res State
  | .memoryField id f => memWriteField σ id f mv
  | .memoryIndex id i => memWriteIndex σ id i mv

/-- The length of the array at a storage path. -/
def arrayLen (σ : State) (r : Name) (segs : List Seg) : Res Value := do
  match ← σ.findStorage r segs with
  | .array elems _ => pure (.int elems.length)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

mutual

def Term.eval (σ : State) : Term C → Res Value
  | .lit v => pure v
  | .pv x => do
    match ← σ.getEnv x with
    | .val v => pure v
    | .spath .. | .mref _ => .error .stuck
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

def PTerm.eval (σ : State) : PTerm C → Res (Name × List Seg)
  | .root r => pure (r, [])
  | .pv x => aliasPath σ x
  | .field p f => do
    let (r, segs) ← p.eval σ
    pure (r, segs ++ [.field f])
  | .at p i => do
    let (r, segs) ← p.eval σ
    let i ← (← i.eval σ).asInt
    pure (r, segs ++ [.at i])

def STerm.eval (σ : State) : STerm C → Res State
  | .storage => pure σ
  | .save s p v => do
    let sv ← v.eval σ
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    τ.saveStorage r segs sv
  | .delAt s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    let cur ← τ.findStorage r segs
    τ.saveStorage r segs cur.defaultOf
  | .push s p v => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    pushAt τ .uint r segs fun _ => v.eval σ
  | .pushSlot s p E => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    pushAt τ E r segs pure
  | .pop s p => do
    let τ ← s.eval σ
    let (r, segs) ← p.eval σ
    popAt τ r segs
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

def ITerm.eval (σ : State) : ITerm C → Res Nat
  | .pv x => do
    match ← σ.getEnv x with
    | .mref id => pure id
    | .val _ | .spath .. => .error .stuck
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

/-! ## Updates -/

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
  /-- `memory := m` -/
  | memory (m : MTerm C)
  /-- `transfer(r, a)`: KeY's `{selfBalance := selfBalance - a ‖ net := …}`,
  the pair that moves together. -/
  | transfer (r a : Term C)

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
  | .memory m, τ => do
    let μ ← m.eval σ₀
    pure { τ with heap := μ.heap, nextId := μ.nextId }
  | .transfer r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    transferAt τ addr amt

/-- The state an update leaves, from `σ`. -/
def Upd.apply (U : Upd C) (σ : State) : Res State :=
  U.foldlM (fun τ e => e.write σ τ) σ

/-! ## Formulas -/

/-- A formula about programs of the contract `C`. -/
inductive Fml (C : Contract) where
  | tt
  | eq (a b : Term C)
  | not (φ : Fml C)
  | and (φ ψ : Fml C)
  | imp (φ ψ : Fml C)
  /-- `{U} φ`, produced under the modality `m`. -/
  | upd (m : Modality) (U : Upd C) (φ : Fml C)
  /-- `⟨ P ⟩ φ` or `[ P ] φ`. -/
  | modal (m : Modality) (P : Prog C) (φ : Fml C)

instance : Inhabited (Fml C) := ⟨.tt⟩

/-- `false` is `¬true`. -/
abbrev Fml.ff : Fml C := .not .tt

/-- Whether `φ` holds in `σ`.  An equation holds when both sides are
defined and equal. -/
def holds (σ : State) : Fml C → Prop
  | .tt => True
  | .eq a b =>
    match a.eval σ, b.eval σ with
    | .ok x, .ok y => x = y
    | _, _ => False
  | .not φ => ¬ holds σ φ
  | .and φ ψ => holds σ φ ∧ holds σ ψ
  | .imp φ ψ => holds σ φ → holds σ ψ
  | .upd m U φ => m.after (holds · φ) (U.apply σ)
  | .modal m P φ => m.after (holds · φ) (Prog.run σ P)

/-- Valid: true in every state. -/
def Valid (φ : Fml C) : Prop := ∀ σ, holds σ φ


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

def PTerm.vars : PTerm C → List Var
  | .root _ => []
  | .pv x => [x]
  | .field p _ => p.vars
  | .at p i => p.vars ++ i.vars

def STerm.vars : STerm C → List Var
  | .storage => []
  | .save s p v | .push s p v => s.vars ++ p.vars ++ v.vars
  | .delAt s p | .pushSlot s p _ | .pop s p | .extend s p _ => s.vars ++ p.vars

def SValT.vars : SValT C → List Var
  | .val t => t.vars
  | .find s p => s.vars ++ p.vars
  | .copyMem m i => m.vars ++ i.vars

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
  | .memory m => m.vars
  | .transfer r a => r.vars ++ a.vars

def Upd.vars : Upd C → List Var
  | [] => []
  | e :: U => e.vars ++ Upd.vars U

/-- The variables a formula mentions, its programs' included. -/
def Fml.vars : Fml C → List Var
  | .tt => []
  | .eq a b => a.vars ++ b.vars
  | .not φ => φ.vars
  | .and φ ψ | .imp φ ψ => φ.vars ++ ψ.vars
  | .upd _ U φ => Upd.vars U ++ φ.vars
  | .modal _ P φ => Prog.vars P ++ φ.vars

section Frame

variable {ns : List Var}

theorem readAddr_congr {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (a : Addr) :
    readAddr σ a = readAddr τ a := by
  cases a <;> simp only [readAddr, getObj_congr hag]

theorem writeAddr_agree {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (mv : MVal) (a : Addr) :
    ResultsAgree ns (writeAddr σ mv a) (writeAddr τ mv a) := by
  cases a
  · exact memWriteField_agree hag _ _ _
  · exact memWriteIndex_agree hag _ _ _

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

theorem PTerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (p : PTerm C) → Avoids p.vars ns → p.eval σ = p.eval τ
  | .root _, _ => rfl
  | .pv x, h => aliasPath_frame hag (h.head)
  | .field p _, h => by simp only [PTerm.eval, p.eval_frame hag h]
  | .at p i, h => by simp only [PTerm.eval, p.eval_frame hag h.left, i.eval_frame hag h.right]

theorem STerm.eval_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (s : STerm C) → Avoids s.vars ns → ResultsAgree ns (s.eval σ) (s.eval τ)
  | .storage, _ => hag
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
    exact v.eval_frame hag h.right
  | .pushSlot s p _, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    exact bindPureResults_agree _ fun _ => pushAt_agree h' _ _ _ fun _ => rfl
  | .pop s p, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    agree_run h'
  | .extend s p _, h => by
    simp only [STerm.eval, p.eval_frame hag h.right]
    refine ResultsAgree.bind (s.eval_frame hag h.left) fun _ _ h' => ?_
    refine bindPureResults_agree _ fun _ => ?_
    exact ResAgree.bindState (pushPlaceAt_agree h' _ _ _) fun _ _ _ h'' => h''

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
    | .ok a, .ok b, hs => exact ⟨hs.storage, h.heap, h.nextId, h.net, h.env, h.selfBalance⟩
  | .memory m, hv => by
    simp only [UpdElem.write]
    match m.eval σ₀, m.eval σ₀', m.eval_frame h₀ hv with
    | .error _, .error _, he => subst he; rfl
    | .ok a, .ok b, hs => exact ⟨h.storage, hs.heap, hs.nextId, h.net, h.env, h.selfBalance⟩
  | .transfer r a, hv => by
    simp only [UpdElem.write, r.eval_frame h₀ hv.left, a.eval_frame h₀ hv.right]
    agree_run h

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
    simp only [holds, a.eval_frame hag h.left, b.eval_frame hag h.right]
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

end Frame

/-! ## Lowering program expressions to terms

A value position lowers with `lower`, a path position with `lowerPath`, once,
at the rule (Maude's `lower(LV, C)`).  Lowering keeps meaning:
`lower_eval` below. -/

def Simple.lower {p : PrimTy} : Simple C p → Term C
  | .lit n _ => .lit (.int n)
  | .bool b => .lit (.bool b)
  | .local x => .pv x

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
  | _, .index b i => .at b.lower i.lower

def Val.lower : {p : PrimTy} → Val C p → Term C
  | _, .simple s => s.lower
  | _, .read l => .find .storage l.lower
  | _, @Val.binop _ p _ op _ _ a b => .binop op p a.lower b.lower
  | _, @Val.unop _ p _ op _ _ a => .unop op p a.lower
  | _, .ternary c a b => .ite c.lower a.lower b.lower
  | _, .readMem l => .read .memory l.lower

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
  | _, .index b i => by
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

end

end Solidity
