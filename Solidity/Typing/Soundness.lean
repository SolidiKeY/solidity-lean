import Solidity.Typing.State

/-!
# Type soundness: `Stmt.run` keeps the state well-typed

The typed syntax already rules out every *static* mismatch the old
checker looked for: a member exists, an operator takes its operand, a copy
holds no mapping, a pushed default is well-formed.  What it cannot see is
the **locals**: `Var`s are not typed by the syntax (so a rule can declare
fresh ones without re-typing the program), and `Simple.local x` may be
written at `uint` in one place and at `bool` in another.  So what is left to
check is exactly the locals context, and that is all `Stmt.wt` does: it
threads a `Ctx` through the block — a declaration extends it, every use of
a local must agree with it — and returns the context the statement leaves.

`RunWT C Γ H σ` is the invariant, `StateWT` (`Typing/State.lean`) adapted
to the typed syntax in one respect: it drops `envTypedB`'s ban on bindings
`Γ` does not track.  That ban protected the old resolver, which looked a
name up in the environment before falling back to a storage root; here an
alias and a root are different constructors, so an untracked binding is
never read, and dropping the ban is what lets a branch of an `if` declare
a local the join then forgets (`StateWT.toRunWT` recovers the new
invariant from the old one).

The headline is `Stmt.run_wt`/`Prog.run_wt`: a checked statement run from
a `RunWT` state ends, if it ends in a state, in a `RunWT` state under the
context the check returned and a store typing that only grew (a memory
allocation adds claims).  A halt (`revert`, `stuck`) is a run the theorem
says nothing about, as there is no state to type.

The proof goes one evaluator at a time, in the order `Semantics.lean`
defines them: the paths resolve to a place the layout types at the path's
type (`Loc.resolve_wt`), the memory reads find a slot of the path's type
(`MLoc.read_wt`), a value evaluates to one of its type (`Val.eval_wt`),
and each statement's write stores what the place holds.
-/

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne HeapWellFormed
  lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## The layout a contract declares -/

/-- The storage layout of `C`: its roots at their declared types.  A root's
type is `C.rootType`, and one step down is `segTy`, which reads the same
`structDef` as `C.fieldType`. -/
def Contract.layout (C : Contract) : Layout := ⟨C.vars⟩

/-- `alice` in `StandardExample` has type `Person` in the layout, as
declared. -/
theorem Contract.layout_tyAt_root {C : Contract} {r : Name} {T : Ty}
    (h : C.rootType r = some T) : C.layout.tyAt r [] = some T := by
  simp only [Layout.tyAt, Contract.layout]
  rw [show lookupBy r C.vars = some T from h]
  rfl

/-! ## The locals check -/

/-- A context sees at least what another sees: every local `Γ` binds is
bound the same way in `Γ'`.  After `if (c) { uint y = 1; } else { }` the
branch's context is `Γ` plus `y`, which is `≥ Γ`. -/
def Ctx.le (Γ Γ' : Ctx) : Bool :=
  Γ.all fun g => lookupBy g.1 Γ' == lookupBy g.1 Γ

/-- A local the smaller context binds, the larger binds the same way: `y`
of `uint y;` before the branch is `uint` in it. -/
theorem Ctx.le_lookup {Γ Γ' : Ctx} {x : Var} {bt : BTy} (hle : Ctx.le Γ Γ' = true)
    (h : lookupBy x Γ = some bt) : lookupBy x Γ' = some bt := by
  have hmem := lookupBy_eq_some_mem h
  have := List.all_eq_true.mp hle _ hmem
  simp only [beq_iff_eq] at this
  rw [this, h]

/-- A simple value's local, if any, is a stack local of its type:
`x` read as a `uint` needs `uint x` in `Γ`. -/
def Simple.wt (Γ : Ctx) : {p : PrimTy} → Simple C p → Bool
  | p, .local x => lookupBy x Γ == some (.stack (.prim p))
  | _, .lit .. => true
  | _, .bool _ => true
  | _, .env .. => true

mutual

/-- Every local a storage path mentions is bound as it is used: `p.age`
needs `Person storage p` in `Γ`. -/
def SPath.wt (Γ : Ctx) : {T : Ty} → SPath C T → Bool
  | _, @SPath.alias _ R x => lookupBy x Γ == some (.path (.ref R))
  | _, .loc l => l.wt Γ

/-- `alice.age` has no locals; `balances[i]` needs `i` at the key type. -/
def Loc.wt (Γ : Ctx) : {T : Ty} → Loc C T → Bool
  | _, .root .. => true
  | _, .field b _ _ => b.wt Γ
  | _, .index _ b i => b.wt Γ && i.wt Γ

/-- `m.age` needs `Person memory m` in `Γ`. -/
def MPath.wt (Γ : Ctx) : {T : Ty} → MPath C T → Bool
  | _, @MPath.var _ R x => lookupBy x Γ == some (.mem (.ref R))
  | _, .loc l => l.wt Γ

/-- `ns[i]` needs `ns` a memory array and `i` a `uint` local. -/
def MLoc.wt (Γ : Ctx) : {T : Ty} → MLoc C T → Bool
  | _, .field b _ _ => b.wt Γ
  | _, .index _ b i => b.wt Γ && i.wt Γ

/-- `x + alice.age` needs `x` a `uint`. -/
def Val.wt (Γ : Ctx) : {p : PrimTy} → Val C p → Bool
  | _, .simple s => s.wt Γ
  | _, .read l => l.wt Γ
  | _, .binop _ _ _ a b => a.wt Γ && b.wt Γ
  | _, .unop _ _ _ a => a.wt Γ
  | _, .ternary c a b => c.wt Γ && a.wt Γ && b.wt Γ
  | _, .readMem l => l.wt Γ
  | _, .len b _ => b.wt Γ
  | _, .mlen b _ => b.wt Γ

end

/-- The source of `alice.age = x;` or `alice = p;`. -/
def Src.wt (Γ : Ctx) {T : Ty} : Src C T → Bool
  | .val v => v.wt Γ
  | .copy p _ => p.wt Γ

/-- The path `p = alice;` or `p = persons.push();` binds. -/
def ARhs.wt (Γ : Ctx) {R : RefTy} : ARhs C R → Bool
  | .path p => p.wt Γ
  | .push b _ => b.wt Γ

/-- The object `m = n;` or `m = alice;` binds. -/
def MRhs.wt (Γ : Ctx) {R : RefTy} : MRhs C R → Bool
  | .alias p => p.wt Γ
  | .copy p _ => p.wt Γ
  | .newArr n _ => n.wt Γ

/-- Where `basket.items = new uint[](n);` lands. -/
def NewLhs.wt (Γ : Ctx) {R : RefTy} : NewLhs C R → Bool
  | .store l => l.wt Γ
  | .mem l => l.wt Γ

/-- What `m.age = x;` or `m.account = n;` writes. -/
def MSrc.wt (Γ : Ctx) {T : Ty} : MSrc C T → Bool
  | .val v => v.wt Γ
  | .ref p => p.wt Γ

/-- The target of `x += 1;`, `alice.age++;`, `m.age -= 1;`. -/
def OpLoc.wt (Γ : Ctx) : {p : PrimTy} → OpLoc C p → Bool
  | p, .local x => lookupBy x Γ == some (.stack (.prim p))
  | _, .root .. => true
  | _, .field b _ _ => b.wt Γ
  | _, .index _ b i => b.wt Γ && i.wt Γ
  | _, .mfield b _ _ => b.wt Γ
  | _, .mindex _ b i => b.wt Γ && i.wt Γ

/-- `x` is bound as `bt` in `Γ`. -/
def Ctx.has (Γ : Ctx) (x : Var) (bt : BTy) : Bool := lookupBy x Γ == some bt

/-- The context a call's parameters leave: each argument checked where it is
bound, as its inlining declares them one after another. -/
def Arg.wt : Ctx → List (Arg C) → Option Ctx
  | Γ, [] => some Γ
  | Γ, a :: as => if a.e.wt Γ then Arg.wt (setBy a.x (.stack (.prim a.p)) Γ) as else none

/-- The context a call's return variable is declared in. -/
def CallRet.ctx (Γ : Ctx) : CallRet → Ctx
  | .none => Γ
  | .val p r _ => setBy r (.stack (.prim p)) Γ

/-- The returned value lands in a local of its type. -/
def CallRet.wt (Γ : Ctx) : CallRet → Bool
  | .val p r (some y) => Ctx.has Γ r (.stack (.prim p)) && Ctx.has Γ y (.stack (.prim p))
  | _ => true

/-- The context the locals an outcome of an external call binds leave, each
at its type, in the order `bindData` binds them. -/
def bindCtx : List (PrimTy × Var) → Ctx → Ctx
  | [], Γ => Γ
  | (p, x) :: xs, Γ => bindCtx xs (setBy x (.stack (.prim p)) Γ)

/-- An external call's receiver and arguments read locals as declared. -/
def ExtCall.wt (Γ : Ctx) (c : ExtCall C) : Bool :=
  c.addr.wt Γ && c.args.all fun a => a.2.wt Γ

mutual

/-- The context a statement leaves, if its locals are used as declared:
`uint x = 1;` adds `x : uint`, `x = x + 1;` needs it.  `Person storage p;`
binds nothing at run time, so it adds nothing.  An `if` keeps the context
it started with, and each branch must not rebind what that context binds
(`Ctx.le`): the interpreter has no scopes, so a branch's declaration
outlives it, and one that retyped an outer local would break the join. -/
def Stmt.wt (Γ : Ctx) : Stmt C → Option Ctx
  | .assign l r => if l.wt Γ && r.wt Γ then some Γ else none
  | @Stmt.rebind _ R x r => if Ctx.has Γ x (.path (.ref R)) && r.wt Γ then some Γ else none
  | @Stmt.assignLocal _ p x r =>
    if Ctx.has Γ x (.stack (.prim p)) && r.wt Γ then some Γ else none
  | .declLocal p x init =>
    if init.all (·.wt Γ) then some (setBy x (.stack (.prim p)) Γ) else none
  | .declStorage R x init =>
    match init with
    | none => some Γ
    | some r => if r.wt Γ then some (setBy x (.path (.ref R)) Γ) else none
  | .opAssign _ _ _ l r => if l.wt Γ && r.wt Γ then some Γ else none
  | .incDec _ _ l => if l.wt Γ then some Γ else none
  | @Stmt.assignIncDec _ p x _ _ l _ =>
    if Ctx.has Γ x (.stack (.prim p)) && l.wt Γ then some Γ else none
  | .push b v _ => if b.wt Γ && v.all (·.wt Γ) then some Γ else none
  | .pop b => if b.wt Γ then some Γ else none
  | .transfer r a => if r.wt Γ && a.wt Γ then some Γ else none
  | .declMem R x init _ =>
    if init.all (·.wt Γ) then some (setBy x (.mem (.ref R)) Γ) else none
  | @Stmt.rebindMem _ R x r => if Ctx.has Γ x (.mem (.ref R)) && r.wt Γ then some Γ else none
  | .assignFromMem l p => if l.wt Γ && p.wt Γ then some Γ else none
  | .assignMem l r => if l.wt Γ && r.wt Γ then some Γ else none
  | .delete l => if l.wt Γ then some Γ else none
  | .deleteMem p _ => if p.wt Γ then some Γ else none
  | .assignNew l n _ => if l.wt Γ && n.wt Γ then some Γ else none
  | .ite c thn els =>
    if c.wt Γ then
      match Prog.wt Γ thn, Prog.wt Γ els with
      | some Γt, some Γe => if Ctx.le Γ Γt && Ctx.le Γ Γe then some Γ else none
      | _, _ => none
    else none
  | .require c => if c.wt Γ then some Γ else none
  | .assert c => if c.wt Γ then some Γ else none
  | .revert => some Γ
  | .call _ args _ ret body =>
    match Arg.wt Γ args with
    | some Γ₁ =>
      match Prog.wt (ret.ctx Γ₁) body with
      | some Γ₂ => if ret.wt Γ₂ then some Γ₂ else none
      | none => none
    | none => none
  | .tryCall c rets ok err code pnc other =>
    if c.wt Γ then
      match Prog.wt (bindCtx rets Γ) ok, Prog.wt Γ err, Prog.wt (bindCtx (codeBinders code) Γ) pnc,
          Prog.wt Γ other with
      | some Γ₁, some Γ₂, some Γ₃, some Γ₄ =>
        if Ctx.le Γ Γ₁ && Ctx.le Γ Γ₂ && Ctx.le Γ Γ₃ && Ctx.le Γ Γ₄ then some Γ else none
      | _, _, _, _ => none
    else none

/-- The context a block leaves. -/
def Prog.wt (Γ : Ctx) : List (Stmt C) → Option Ctx
  | [] => some Γ
  | s :: P =>
    match s.wt Γ with
    | some Γ₁ => Prog.wt Γ₁ P
    | none => none

end

/-! ## The invariant -/

/-- Every local `Γ` tracks is bound as `Γ` says: `x : uint` holds a number,
`p : Person storage` a path the layout types `Person`, `m : Person memory`
an identity the store typing claims at `Person`. -/
def EnvWT (Γ : Ctx) (L : Layout) (H : HeapTy) (env : List (Var × Binding)) : Prop :=
  ∀ x bt, lookupBy x Γ = some bt → ∃ b, lookupBy x env = some b ∧ BTy.matchesB L H bt b = true

/-- The state invariant for contract `C` under locals `Γ` and store typing
`H`: storage inhabits `C`'s layout, the locals `Γ` and the heap `H`, and
the allocation counter is fresh. -/
structure RunWT (C : Contract) (Γ : Ctx) (H : HeapTy) (σ : State) : Prop where
  layoutNodup : nodupKeysB C.vars = true
  storage : wellTypedStorageB C.layout σ.storage = true
  env : EnvWT Γ C.layout H σ.env
  heapTyNodup : nodupKeysB H = true
  heap : heapTypedB H σ.heap = true
  heapWf : HeapWellFormed σ

/-- The old invariant is a stronger one: a state `StateWT` types under
`C`'s layout is `RunWT`. -/
theorem Semantics.StateWT.toRunWT {Γ : Ctx} {H : HeapTy} {σ : State}
    (h : StateWT Γ H C.layout σ) : RunWT C Γ H σ := by
  refine ⟨h.layoutNodup, h.storage, ?_, h.heapTyNodup, h.heap, h.heapWf⟩
  intro x bt hx
  have henv := h.env
  simp only [envTypedB, Bool.and_eq_true] at henv
  have := List.all_eq_true.mp henv.1 _ (lookupBy_eq_some_mem hx)
  revert this
  cases hb : lookupBy x σ.env with
  | none => intro h; exact absurd h (by simp)
  | some b => intro h; exact ⟨b, rfl, h⟩

namespace RunWT

variable {Γ : Ctx} {H : HeapTy} {σ : State}

/-- A binding a checked local reads. -/
theorem lookup (hwt : RunWT C Γ H σ) {x : Var} {bt : BTy}
    (hx : Ctx.has Γ x bt = true) :
    ∃ b, σ.getEnv x = .ok b ∧ BTy.matchesB C.layout H bt b = true := by
  simp only [Ctx.has, beq_iff_eq] at hx
  obtain ⟨b, hb, hm⟩ := hwt.env x bt hx
  exact ⟨b, by simp [State.getEnv, hb], hm⟩

end RunWT

/-! ## Value and heap lemmas -/

section Lemmas

variable {H : HeapTy}

/-- A reference slot typed at a reference type is the store typing's claim. -/
theorem MVal.hasTyH_ref {id : Nat} {R : RefTy} :
    MVal.hasTyH H (.ref id) (.ref R) = true ↔ lookupBy id H = some (.ref R) := by
  simp [MVal.hasTyH]

/-- The object at a claimed identity exists and has the claimed type. -/
theorem heapTypedB_obj {heap : List (Nat × MObj)} {id : Nat} {ty : Ty}
    (hheap : heapTypedB H heap = true) (h : lookupBy id H = some ty) :
    ∃ obj, lookupBy id heap = some obj ∧ obj.hasTyH H ty = true := by
  have := List.all_eq_true.mp hheap _ (lookupBy_eq_some_mem h)
  revert this
  cases hl : lookupBy id heap with
  | none => intro h; exact absurd h (by simp)
  | some obj => intro h; exact ⟨obj, rfl, h⟩

/-- A member of a typed memory struct has its declared type: `m.age` a `uint`. -/
theorem mHasTyHFields_lookup {str : Name} {fields : List (Name × MVal)} {n : Name} {v : MVal}
    (hwt : MObj.hasTyH.hasTyHFields H str fields = true)
    (hlook : lookupBy n fields = some v) :
    ∃ ty, lookupBy n (structDef str) = some ty ∧ MVal.hasTyH H v ty = true := by
  induction fields with
  | nil => simp [lookupBy] at hlook
  | cons p rest ih =>
      obtain ⟨n', v'⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at hwt
      by_cases hn : n = n'
      · subst hn
        simp [lookupBy] at hlook
        subst hlook
        cases hdef : lookupBy n (structDef str) with
        | none => rw [hdef] at hwt; exact Bool.noConfusion hwt.1
        | some ty =>
            rw [hdef] at hwt
            exact ⟨ty, rfl, hwt.1⟩
      · simp [lookupBy, hn] at hlook
        exact ih hwt.2 hlook

/-- An element of a typed memory array has the element type: `ns[i]` a `uint`. -/
theorem mHasTyHElems_mem {elem : Ty} {elems : List MVal} {v : MVal}
    (hwt : MObj.hasTyH.hasTyHElems H elem elems = true) (hmem : v ∈ elems) :
    MVal.hasTyH H v elem = true := by
  induction elems with
  | nil => cases hmem
  | cons w rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at hwt
      cases hmem with
      | head => exact hwt.1
      | tail _ hmem => exact ih hwt.2 hmem

/-- `m.age = 3;` keeps `m`'s object a `Person`. -/
theorem mHasTyHFields_setBy {str : Name} {fields : List (Name × MVal)} {n : Name} {w : MVal}
    {tyf : Ty} (hwt : MObj.hasTyH.hasTyHFields H str fields = true)
    (hdef : lookupBy n (structDef str) = some tyf) (hw : MVal.hasTyH H w tyf = true) :
    MObj.hasTyH.hasTyHFields H str (setBy n w fields) = true := by
  induction fields with
  | nil => simp [setBy, MObj.hasTyH.hasTyHFields, hdef, hw]
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at hwt
      by_cases hn : n = k
      · subst hn
        simp [setBy, MObj.hasTyH.hasTyHFields, hdef, hw, hwt.2]
      · simp [setBy, hn, MObj.hasTyH.hasTyHFields, hwt.1, ih hwt.2]

/-- The element type of an array type of either kind: `uint` of `uint[]` and
of `uint[3]`. -/
def RefTy.arrElem? : RefTy → Option Ty
  | .array E | .fixed E _ => some E
  | _ => none

theorem ArrTy.arrElem {R : RefTy} {E : Ty} : ArrTy R E → R.arrElem? = some E
  | .dyn | .fixed => rfl

/-- An object typed at an array type is an array of the element type. -/
theorem MObj.hasTyH_arrElem {R : RefTy} {E : Ty} {obj : MObj} (hR : R.arrElem? = some E)
    (h : MObj.hasTyH H obj (.ref R) = true) :
    ∃ elems fx, obj = .array elems fx ∧ MObj.hasTyH.hasTyHElems H E elems = true := by
  cases R <;> simp only [RefTy.arrElem?, Option.some.injEq, reduceCtorEq] at hR <;> subst hR <;>
    cases obj <;> simp_all [MObj.hasTyH]

/-- `ns[i] = 3;` keeps `ns`'s object a `uint[]`. -/
theorem mHasTyHElems_set {elem : Ty} {elems : List MVal} {i : Nat} {w : MVal}
    (hwt : MObj.hasTyH.hasTyHElems H elem elems = true) (hw : MVal.hasTyH H w elem = true) :
    MObj.hasTyH.hasTyHElems H elem (elems.set i w) = true := by
  induction elems generalizing i with
  | nil => exact hwt
  | cons v rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at hwt
      cases i with
      | zero =>
          simp only [List.set, MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
          exact ⟨hw, hwt.2⟩
      | succ n =>
          simp only [List.set, MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
          exact ⟨hwt.1, ih hwt.2⟩

/-- Writing a typed object over a claimed identity keeps the heap typed. -/
theorem heapTypedB_setObj {heap : List (Nat × MObj)} {id : Nat} {ty : Ty} {obj : MObj}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H heap = true)
    (hclaim : lookupBy id H = some ty) (hobj : obj.hasTyH H ty = true) :
    heapTypedB H (setBy id obj heap) = true := by
  refine List.all_eq_true.mpr fun r hr => ?_
  show (match lookupBy r.1 (setBy id obj heap) with
    | some o => o.hasTyH H r.2
    | none => false) = true
  by_cases hid : r.1 = id
  · have : r.2 = ty := by
      have hl := lookupBy_eq_of_nodup hnd hr
      rw [hid, hclaim] at hl
      exact (Option.some.inj hl).symm
    rw [hid, lookupBy_setBy_self, this]
    exact hobj
  · rw [lookupBy_setBy_ne hid]
    exact List.all_eq_true.mp hheap _ hr

/-- `setObj` on a present identity keeps the allocation counter fresh. -/
theorem HeapWellFormed.setObj' {s : State} {id : Nat} {obj : MObj}
    (hwf : HeapWellFormed s) (hpresent : lookupBy id s.heap ≠ none) :
    HeapWellFormed (s.setObj id obj) := by
  intro i hi
  show lookupBy i (setBy id obj s.heap) = none
  have hne : i ≠ id := by
    intro he
    subst he
    exact hpresent (hwf i hi)
  rw [lookupBy_setBy_ne hne]
  exact hwf i hi

/-- A primitive slot read out is a stack value of the slot's type. -/
theorem MVal.asValue_hasTy {mv : MVal} {ty : Ty} {v : Value}
    (h : MVal.hasTyH H mv ty = true) (hval : mv.asValue = .ok v) :
    (Value.toSVal v).hasTy ty = true := by
  cases mv with
  | prim p =>
      cases p <;> simp only [MVal.asValue] at hval <;> cases hval <;>
        cases ty with
        | prim pt => cases pt <;> simp_all [MVal.hasTyH, Value.toSVal, SVal.hasTy]
        | ref r => simp [MVal.hasTyH] at h
  | ref id => exact nomatch hval

/-- A typed stack value stored in memory is a typed slot. -/
theorem Value.toMVal_hasTyH {v : Value} {ty : Ty}
    (h : (Value.toSVal v).hasTy ty = true) : MVal.hasTyH H v.toMVal ty = true := by
  cases v <;> cases ty with
  | prim pt => cases pt <;> simp_all [Value.toSVal, SVal.hasTy, Value.toMVal, MVal.hasTyH]
  | ref r => simp [Value.toSVal, SVal.hasTy] at h

/-- A stored primitive read out is a stack value of its type. -/
theorem SVal.asValue_hasTy {sv : SVal} {ty : Ty} {v : Value}
    (h : sv.hasTy ty = true) (hval : sv.asValue = .ok v) : (Value.toSVal v).hasTy ty = true := by
  rw [SVal.asValue_toSVal hval]; exact h

/-- A slot read as an object is a reference: `m` in `m.age`. -/
theorem MVal.asRef_ok {mv : MVal} {id : Nat} (h : mv.asRef = .ok id) : mv = .ref id := by
  cases mv with
  | ref i => cases h; rfl
  | prim _ => exact nomatch h

/-- An integer is a value of every numeric type. -/
theorem int_toSVal_hasTy {p : PrimTy} (hp : p.isNumeric = true) (n : Int) :
    (Value.toSVal (.int n)).hasTy (.prim p) = true := by
  cases p <;> simp_all [PrimTy.isNumeric, Value.toSVal, SVal.hasTy]

/-- Comparisons and connectives produce booleans. -/
theorem applyBinOp_nonarith_bool {op : BinOp} {l r v : Value}
    (hop : op.isArith = false) (h : applyBinOp op l r = .ok v) : ∃ b, v = .bool b := by
  cases op <;> simp only [BinOp.isArith] at hop <;> try exact Bool.noConfusion hop
  all_goals simp only [applyBinOp, bind, Except.bind] at h
  all_goals repeat' split at h
  all_goals first
    | exact ⟨_, (Except.ok.inj h).symm⟩
    | exact nomatch h

end Lemmas

/-! ## Operators -/

/-- `a ⊕ b` evaluates to a value of the type `⊕` returns: `a + b` at `uint`
is a number, `a < b` a boolean, whatever the operands held. -/
theorem evalBinop_wt {op : BinOp} {p q : PrimTy} {lv : Value} {rb : Res Value} {w : Value}
    (hacc : op.accepts p = true) (hq : op.ret p = q) (h : evalBinop op p lv rb = .ok w) :
    (Value.toSVal w).hasTy (.prim q) = true := by
  subst hq
  unfold evalBinop at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · obtain ⟨rv, _, h⟩ := bind_ok_inv h
    obtain ⟨v', hv', h⟩ := bind_ok_inv h
    have hw := checkArith_ok_eq h
    subst hw
    cases hA : op.isArith
    · obtain ⟨b, rfl⟩ := applyBinOp_nonarith_bool hA hv'
      simp [BinOp.ret, hA, Value.toSVal, SVal.hasTy]
    · obtain ⟨n, rfl⟩ := applyBinOp_arith_int hA hv'
      have hnum : p.isNumeric = true := by
        cases op <;> simp_all [BinOp.isArith, BinOp.accepts, PrimTy.isNumeric]
      simp only [BinOp.ret, hA, if_true]
      exact int_toSVal_hasTy hnum n

/-- `-a`, `!a` and `~a` evaluate to a value of the type they return. -/
theorem evalUnop_wt {op : UnOp} {p q : PrimTy} {v w : Value}
    (hacc : op.accepts p = true) (hq : op.ret p = q)
    (h : (do unopCheck op p (← applyUnOp op v)) = (.ok w : Res Value)) :
    (Value.toSVal w).hasTy (.prim q) = true := by
  subst hq
  obtain ⟨u, hu, h⟩ := bind_ok_inv h
  have hw : w = u := by
    unfold unopCheck at h
    split at h
    · exact checkArith_ok_eq h
    · cases h; rfl
  subst hw
  cases op with
  | neg =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu; exact int_toSVal_hasTy (by simpa [UnOp.accepts] using hacc) _
  | not =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu; rfl
  | bnot =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu; exact int_toSVal_hasTy (by simp_all [UnOp.accepts, UnOp.ret, PrimTy.isNumeric]) _

/-! ## The evaluators are typed

`H` is fixed here: nothing an expression does allocates. -/

section Eval

variable {Γ : Ctx} {H : HeapTy} {σ : State}

/-- A simple value is of its type: `x` at `uint` holds a number when `Γ`
says `uint x`. -/
theorem Simple.eval_wt (hwt : RunWT C Γ H σ) {p : PrimTy} {s : Simple C p} {w : Value}
    (hw : s.wt Γ = true) (h : s.eval σ = .ok w) : (Value.toSVal w).hasTy (.prim p) = true := by
  cases s with
  | lit n hn => cases h; exact int_toSVal_hasTy hn n
  | bool b => cases h; rfl
  | «local» x =>
    obtain ⟨b, hb, hm⟩ := hwt.lookup hw
    simp only [Simple.eval, hb, bind, Except.bind] at h
    cases b with
    | val v => cases h; simpa [BTy.matchesB] using hm
    | spath _ _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | env k hp => subst hp; cases h; rfl

mutual

/-- A checked storage path resolves to a place the layout types at the
path's type: `p.age`, with `p : Person storage`, at `uint`. -/
theorem SPath.resolve_wt (hwt : RunWT C Γ H σ) :
    ∀ {T : Ty} (p : SPath C T) {r : Name} {segs : List Seg},
      p.wt Γ = true → p.resolve σ = .ok (r, segs) → C.layout.tyAt r segs = some T
  | _, @SPath.alias _ R x, r, segs, hw, h => by
    obtain ⟨b, hb, hm⟩ := hwt.lookup (x := x) (bt := .path (.ref R)) hw
    simp only [SPath.resolve, aliasPath, hb, bind, Except.bind] at h
    cases b with
    | spath r' segs' =>
      cases h
      simpa [BTy.matchesB] using hm
    | val _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | _, .loc l, r, segs, hw, h => Loc.resolve_wt hwt l hw h

/-- `alice.age` resolves to `(alice, [age])`, which the layout types `uint`. -/
theorem Loc.resolve_wt (hwt : RunWT C Γ H σ) :
    ∀ {T : Ty} (l : Loc C T) {r : Name} {segs : List Seg},
      l.wt Γ = true → l.resolve σ = .ok (r, segs) → C.layout.tyAt r segs = some T
  | _, .root r' hr, r, segs, _, h => by
    cases h
    exact Contract.layout_tyAt_root hr
  | _, .field b f hf, r, segs, hw, h => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    cases h
    exact tyAt_append_seg (SPath.resolve_wt hwt b hw h0) hf
  | _, .index it b i, r, segs, hw, h => by
    simp only [Loc.wt, Bool.and_eq_true] at hw
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    obtain ⟨k, _, h⟩ := bind_ok_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    bind_inv h
    cases h
    have hb := SPath.resolve_wt hwt b hw.1 h0
    cases it with
    | map => exact tyAt_append_seg hb rfl
    | arr a => cases a <;> exact tyAt_append_seg hb rfl

/-- A checked memory path holds a slot of its type: `m`, with
`m : Person memory`, an identity the store typing claims at `Person`. -/
theorem MPath.mval_wt (hwt : RunWT C Γ H σ) :
    ∀ {T : Ty} (p : MPath C T) {mv : MVal},
      p.wt Γ = true → p.mval σ = .ok mv → MVal.hasTyH H mv T = true
  | _, @MPath.var _ R x, mv, hw, h => by
    obtain ⟨b, hb, hm⟩ := hwt.lookup (x := x) (bt := .mem (.ref R)) hw
    simp only [MPath.mval, hb, bind, Except.bind] at h
    cases b with
    | mref id => cases h; simpa [BTy.matchesB] using hm
    | val _ => exact nomatch h
    | spath _ _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | _, .loc l, mv, hw, h => MLoc.read_wt hwt l hw h

/-- `m.age` reads a slot the heap types `uint`. -/
theorem MLoc.read_wt (hwt : RunWT C Γ H σ) :
    ∀ {T : Ty} (l : MLoc C T) {mv : MVal},
      l.wt Γ = true → l.read σ = .ok mv → MVal.hasTyH H mv T = true
  | _, @MLoc.field _ s _ b f hf, mv, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.heap hb
    obtain ⟨o, ho, h⟩ := bind_ok_inv h
    simp only [State.getObj, hobj] at ho
    cases ho
    cases obj with
    | struct fields =>
      simp only at h
      split at h
      · rename_i v hv
        cases h
        obtain ⟨ty, hdef, hv⟩ := mHasTyHFields_lookup (by simpa [MObj.hasTyH] using hty) hv
        have : ty = _ := Option.some.inj (hdef.symm.trans hf)
        subst this
        exact hv
      · exact nomatch h
    | array _ => exact nomatch h
  | _, @MLoc.index _ _ E a b i, mv, hw, h => by
    simp only [MLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.heap hb
    obtain ⟨elems, fx, rfl, hel⟩ := MObj.hasTyH_arrElem a.arrElem hty
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    obtain ⟨o, ho, h⟩ := bind_ok_inv h
    simp only [State.getObj, hobj] at ho
    cases ho
    simp only at h
    split at h
    · cases h
      exact mHasTyHElems_mem hel (List.get_mem _ _)
    · exact nomatch h

/-- A checked value evaluates to a value of its type: `alice.age + 1` to
a number, `x < y` to a boolean. -/
theorem Val.eval_wt (hwt : RunWT C Γ H σ) :
    ∀ {p : PrimTy} (v : Val C p) {w : Value},
      v.wt Γ = true → v.eval σ = .ok w → (Value.toSVal w).hasTy (.prim p) = true
  | _, .simple s, w, hw, h => Simple.eval_wt hwt hw h
  | _, .read l, w, hw, h => by
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    exact SVal.asValue_hasTy
      (findStorage_hasTy hwt.storage (Loc.resolve_wt hwt l hw hr) hsv) h
  | _, .binop op hacc hq a b, w, _, h => by
    obtain ⟨lv, _, h⟩ := bind_ok_inv h
    exact evalBinop_wt hacc hq h
  | _, .unop op hacc hq a, w, _, h => by
    obtain ⟨av, _, h⟩ := bind_ok_inv h
    exact evalUnop_wt hacc hq h
  | _, .ternary c a b, w, hw, h => by
    simp only [Val.wt, Bool.and_eq_true] at hw
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold pickBranch at h
    split at h
    · exact Val.eval_wt hwt a hw.1.2 h
    · exact Val.eval_wt hwt b hw.2 h
    · exact nomatch h
  | _, .readMem l, w, hw, h => by
    obtain ⟨mv, hmv, h⟩ := bind_ok_inv h
    exact MVal.asValue_hasTy (MLoc.read_wt hwt l hw hmv) h
  | _, .len b hp, w, _, h => by
    subst hp
    bind_inv h
    obtain ⟨sv, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; rfl
    all_goals exact nomatch h
  | _, .mlen b hp, w, _, h => by
    subst hp
    iterate 2 bind_inv h
    obtain ⟨o, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; rfl
    all_goals exact nomatch h

end

end Eval

/-! ## Well-formed defaults

The syntax carries `defaultOkS`, which the kernel evaluates; the typing
lemmas want `defaultOk`, which it cannot (it recurses through `structDef`
by well-founded recursion).  They agree on every struct `defaultOkS`
admits, checked here once per struct. -/

theorem defaultOk_struct_of_mem {s : Name} (h : s ∈ defaultOkStructs) :
    defaultOk (.ref (.struct s)) = true := by
  simp only [defaultOkStructs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [defaultOk, defaultOkFields, structDef, lookupBy]

/-- `Person memory m;` and `persons.push();` build a default of the type
they name: `defaultOkS` is enough for `defaultForTy_hasTy`. -/
theorem defaultOk_of_defaultOkS : ∀ {T : Ty}, T.defaultOkS = true → defaultOk T = true
  | .prim _, _ => by simp [defaultOk]
  | .ref (.struct _), h => defaultOk_struct_of_mem (by simpa [Ty.defaultOkS] using h)
  | .ref (.array _), _ => by simp [defaultOk]
  | .ref (.fixed _ _), h => by
    rw [defaultOk]; exact defaultOk_of_defaultOkS (by simpa [Ty.defaultOkS] using h)
  | .ref (.mapping _ _), h => by
    rw [defaultOk]; exact defaultOk_of_defaultOkS (by simpa [Ty.defaultOkS] using h)

/-! ## The invariant under the state operations -/

namespace RunWT

variable {Γ : Ctx} {H : HeapTy} {σ σ' : State}

/-- A storage write of a value of the place's type: `alice.age = 10;`
writes a number where the layout says `uint`. -/
theorem save (hwt : RunWT C Γ H σ) {r : Name} {segs : List Seg} {T : Ty} {new : SVal}
    (hty : C.layout.tyAt r segs = some T) (hnew : new.hasTy T = true)
    (h : σ.saveStorage r segs new = .ok σ') : RunWT C Γ H σ' := by
  obtain ⟨hheap, hnext, henv, _⟩ := SemanticsProperties.State.saveStorage_frame h
  refine ⟨hwt.layoutNodup, State.saveStorage_wellTyped hwt.layoutNodup hwt.storage hty hnew h,
    ?_, hwt.heapTyNodup, ?_, ?_⟩
  · rw [henv]; exact hwt.env
  · rw [hheap]; exact hwt.heap
  · intro i hi; rw [hheap]; exact hwt.heapWf i (hnext ▸ hi)

/-- A storage write of what an assignment's right-hand side denotes, of the
place's type: a word saved, or a copy over what is there (`SVal.overlay`),
which keeps the type the old value had. -/
theorem write (hwt : RunWT C Γ H σ) {r : Name} {segs : List Seg} {T : Ty} {new : SVal}
    (hty : C.layout.tyAt r segs = some T) (hnew : new.hasTy T = true)
    (h : σ.writeStorage r segs new = .ok σ') : RunWT C Γ H σ' := by
  rcases State.writeStorage_ok_inv h with h | ⟨cur, hcur, h⟩
  · exact hwt.save hty hnew h
  · exact hwt.save hty (SVal.overlay_hasTy (findStorage_hasTy hwt.storage hty hcur) hnew) h

/-- A declaration: `uint x = 1;` binds `x` and `Γ` learns `x : uint`. -/
theorem setEnv (hwt : RunWT C Γ H σ) {x : Var} {bt : BTy} {b : Binding}
    (hm : BTy.matchesB C.layout H bt b = true) :
    RunWT C (setBy x bt Γ) H (σ.setEnv x b) := by
  refine { hwt with env := ?_ }
  intro y bt' hy
  by_cases hyx : y = x
  · subst hyx
    rw [lookupBy_setBy_self] at hy
    cases hy
    exact ⟨b, by simp [State.setEnv, lookupBy_setBy_self], hm⟩
  · rw [lookupBy_setBy_ne hyx] at hy
    obtain ⟨b', hb', hm'⟩ := hwt.env y bt' hy
    exact ⟨b', by simp only [State.setEnv]; rw [lookupBy_setBy_ne hyx]; exact hb', hm'⟩

/-- An assignment to a declared local: `x = 2;` with `x : uint` in `Γ`
leaves `Γ` as it was. -/
theorem setEnv_same (hwt : RunWT C Γ H σ) {x : Var} {bt : BTy} {b : Binding}
    (hx : Ctx.has Γ x bt = true) (hm : BTy.matchesB C.layout H bt b = true) :
    RunWT C Γ H (σ.setEnv x b) := by
  have h := hwt.setEnv (x := x) hm
  simp only [Ctx.has, beq_iff_eq] at hx
  refine { h with env := fun y bt' hy => h.env y bt' ?_ }
  by_cases hyx : y = x
  · subst hyx; rw [hx] at hy; rw [lookupBy_setBy_self, hy]
  · rw [lookupBy_setBy_ne hyx]; exact hy

/-- A branch that declared more is still typed under the context it
started from: after `if (c) { uint y = 1; } else { }`, `Γ` without `y`. -/
theorem weaken {Γ' : Ctx} (hwt : RunWT C Γ' H σ) (hle : Ctx.le Γ Γ' = true) :
    RunWT C Γ H σ :=
  { hwt with env := fun x bt hx => hwt.env x bt (Ctx.le_lookup hle hx) }

/-- Along an allocation (a storage→memory copy, a fresh default) the
store typing grows and everything typed stays typed. -/
theorem ofCopyOut {H' : HeapTy} (hwt : RunWT C Γ H σ) (hout : CopyOut H σ H' σ') :
    RunWT C Γ H' σ' where
  layoutNodup := hwt.layoutNodup
  storage := by rw [hout.storage]; exact hwt.storage
  env := by
    rw [hout.env]
    intro x bt hx
    obtain ⟨b, hb, hm⟩ := hwt.env x bt hx
    exact ⟨b, hb, BTy.matchesB_mono hout.ext hm⟩
  heapTyNodup := hout.nodup
  heap := hout.heap
  heapWf := hout.heapWf

/-- A memory write of an object of the identity's claimed type:
`m.age = 3;` keeps `m`'s object a `Person`. -/
theorem setObj (hwt : RunWT C Γ H σ) {id : Nat} {ty : Ty} {obj obj₀ : MObj}
    (hclaim : lookupBy id H = some ty) (hpresent : lookupBy id σ.heap = some obj₀)
    (hobj : obj.hasTyH H ty = true) : RunWT C Γ H (σ.setObj id obj) where
  layoutNodup := hwt.layoutNodup
  storage := hwt.storage
  env := hwt.env
  heapTyNodup := hwt.heapTyNodup
  heap := heapTypedB_setObj hwt.heapTyNodup hwt.heap hclaim hobj
  heapWf := HeapWellFormed.setObj' hwt.heapWf (by simp [hpresent])

/-- `a.transfer(v)` books the ledger and the contract's funds only. -/
theorem transferAt (hwt : RunWT C Γ H σ) {addr amt : Int}
    (h : Solidity.transferAt σ addr amt = .ok σ') : RunWT C Γ H σ' := by
  unfold Solidity.transferAt at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · cases h; exact ⟨hwt.1, hwt.2, hwt.3, hwt.4, hwt.5, hwt.6⟩

end RunWT

/-! ## The statements' effects are typed -/

section Effects

variable {Γ : Ctx} {H : HeapTy} {σ σ' : State}

/-- The arithmetic write-back of `x += e` stores a number of `x`'s type. -/
theorem arith_new_wt {op : BinOp} {p : PrimTy} {old v n₁ n₂ : Value}
    (hop : op.isArith = true) (hp : p.isNumeric = true)
    (h₁ : applyBinOp op old v = .ok n₁) (h₂ : checkArith (.prim p) n₁ = .ok n₂) :
    (Value.toSVal n₂).hasTy (.prim p) = true := by
  rw [checkArith_ok_eq h₂]
  obtain ⟨n, rfl⟩ := applyBinOp_arith_int hop h₁
  exact int_toSVal_hasTy hp n

/-- `x++` stores and yields numbers of `x`'s type. -/
theorem bump_new_wt {p : PrimTy} {m : Int} {n : Value} (hp : p.isNumeric = true)
    (h : checkArith (.prim p) (.int m) = .ok n) : (Value.toSVal n).hasTy (.prim p) = true := by
  rw [checkArith_ok_eq h]; exact int_toSVal_hasTy hp m

/-- `+=` .. `%=` are arithmetic, so `x += 1` writes a number. -/
theorem compound_isArith {op : BinOp} (h : op.hasCompoundAssign = true) : op.isArith = true := by
  cases op <;> simp_all [BinOp.hasCompoundAssign, BinOp.isArith]

/-- A source stores a value of its type: `alice = bob;` copies a `Person`. -/
theorem Src.value_wt (hwt : RunWT C Γ H σ) {T : Ty} {r : Src C T} {sv : SVal}
    (hw : r.wt Γ = true) (h : r.value σ = .ok sv) : sv.hasTy T = true := by
  cases r with
  | val v =>
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact Val.eval_wt hwt v hw hv
  | copy p _ =>
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    exact findStorage_hasTy hwt.storage (SPath.resolve_wt hwt p hw hr) h

/-- `b.push(v)` at an array of `E`s appends an `E`.  The slot the push
lands on is an `E` whenever `E`'s default is well-formed; a push with an
argument does not look at it. -/
theorem pushAt_wt (hwt : RunWT C Γ H σ) {E : Ty} {r : Name} {segs : List Seg}
    {val : SVal → Res SVal} (hty : C.layout.tyAt r segs = some (.ref (.array E)))
    (hval : ∀ slot v, (defaultOk E = true → slot.hasTy E = true) → val slot = .ok v →
      v.hasTy E = true)
    (h : pushAt σ E r segs val = .ok σ') : RunWT C Γ H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsvt := findStorage_hasTy hwt.storage hty hsv
  cases sv with
  | array elems shadow fx =>
    simp only [SVal.hasTy, Bool.and_eq_true] at hsvt
    obtain ⟨newElem, hnew, h⟩ := bind_ok_inv h
    have hslot : defaultOk E = true → (pushSlot E shadow).1.hasTy E = true :=
      fun hok => (pushSlot_hasTy hsvt.2 hok).1
    refine hwt.save hty ?_ h
    simp only [SVal.hasTy, Bool.and_eq_true]
    refine ⟨⟨hsvt.1.1, hasTyElems_append hsvt.1.2 ?_⟩, pushSlot_rest_hasTy hsvt.2⟩
    simp [SVal.hasTy.hasTyElems, hval _ _ hslot hnew]
  | prim _ => exact nomatch h
  | struct _ => exact nomatch h
  | map _ _ => exact nomatch h

/-- `b.push()` as a place: the array stays typed. -/
theorem pushPlaceAt_wt (hwt : RunWT C Γ H σ) {E : Ty} {r : Name} {segs : List Seg} {n : Int}
    (hty : C.layout.tyAt r segs = some (.ref (.array E))) (hok : defaultOk E = true)
    (h : pushPlaceAt σ E r segs = .ok (σ', n)) : RunWT C Γ H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsvt := findStorage_hasTy hwt.storage hty hsv
  cases sv with
  | array elems shadow fx =>
    simp only [SVal.hasTy, Bool.and_eq_true] at hsvt
    obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
    cases h
    refine hwt.save hty ?_ hσ₁
    simp only [SVal.hasTy, Bool.and_eq_true]
    refine ⟨⟨hsvt.1.1, hasTyElems_append hsvt.1.2 ?_⟩, pushSlot_rest_hasTy hsvt.2⟩
    simp only [SVal.hasTy.hasTyElems, Bool.and_true]
    exact (pushSlot_hasTy hsvt.2 hok).1
  | prim _ => exact nomatch h
  | struct _ => exact nomatch h
  | map _ _ => exact nomatch h

/-- `b.pop()` keeps the array typed: the popped element is cleared into
the recycled slots at its own type. -/
theorem popAt_wt (hwt : RunWT C Γ H σ) {E : Ty} {keep : Bool} {r : Name} {segs : List Seg}
    (hty : C.layout.tyAt r segs = some (.ref (.array E))) (h : popAt σ keep r segs = .ok σ') :
    RunWT C Γ H σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsvt := findStorage_hasTy hwt.storage hty hsv
  cases sv with
  | array elems shadow fx =>
    simp only [SVal.hasTy, Bool.and_eq_true] at hsvt
    simp only at h
    split at h
    · exact nomatch h
    · rename_i last restRev hrev
      have hmem : ∀ v, v ∈ last :: restRev → v ∈ elems := by
        intro v hv; rw [← hrev] at hv; exact List.mem_reverse.mp hv
      refine hwt.save hty ?_ h
      simp only [SVal.hasTy, Bool.and_eq_true, SVal.hasTy.hasTyElems]
      refine ⟨⟨hsvt.1.1, hasTyElems_of_forall_mem fun v hv => ?_⟩, ?_, hsvt.2⟩
      · exact hasTyElems_mem hsvt.1.2 (hmem v (List.mem_cons_of_mem _ (List.mem_reverse.mp hv)))
      · have hl := hasTyElems_mem hsvt.1.2 (hmem last List.mem_cons_self)
        cases keep
        · exact SVal.defaultOf_hasTy hl
        · exact hl
  | prim _ => exact nomatch h
  | struct _ => exact nomatch h
  | map _ _ => exact nomatch h

/-- A write into a memory struct's member of the member's type. -/
theorem memWriteField_wt (hwt : RunWT C Γ H σ) {id : Nat} {s f : Name} {T : Ty} {mv : MVal}
    (hid : lookupBy id H = some (.ref (.struct s))) (hf : lookupBy f (structDef s) = some T)
    (hmv : MVal.hasTyH H mv T = true) (h : memWriteField σ id f mv = .ok σ') :
    RunWT C Γ H σ' := by
  obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.heap hid
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  simp only [State.getObj, hobj] at ho
  cases ho
  cases obj with
  | struct fields =>
    cases h
    exact hwt.setObj hid hobj
      (by simpa [MObj.hasTyH] using mHasTyHFields_setBy (by simpa [MObj.hasTyH] using hty) hf hmv)
  | array _ => exact nomatch h

/-- A write into a memory array's element of the element type. -/
theorem memWriteIndex_wt (hwt : RunWT C Γ H σ) {id : Nat} {i : Int} {R : RefTy} {E : Ty}
    {mv : MVal} (hid : lookupBy id H = some (.ref R)) (hR : R.arrElem? = some E)
    (hmv : MVal.hasTyH H mv E = true)
    (h : memWriteIndex σ id i mv = .ok σ') : RunWT C Γ H σ' := by
  obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.heap hid
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  simp only [State.getObj, hobj] at ho
  cases ho
  cases obj with
  | array elems fx =>
    simp only at h
    split at h
    · cases h
      refine hwt.setObj hid hobj ?_
      cases R <;> simp only [RefTy.arrElem?, Option.some.injEq, reduceCtorEq] at hR <;>
        subst hR <;> simp only [MObj.hasTyH, Bool.and_eq_true, beq_iff_eq] at hty ⊢
      · exact ⟨hty.1, mHasTyHElems_set hty.2 hmv⟩
      · exact ⟨⟨hty.1.1, by simp [hty.1.2]⟩, mHasTyHElems_set hty.2 hmv⟩
    · exact nomatch h
  | struct _ => exact nomatch h

/-- The memory place a memory target resolves to holds a `p`: `m.age`
with `m : Person memory`, `ns[i]` with `ns : uint[] memory`. -/
def AddrTy (H : HeapTy) (p : PrimTy) : Addr → Prop
  | .memoryField id f => ∃ s, lookupBy id H = some (.ref (.struct s)) ∧
      lookupBy f (structDef s) = some (.prim p)
  | .memoryIndex id _ => ∃ R, lookupBy id H = some (.ref R) ∧ R.arrElem? = some (.prim p)

/-- The memory place a memory location resolves to holds a `T`. -/
def AddrTyT (H : HeapTy) (T : Ty) : Addr → Prop
  | .memoryField id f => ∃ s, lookupBy id H = some (.ref (.struct s)) ∧
      lookupBy f (structDef s) = some T
  | .memoryIndex id _ => ∃ R, lookupBy id H = some (.ref R) ∧ R.arrElem? = some T

/-- A typed place stays typed as the store typing grows (an allocation). -/
theorem AddrTyT.mono {H H' : HeapTy} {T : Ty} {a : Addr} (hext : H.Extends H')
    (h : AddrTyT H T a) : AddrTyT H' T a := by
  cases a with
  | memoryField id f => obtain ⟨s, hid, hf⟩ := h; exact ⟨s, hext _ _ hid, hf⟩
  | memoryIndex id i => obtain ⟨R, hid, hR⟩ := h; exact ⟨R, hext _ _ hid, hR⟩

/-- `delete m.inner;` writes an object of the member's type there. -/
theorem writeAddr_wt (hwt : RunWT C Γ H σ) {T : Ty} {a : Addr} {mv : MVal}
    (ha : AddrTyT H T a) (hmv : MVal.hasTyH H mv T = true)
    (h : writeAddr σ mv a = .ok σ') : RunWT C Γ H σ' := by
  cases a with
  | memoryField id f =>
    obtain ⟨s, hid, hf⟩ := ha
    exact memWriteField_wt hwt hid hf hmv h
  | memoryIndex id i => obtain ⟨R, hid, hR⟩ := ha; exact memWriteIndex_wt hwt hid hR hmv h

/-- A checked memory location resolves to a place of its type. -/
theorem MLoc.addr_wt (hwt : RunWT C Γ H σ) :
    ∀ {T : Ty} (l : MLoc C T) {a : Addr}, l.wt Γ = true → l.addr σ = .ok a → AddrTyT H T a
  | _, @MLoc.field _ s _ b f hf, a, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact ⟨s, hb, hf⟩
  | _, .index ak b i, a, hw, h => by
    simp only [MLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    cases h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact ⟨_, hb, ak.arrElem⟩

/-- `m.age -= 1;` writes a number where the heap says `uint`. -/
theorem writeLoc_wt (hwt : RunWT C Γ H σ) {p : PrimTy} {loc : Addr} {v : Value}
    (hloc : AddrTy H p loc) (hv : (Value.toSVal v).hasTy (.prim p) = true)
    (h : writeLoc σ loc v = .ok σ') : RunWT C Γ H σ' := by
  cases loc with
  | memoryField id f =>
    obtain ⟨s, hid, hf⟩ := hloc
    exact memWriteField_wt hwt hid hf (Value.toMVal_hasTyH hv) h
  | memoryIndex id i =>
    obtain ⟨R, hid, hR⟩ := hloc
    exact memWriteIndex_wt hwt hid hR (Value.toMVal_hasTyH hv) h

/-- `x ⊕= e` at a storage place of a numeric type. -/
theorem opStore_wt (hwt : RunWT C Γ H σ) {op : BinOp} {p : PrimTy} {r : Name}
    {segs : List Seg} {v : Value} (hop : op.isArith = true) (hp : p.isNumeric = true)
    (hty : C.layout.tyAt r segs = some (.prim p)) (h : opStore σ op p r segs v = .ok σ') :
    RunWT C Γ H σ' := by
  obtain ⟨_, _, _, h₁, h₂, h⟩ := opStore_ok_inv h
  exact hwt.save hty (arith_new_wt hop hp h₁ h₂) h

/-- `m.age += x;` keeps the heap typed. -/
theorem opMem_wt (hwt : RunWT C Γ H σ) {op : BinOp} {p : PrimTy} {loc : Addr} {v : Value}
    (hop : op.isArith = true) (hp : p.isNumeric = true) (hloc : AddrTy H p loc)
    (h : opMem σ op p loc v = .ok σ') : RunWT C Γ H σ' := by
  obtain ⟨_, _, _, h₁, h₂, h⟩ := opMem_ok_inv h
  exact writeLoc_wt hwt hloc (arith_new_wt hop hp h₁ h₂) h

/-- `x ⊕= e` keeps the state typed: the target is resolved once, and the
number written back is of its type. -/
theorem OpLoc.store_wt (hwt : RunWT C Γ H σ) {op : BinOp} (hop : op.isArith = true) :
    ∀ {p : PrimTy} (l : OpLoc C p) {v : Value}, p.isNumeric = true → l.wt Γ = true →
      l.store σ op v = .ok σ' → RunWT C Γ H σ'
  | p, .local x, v, hp, hw, h => by
    obtain ⟨b, hb, _⟩ := hwt.lookup hw
    simp only [OpLoc.store, opLocal, hb, bind, Except.bind] at h
    cases b with
    | val old =>
      simp only [pure, Except.pure] at h
      split at h
      · exact nomatch h
      · rename_i n₁ h₁
        split at h
        · exact nomatch h
        · rename_i n₂ h₂
          cases h
          exact hwt.setEnv_same hw (by simpa [BTy.matchesB] using arith_new_wt hop hp h₁ h₂)
    | spath _ _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | p, .root r hr, v, hp, _, h => opStore_wt hwt hop hp (Contract.layout_tyAt_root hr) h
  | p, .field b f hf, v, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact opStore_wt hwt hop hp (Loc.resolve_wt hwt (.field b f hf) hw hr) h
  | p, .index it b i, v, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact opStore_wt hwt hop hp (Loc.resolve_wt hwt (.index it b (.simple i)) hw hr) h
  | p, @OpLoc.mfield _ s _ b f hf, v, hp, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact opMem_wt hwt hop hp (loc := .memoryField id f) ⟨s, hb, hf⟩ h
  | p, .mindex ak b i, v, hp, hw, h => by
    simp only [OpLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    exact opMem_wt hwt hop hp (loc := .memoryIndex id iv) ⟨_, hb, ak.arrElem⟩ h

/-- `alice.age++` stores and yields numbers. -/
theorem bumpStore_wt (hwt : RunWT C Γ H σ) {op : IncDec} {p : PrimTy} {r : Name}
    {segs : List Seg} {w : Value} (hp : p.isNumeric = true)
    (hty : C.layout.tyAt r segs = some (.prim p)) (h : bumpStore σ op p r segs = .ok (σ', w)) :
    RunWT C Γ H σ' ∧ (Value.toSVal w).hasTy (.prim p) = true := by
  obtain ⟨m, n, hn, hσ₁, rfl⟩ := bumpStore_ok_inv h
  have hnew := bump_new_wt hp hn
  refine ⟨hwt.save hty hnew hσ₁, ?_⟩
  split
  · exact hnew
  · exact int_toSVal_hasTy hp m

/-- `m.age++` stores and yields numbers. -/
theorem bumpMem_wt (hwt : RunWT C Γ H σ) {op : IncDec} {p : PrimTy} {loc : Addr} {w : Value}
    (hp : p.isNumeric = true) (hloc : AddrTy H p loc) (h : bumpMem σ op p loc = .ok (σ', w)) :
    RunWT C Γ H σ' ∧ (Value.toSVal w).hasTy (.prim p) = true := by
  obtain ⟨m, n, hn, hσ₁, rfl⟩ := bumpMem_ok_inv h
  have hnew := bump_new_wt hp hn
  refine ⟨writeLoc_wt hwt hloc hnew hσ₁, ?_⟩
  split
  · exact hnew
  · exact int_toSVal_hasTy hp m

/-- `x++` keeps the state typed, and its value is of `x`'s type. -/
theorem OpLoc.bump_wt (hwt : RunWT C Γ H σ) {op : IncDec} :
    ∀ {p : PrimTy} (l : OpLoc C p) {w : Value}, p.isNumeric = true → l.wt Γ = true →
      l.bump σ op = .ok (σ', w) → RunWT C Γ H σ' ∧ (Value.toSVal w).hasTy (.prim p) = true
  | p, .local x, w, hp, hw, h => by
    obtain ⟨b, hb, _⟩ := hwt.lookup hw
    simp only [OpLoc.bump, bumpLocal, hb, bind, Except.bind] at h
    cases b with
    | val old =>
      simp only [pure, Except.pure] at h
      split at h
      · exact nomatch h
      · rename_i m hm
        split at h
        · exact nomatch h
        · rename_i n hn
          cases h
          have hnew := bump_new_wt hp hn
          refine ⟨hwt.setEnv_same hw (by simpa [BTy.matchesB] using hnew), ?_⟩
          split
          · exact hnew
          · rw [Value.asInt_ok hm]; exact int_toSVal_hasTy hp m
    | spath _ _ => exact nomatch h
    | mref _ => exact nomatch h
    | store _ => exact nomatch h
    | ledger _ => exact nomatch h
  | p, .root r hr, w, hp, _, h => bumpStore_wt hwt hp (Contract.layout_tyAt_root hr) h
  | p, .field b f hf, w, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact bumpStore_wt hwt hp (Loc.resolve_wt hwt (.field b f hf) hw hr) h
  | p, .index it b i, w, hp, hw, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    exact bumpStore_wt hwt hp (Loc.resolve_wt hwt (.index it b (.simple i)) hw hr) h
  | p, @OpLoc.mfield _ s _ b f hf, w, hp, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact bumpMem_wt hwt hp (loc := .memoryField id f) ⟨s, hb, hf⟩ h
  | p, .mindex ak b i, w, hp, hw, h => by
    simp only [OpLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    exact bumpMem_wt hwt hp (loc := .memoryIndex id iv) ⟨_, hb, ak.arrElem⟩ h

/-- `m.age = 3;` writes a slot of the member's type. -/
theorem MLoc.write_wt (hwt : RunWT C Γ H σ) {mv : MVal} :
    ∀ {T : Ty} (l : MLoc C T), MVal.hasTyH H mv T = true → l.wt Γ = true →
      l.write σ mv = .ok σ' → RunWT C Γ H σ'
  | _, @MLoc.field _ s _ b f hf, hmv, hw, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact memWriteField_wt hwt hb hf hmv h
  | _, .index ak b i, hmv, hw, h => by
    simp only [MLoc.wt, Bool.and_eq_true] at hw
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hw.1 hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    exact memWriteIndex_wt hwt hb ak.arrElem hmv h

/-- What a memory write stores is of the place's type: a number, or an
object the store typing claims at the reference type. -/
theorem MSrc.mval_wt (hwt : RunWT C Γ H σ) {T : Ty} {r : MSrc C T} {mv : MVal}
    (hw : r.wt Γ = true) (h : r.mval σ = .ok mv) : MVal.hasTyH H mv T = true := by
  cases r with
  | val v =>
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact Value.toMVal_hasTyH (Val.eval_wt hwt v hw hv)
  | ref p =>
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have := MPath.mval_wt hwt p hw hm0
    rwa [MVal.asRef_ok hid] at this

/-- `new uint[](n)` copies in a value of its type: `n` well-formed defaults. -/
theorem newArrVal_hasTy {R : RefTy} (h : R.newArrOk = true) (n : Int) :
    (newArrVal R n).hasTy (.ref R) = true := by
  cases R with
  | array E =>
    simp only [RefTy.newArrOk, Bool.and_eq_true] at h
    have hE := defaultForTy_hasTy (defaultOk_of_defaultOkS h.2)
    simp only [newArrVal, SVal.hasTy, SVal.hasTy.hasTyElems, Bool.and_true, Bool.not_false,
      Bool.true_and]
    induction n.toNat with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, SVal.hasTy.hasTyElems, hE, ih]
  | struct _ => simp [RefTy.newArrOk] at h
  | fixed _ _ => simp [RefTy.newArrOk] at h
  | mapping _ _ => simp [RefTy.newArrOk] at h

/-- `m = n;` and `m = alice;` bind `m` to an object of `m`'s type: `n`'s,
or a fresh deep copy, which grows the store typing. -/
theorem MRhs.bind_wt (hwt : RunWT C Γ H σ) {x : Var} {R : RefTy} {r : MRhs C R}
    (hw : r.wt Γ = true) (h : r.bind σ x = .ok σ') :
    ∃ H' σ₁ id, H.Extends H' ∧ RunWT C Γ H' σ₁ ∧
      MVal.hasTyH H' (.ref id) (.ref R) = true ∧ σ' = σ₁.setEnv x (.mref id) := by
  cases r with
  | alias p =>
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have := MPath.mval_wt hwt p hw hm0
    rw [MVal.asRef_ok hid] at this
    exact ⟨H, σ, id, HeapTy.Extends.refl H, hwt, this, rfl⟩
  | copy p _ =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have hsvt := findStorage_hasTy hwt.storage (SPath.resolve_wt hwt p hw hr) hsv
    obtain ⟨H', hout, hmv⟩ := copyStToM_typed hwt.heapTyNodup hwt.heap hwt.heapWf hsvt hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', σ₁, id, hout.ext, hwt.ofCopyOut hout, hmv, rfl⟩
  | newArr n hn =>
    bind_inv h
    obtain ⟨nv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hmv⟩ :=
      copyStToM_typed hwt.heapTyNodup hwt.heap hwt.heapWf (newArrVal_hasTy hn nv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', σ₁, id, hout.ext, hwt.ofCopyOut hout, hmv, rfl⟩

/-- `p = alice;` and `p = persons.push();` bind `p` to a path the layout
types at `p`'s type. -/
theorem ARhs.bind_wt (hwt : RunWT C Γ H σ) {x : Var} {R : RefTy} {r : ARhs C R}
    (hw : r.wt Γ = true) (h : r.bind σ x = .ok σ') :
    ∃ σ₁ root segs, RunWT C Γ H σ₁ ∧ C.layout.tyAt root segs = some (.ref R) ∧
      σ' = σ₁.setEnv x (.spath root segs) := by
  cases r with
  | path p =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    cases h
    exact ⟨σ, root, segs, hwt, SPath.resolve_wt hwt p hw hr, rfl⟩
  | push b hd =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, n⟩, hpush, h⟩ := bind_ok_inv h
    cases h
    have hty := SPath.resolve_wt hwt b hw hr
    exact ⟨σ₁, root, segs ++ [.at n],
      pushPlaceAt_wt hwt hty (defaultOk_of_defaultOkS hd) hpush, tyAt_append_seg hty rfl, rfl⟩

/-- A call's parameters bound: each argument of its type. -/
theorem Arg.bindSeq_wt : ∀ {args : List (Arg C)} {Γ Γ' : Ctx} {σ σ' : State},
    RunWT C Γ H σ → Arg.wt Γ args = some Γ' → Arg.bindSeq args σ = .ok σ' → RunWT C Γ' H σ'
  | [], _, _, _, _, hwt, hs, h => by cases hs; cases h; exact hwt
  | a :: as, Γ, Γ', σ, σ', hwt, hs, h => by
    simp only [Arg.wt] at hs
    split at hs
    · rename_i hc
      obtain ⟨w, hv, h⟩ := bind_ok_inv h
      exact Arg.bindSeq_wt (hwt.setEnv (by simpa [BTy.matchesB] using Val.eval_wt hwt a.e hc hv)) hs h
    · exact nomatch hs

theorem CallRet.enter_wt (hwt : RunWT C Γ H σ) :
    (ret : CallRet) → RunWT C (ret.ctx Γ) H (ret.enter σ)
  | .none => hwt
  | .val p _ _ => hwt.setEnv (by cases p <;> rfl)

theorem CallRet.leave_wt (hwt : RunWT C Γ H σ) {σ' : State} :
    (ret : CallRet) → ret.wt Γ = true → CallRet.leave (C := C) σ ret = .ok σ' → RunWT C Γ H σ'
  | .none, _, h => by cases h; exact hwt
  | .val _ _ Option.none, _, h => by cases h; exact hwt
  | .val p r (some y), hr, h => by
    simp only [CallRet.wt, Bool.and_eq_true] at hr
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    have hw : (Simple.local r : Simple C p).wt Γ = true := by simpa [Simple.wt, Ctx.has] using hr.1
    have := Simple.eval_wt hwt hw hv
    exact hwt.setEnv_same hr.2 (by simpa [BTy.matchesB] using this)

/-- The locals an outcome of an external call binds, each a value of its
type: decoding checked it. -/
theorem bindData_wt : ∀ {xs : List (PrimTy × Var)} {vs : List Value} {Γ : Ctx} {σ σ' : State},
    RunWT C Γ H σ → bindData xs vs σ = .ok σ' → RunWT C (bindCtx xs Γ) H σ'
  | [], _, _, _, _, hwt, h => by cases h; exact hwt
  | _ :: _, [], _, _, _, _, h => by simp [bindData] at h
  | (p, x) :: xs, v :: vs, Γ, σ, σ', hwt, h => by
    simp only [bindData] at h
    split at h
    · rename_i hv
      show RunWT C (bindCtx xs (setBy x (.stack (.prim p)) Γ)) H σ'
      refine bindData_wt (hwt.setEnv ?_) h
      cases p <;> cases v <;> simp_all [PrimVal.fits, BTy.matchesB, Value.toSVal, SVal.hasTy]
    · cases h

end Effects

/-! ## The headline -/

theorem wt_if {c : Bool} {a b : Ctx} (h : (if c = true then some a else none) = some b) :
    c = true ∧ a = b := by
  split at h
  · exact ⟨‹_›, Option.some.inj h⟩
  · exact nomatch h

mutual

/-- **Type soundness, statement level.**  A statement whose locals are
used as declared, run from a well-typed state, ends in a state well-typed
under the context the check returns; the store typing only grows.  From
`uint x = 1;` the state binds `x` to a number and `Γ` learns `x : uint`;
from `alice.age = x;` storage still inhabits the layout. -/
theorem Stmt.run_wt : ∀ (s : Stmt C) {Γ Γ' : Ctx} {H : HeapTy} {σ σ' : State},
    RunWT C Γ H σ → s.wt Γ = some Γ' → s.run σ = .ok σ' →
      ∃ H', H.Extends H' ∧ RunWT C Γ' H' σ'
  | .assign l r, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    exact ⟨H, .refl H, hwt.write (Loc.resolve_wt hwt l hc.1 hr) (Src.value_wt hwt hc.2 hsv) h⟩
  | .rebind x r, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨σ₁, root, segs, hwt₁, hty, rfl⟩ := ARhs.bind_wt hwt hc.2 h
    exact ⟨H, .refl H, hwt₁.setEnv_same hc.1 (by simp [BTy.matchesB, hty])⟩
  | .assignLocal x r, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact ⟨H, .refl H,
      hwt.setEnv_same hc.1 (by simpa [BTy.matchesB] using Val.eval_wt hwt r hc.2 hv)⟩
  | .declLocal p x init, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Stmt.run] at h
    cases init with
    | none =>
      obtain ⟨w, hv, h⟩ := bind_ok_inv h
      cases hv; cases h
      exact ⟨H, .refl H, hwt.setEnv (by cases p <;> rfl)⟩
    | some e =>
      obtain ⟨w, hv, h⟩ := bind_ok_inv h
      cases h
      exact ⟨H, .refl H, hwt.setEnv
        (by simpa [BTy.matchesB] using Val.eval_wt hwt e (by simpa using hc) hv)⟩
  | .declStorage R x init, Γ, Γ', H, σ, σ', hwt, hs, h => by
    cases init with
    | none =>
      cases hs; cases h
      exact ⟨H, .refl H, hwt⟩
    | some r =>
      obtain ⟨hc, rfl⟩ := wt_if hs
      obtain ⟨σ₁, root, segs, hwt₁, hty, rfl⟩ := ARhs.bind_wt hwt hc h
      exact ⟨H, .refl H, hwt₁.setEnv (by simp [BTy.matchesB, hty])⟩
  | .opAssign op hop hp l r, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨v, _, h⟩ := bind_ok_inv h
    exact ⟨H, .refl H, OpLoc.store_wt hwt (compound_isArith hop) l hp hc.1 h⟩
  | .incDec op hp l, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    exact ⟨H, .refl H, (OpLoc.bump_wt hwt l hp hc hb).1⟩
  | .assignIncDec x op hp l _, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨σ₁, w⟩, hb, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨hwt₁, hw⟩ := OpLoc.bump_wt hwt l hp hc.2 hb
    exact ⟨H, .refl H, hwt₁.setEnv_same hc.1 (by simpa [BTy.matchesB] using hw)⟩
  | .push b v hd, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    refine ⟨H, .refl H, pushAt_wt hwt (SPath.resolve_wt hwt b hc.1 hr) ?_ h⟩
    intro slot w hslot hw
    cases v with
    | none =>
      cases hw
      exact hslot (defaultOk_of_defaultOkS (by simpa using hd))
    | some r =>
      obtain ⟨v, hv, hw⟩ := bind_ok_inv hw
      cases hw
      exact SVal.strip_hasTy (Src.value_wt hwt (by simpa using hc.2) hv)
  | .pop b, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    exact ⟨H, .refl H, popAt_wt hwt (SPath.resolve_wt hwt b hc hr) h⟩
  | .transfer r a, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨_, rfl⟩ := wt_if hs
    iterate 4 bind_inv h
    exact ⟨H, .refl H, hwt.transferAt h⟩
  | .declMem R x init hd, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    cases init with
    | none =>
      obtain ⟨⟨σ₁, id⟩, ha, h⟩ := bind_ok_inv h
      cases h
      obtain ⟨H', hout, hid⟩ := allocDefault_typed hwt.heapTyNodup hwt.heap hwt.heapWf
        (defaultOk_of_defaultOkS (by simpa using hd)) ha
      exact ⟨H', hout.ext, (hwt.ofCopyOut hout).setEnv (by simpa [BTy.matchesB] using hid)⟩
    | some r =>
      obtain ⟨H', σ₁, id, hext, hwt₁, hid, rfl⟩ := MRhs.bind_wt hwt (by simpa using hc) h
      exact ⟨H', hext, hwt₁.setEnv (by simpa [BTy.matchesB] using hid)⟩
  | .rebindMem x r, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨H', σ₁, id, hext, hwt₁, hid, rfl⟩ := MRhs.bind_wt hwt hc.2 h
    have hx : Ctx.has Γ x (.mem (.ref _)) = true := hc.1
    exact ⟨H', hext, hwt₁.setEnv_same hx (by simpa [BTy.matchesB] using hid)⟩
  | .assignFromMem l p, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    have hm := MPath.mval_wt hwt p hc.2 hm0
    rw [MVal.asRef_ok hid] at hm
    exact ⟨H, .refl H,
      hwt.write (Loc.resolve_wt hwt l hc.1 hr) (copyMem_hasTy hwt.heap hm hsv) h⟩
  | .assignMem l r, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    obtain ⟨mv, hmv, h⟩ := bind_ok_inv h
    exact ⟨H, .refl H, MLoc.write_wt hwt l (MSrc.mval_wt hwt hc.2 hmv) hc.1 h⟩
  | .delete l, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨cur, hcur, h⟩ := bind_ok_inv h
    have hty := Loc.resolve_wt hwt l hc hr
    exact ⟨H, .refl H,
      hwt.save hty (SVal.defaultOf_hasTy (findStorage_hasTy hwt.storage hty hcur)) h⟩
  | @Stmt.deleteMem _ T p hd, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    cases p with
    | var x =>
      obtain ⟨⟨σ₁, id⟩, ha, h⟩ := bind_ok_inv h
      cases h
      obtain ⟨H', hout, hid⟩ := allocDefault_typed hwt.heapTyNodup hwt.heap hwt.heapWf
        (defaultOk_of_defaultOkS hd) ha
      exact ⟨H', hout.ext, (hwt.ofCopyOut hout).setEnv_same hc (by simpa [BTy.matchesB] using hid)⟩
    | loc l =>
      obtain ⟨a, ha, h⟩ := bind_ok_inv h
      have hat := MLoc.addr_wt hwt l hc ha
      cases T with
      | prim p =>
        refine ⟨H, .refl H, writeAddr_wt hwt hat (Value.toMVal_hasTyH ?_) h⟩
        cases p <;> rfl
      | ref R =>
        obtain ⟨⟨σ₁, id⟩, hal, h⟩ := bind_ok_inv h
        obtain ⟨H', hout, hid⟩ := allocDefault_typed hwt.heapTyNodup hwt.heap hwt.heapWf
          (defaultOk_of_defaultOkS hd) hal
        exact ⟨H', hout.ext, writeAddr_wt (hwt.ofCopyOut hout) (hat.mono hout.ext) hid h⟩
  | .assignNew l n hn, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨hc, rfl⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    bind_inv h
    obtain ⟨nv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨σ₁, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    obtain ⟨H', hout, hmv⟩ :=
      copyStToM_typed hwt.heapTyNodup hwt.heap hwt.heapWf (newArrVal_hasTy hn nv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    have hwt₁ := hwt.ofCopyOut hout
    cases l with
    | store l =>
      obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
      obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
      exact ⟨H', hout.ext,
        hwt₁.write (Loc.resolve_wt hwt₁ l hc.1 hr) (copyMem_hasTy hwt₁.heap hmv hsv) h⟩
    | mem l => exact ⟨H', hout.ext, MLoc.write_wt hwt₁ l hmv hc.1 h⟩
  | .ite c thn els, Γ, Γ', H, σ, σ', hwt, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · split at hs
      · rename_i Γt Γe ht he
        obtain ⟨hle, rfl⟩ := wt_if hs
        simp only [Bool.and_eq_true] at hle
        obtain ⟨cv, _, h⟩ := bind_ok_inv h
        split at h
        · obtain ⟨H', hext, hwt'⟩ := Prog.run_wt thn hwt ht h
          exact ⟨H', hext, hwt'.weaken hle.1⟩
        · obtain ⟨H', hext, hwt'⟩ := Prog.run_wt els hwt he h
          exact ⟨H', hext, hwt'.weaken hle.2⟩
        · exact nomatch h
      · exact nomatch hs
    · exact nomatch hs
  | .require c, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨_, rfl⟩ := wt_if hs
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold guardOk at h
    split at h
    · cases h; exact ⟨H, .refl H, hwt⟩
    · exact nomatch h
    · exact nomatch h
  | .assert c, Γ, Γ', H, σ, σ', hwt, hs, h => by
    obtain ⟨_, rfl⟩ := wt_if hs
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold guardOk at h
    split at h
    · cases h; exact ⟨H, .refl H, hwt⟩
    · exact nomatch h
    · exact nomatch h
  | .revert, _, _, _, _, _, _, _, h => nomatch h
  | .call _ args _ ret body, Γ, Γ', H, σ, σ', hwt, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · rename_i Γ₁ h₁
      split at hs
      · rename_i Γ₂ h₂
        obtain ⟨hr, rfl⟩ := wt_if hs
        simp only [Stmt.run] at h
        obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
        obtain ⟨σ₂, hσ₂, h⟩ := bind_ok_inv h
        obtain ⟨H', hext, hwt₂⟩ :=
          Prog.run_wt body (CallRet.enter_wt (Arg.bindSeq_wt hwt h₁ hσ₁) ret) h₂ hσ₂
        exact ⟨H', hext, CallRet.leave_wt hwt₂ ret hr h⟩
      · exact nomatch hs
    · exact nomatch hs
  | .tryCall c rets ok err code pnc other, Γ, Γ', H, σ, σ', hwt, hs, h => by
    simp only [Stmt.wt] at hs
    split at hs
    · split at hs
      · rename_i Γ₁ Γ₂ Γ₃ Γ₄ h₁ h₂ h₃ h₄
        obtain ⟨hle, rfl⟩ := wt_if hs
        simp only [Bool.and_eq_true] at hle
        simp only [Stmt.run] at h
        obtain ⟨k, _, h⟩ := bind_ok_inv h
        split at h
        · exact nomatch h
        · obtain ⟨σ₁, hb, h⟩ := bind_ok_inv h
          obtain ⟨H', hext, hwt'⟩ := Prog.run_wt ok (bindData_wt hwt hb) h₁ h
          exact ⟨H', hext, hwt'.weaken hle.1.1.1⟩
        · obtain ⟨H', hext, hwt'⟩ := Prog.run_wt err hwt h₂ h
          exact ⟨H', hext, hwt'.weaken hle.1.1.2⟩
        · obtain ⟨σ₁, hb, h⟩ := bind_ok_inv h
          obtain ⟨H', hext, hwt'⟩ := Prog.run_wt pnc (bindData_wt hwt hb) h₃ h
          exact ⟨H', hext, hwt'.weaken hle.1.2⟩
        · obtain ⟨H', hext, hwt'⟩ := Prog.run_wt other hwt h₄ h
          exact ⟨H', hext, hwt'.weaken hle.2⟩
      · exact nomatch hs
    · exact nomatch hs

/-- **Type soundness, block level.** -/
theorem Prog.run_wt : ∀ (P : List (Stmt C)) {Γ Γ' : Ctx} {H : HeapTy} {σ σ' : State},
    RunWT C Γ H σ → Prog.wt Γ P = some Γ' → Prog.run σ P = .ok σ' →
      ∃ H', H.Extends H' ∧ RunWT C Γ' H' σ'
  | [], Γ, Γ', H, σ, σ', hwt, hs, h => by
    cases hs; cases h
    exact ⟨H, .refl H, hwt⟩
  | s :: P, Γ, Γ', H, σ, σ', hwt, hs, h => by
    simp only [Prog.wt] at hs
    split at hs
    · rename_i Γ₁ h₁
      obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
      obtain ⟨H₁, hext₁, hwt₁⟩ := Stmt.run_wt s hwt h₁ hσ₁
      obtain ⟨H₂, hext₂, hwt₂⟩ := Prog.run_wt P hwt₁ hs h
      exact ⟨H₂, hext₁.trans hext₂, hwt₂⟩
    · exact nomatch hs

end

/-! ## Where a run starts, and what the headline buys -/

theorem lookupBy_map_snd {k : Name} {f : Ty → SVal} :
    ∀ l : List (Name × Ty), lookupBy k (l.map fun (n, T) => (n, f T)) = (lookupBy k l).map f
  | [] => rfl
  | (n, T) :: rest => by
    by_cases h : k = n
    · simp [lookupBy, h]
    · simp [lookupBy, h, lookupBy_map_snd rest]

/-- A contract starts well-typed: each root at its type's default, no
locals, an empty heap.  `StandardExample` starts in `State.exampleStore`,
which is `RunWT` (`exampleStore_wt`). -/
theorem RunWT.init {σ : State} (hnd : nodupKeysB C.vars = true)
    (hok : C.vars.all (·.2.defaultOkS) = true)
    (hst : σ.storage = C.initStorage) (hheap : σ.heap = []) : RunWT C [] [] σ where
  layoutNodup := hnd
  storage := by
    rw [hst]
    refine List.all_eq_true.mpr fun g hg => ?_
    show (match lookupBy g.1 C.initStorage with
      | some v => v.hasTy g.2
      | none => false) = true
    simp only [Contract.initStorage, lookupBy_map_snd, lookupBy_eq_of_nodup hnd hg, Option.map]
    exact defaultForTy_hasTy (defaultOk_of_defaultOkS (List.all_eq_true.mp hok g hg))
  env := fun x bt hx => nomatch hx
  heapTyNodup := rfl
  heap := rfl
  heapWf := fun i _ => by rw [hheap]; rfl

/-- `StandardExample`'s store is well-typed. -/
theorem exampleStore_wt : RunWT StandardExample [] [] State.exampleStore :=
  RunWT.init (by decide) (by decide) initStorage_standardExample.symm rfl

/-- **Storage stays well-typed.**  Assume `wellFormed(storage)` once and it
holds after every checked run: after `Person storage p = alice;
p.age = 10;` storage still inhabits `StandardExample`'s layout. -/
theorem Prog.run_storage_wt {Γ Γ' : Ctx} {H : HeapTy} {σ σ' : State} {P : Prog C}
    (hwt : RunWT C Γ H σ) (hP : Prog.wt Γ P = some Γ') (h : Prog.run σ P = .ok σ') :
    wellTypedStorageB C.layout σ'.storage = true :=
  let ⟨_, _, hwt'⟩ := Prog.run_wt P hwt hP h
  hwt'.storage

/-- `aliasWrite` (`Person storage p = alice; p.age = 10; uint x = alice.age;
assert(x == 10);`) uses its locals as it declares them. -/
example : Prog.wt [] aliasWrite = some [(.user "p", .path (.ref (.struct "Person"))),
    (.user "x", .stack (.prim .uint))] := by decide

/-- Reading a `uint` local as a `bool` is refused: `uint x = 1; bool y = x;`,
which `sol{ … }` already rejects, written as a term. -/
example : Prog.wt [] ([.declLocal .uint (.user "x") (some (.simple (.lit 1 rfl))),
    .declLocal .bool (.user "y") (some (.simple (.local (.user "x"))))] :
      Prog StandardExample) = none := by decide

/-- So `aliasWrite` from `StandardExample`'s store leaves storage
well-typed. -/
example {σ' : State} (h : Prog.run State.exampleStore aliasWrite = .ok σ') :
    wellTypedStorageB StandardExample.layout σ'.storage = true :=
  Prog.run_storage_wt (Γ' := [(.user "p", .path (.ref (.struct "Person"))),
    (.user "x", .stack (.prim .uint))]) exampleStore_wt (by decide) h

end Solidity
