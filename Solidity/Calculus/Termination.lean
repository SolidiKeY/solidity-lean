import Solidity.Calculus.Progress
import Solidity.Calculus.Uniqueness
import Solidity.Calculus.Notation

/-!
# Termination: symbolic execution always ends

Every rule `Stmt.step` fires leaves a premise that weighs less than the
statement it replaces (`Stmt.step_smaller`), so a measure on formulas goes
down at every step (`Fml.step_decreases`): there is no infinite chain of
rule applications (`Fml.step_wellFounded`), and with enough fuel the
strategy of `Symex.lean` leaves no modality (`symex_normalizes`).  With
`Progress.lean` it stops exactly there.  This is mini-solkey's
`Ch12_Termination`.

**The weight.**  A part a rule must capture before it can run costs `16`
more than the part itself, a simple one `1` more (`Val.pen`, `SPath.pen`,
`MPath.pen`): that is what pays for the declaration the capture adds.  The
cost of a part is counted where the rules look at it, so a receiver, an
index, an operand or a source is charged, and a declaration's initializer,
which no rule captures, is not.

The smallness is proved about what `Stmt.step` fires (`Stmt.step_smaller`)
and holds of **every derivation** (`Taclet.smaller`): a statement has one
rule, and it is the dispatcher's (`Taclet.eq_step`).  The side conditions
are what make it so: without them `storageFieldRead_unfold_rightFst` would
hold of `lhs = sp.fld` too, leaving `lhs = sp'.fld`, as heavy as it
started.

**The measure.**  `2 ^ weight P * (measure φ + 1)` for `⟨P⟩ φ`:
exponential in the program, because a branch (`ifElseSplit`, and a
conditional lowered by `ternaryToIf`) copies the rest of the program and
the postcondition into both goals.  An `if` weighs `2` more than its heavier
branch, so its two goals cost `2 ^ (w₁ + ω) + 2 ^ (w₂ + ω) < 2 ^ (w + ω)`.
-/

namespace Solidity

variable {C : Contract}

/-! ## Weights -/

/-- What a value in a captured position costs beyond itself: `1` if it is
simple, `16` if a rule must capture it first. -/
def Val.pen {p : PrimTy} (v : Val C p) : Nat := if v.isSimple then 1 else 16

/-- What a storage receiver costs beyond itself: `1` for an alias or a
state variable, `16` for a path a rule must bind to an alias first. -/
def SPath.pen {T : Ty} (b : SPath C T) : Nat := if b.isSimple then 1 else 16

/-- What a memory receiver costs beyond itself: `1` for a memory local, `16`
for a path a rule must bind first. -/
def MPath.pen {T : Ty} (b : MPath C T) : Nat := if b.isSimple then 1 else 16

mutual

/-- Example: `alice` costs `1`, `alice.account` costs `2`, and
`alice.account.balance` costs `18`: its receiver `alice.account` is not
simple. -/
def SPath.cost : {T : Ty} → SPath C T → Nat
  | _, .alias _ => 1
  | _, .loc l => l.cost

/-- Example: `total` costs `1`, `balances[x]` costs `4`. -/
def Loc.cost : {T : Ty} → Loc C T → Nat
  | _, .root .. => 1
  | _, .field b _ _ => b.cost + b.pen
  | _, .index _ b i => b.cost + b.pen + i.cost + i.pen

/-- Example: a memory local `m` costs `1`, `m.age` costs `2`. -/
def MPath.cost : {T : Ty} → MPath C T → Nat
  | _, .var _ => 1
  | _, .loc l => l.cost

def MLoc.cost : {T : Ty} → MLoc C T → Nat
  | _, .field b _ _ => b.cost + b.pen
  | _, .index _ b i => b.cost + b.pen + i.cost + i.pen

/-- Example: `x + 1` costs `4`; `alice.age + 1` costs `3 + 16 + 2 = 21`,
because `binopUnfoldLeft` captures `alice.age` first.  A conditional costs
`4` more than its parts: lowered to an `if`, each branch keeps one. -/
def Val.cost : {p : PrimTy} → Val C p → Nat
  | _, .simple _ => 1
  | _, .read l => l.cost + 1
  | _, .binop _ _ _ a b => a.cost + a.pen + b.cost + b.pen
  | _, .unop _ _ _ a => a.cost + a.pen
  | _, .ternary c a b => c.cost + c.pen + a.cost + b.cost + 4
  | _, .readMem l => l.cost + 1
  | _, .len b _ => b.cost + b.pen + 1
  | _, .mlen b _ => b.cost + b.pen + 1

end

/-- A source is charged like an operand: `16` more unless it is simple. -/
def Src.cost {T : Ty} : Src C T → Nat
  | .val v => v.cost + v.pen
  | .copy p _ => p.cost + p.pen

def ARhs.cost {R : RefTy} : ARhs C R → Nat
  | .path p => p.cost
  | .push b _ => b.cost + b.pen + 1

def MRhs.cost {R : RefTy} : MRhs C R → Nat
  | .alias p => p.cost
  | .copy p _ => p.cost + p.pen
  | .newArr _ _ => 1

/-- A fresh array's target costs what the location does. -/
def NewLhs.cost {R : RefTy} : NewLhs C R → Nat
  | .store l => l.cost
  | .mem l => l.cost

def MSrc.cost {T : Ty} : MSrc C T → Nat
  | .val v => v.cost + v.pen
  | .ref p => p.cost + p.pen

def OpLoc.cost {p : PrimTy} : OpLoc C p → Nat
  | .local _ | .root .. => 1
  | .field b _ _ => b.cost + b.pen
  | .index _ b _ => b.cost + b.pen + 1
  | .mfield b _ _ => b.cost + b.pen
  | .mindex _ b _ => b.cost + b.pen + 1

mutual

/-- The weight of a statement.

Example: `x = 1;` weighs `2`, `alice.age = 10;` weighs `5`, and
`if (c) { x = 1; } else { x = 2; }` weighs `2 + 2 + 2 = 6`: an `if` weighs
its heavier branch, not both. -/
def Stmt.weight : Stmt C → Nat
  | .assign l r => l.cost + r.cost + 1
  | .rebind _ r => r.cost + 1
  | .assignLocal _ v => v.cost + 1
  | .declLocal _ _ none => 1
  | .declLocal _ _ (some e) => e.cost + 2
  | .declStorage _ _ none => 1
  | .declStorage _ _ (some r) => r.cost + 2
  | .opAssign _ _ _ l r => l.cost + r.cost + r.pen + 1
  | .incDec _ _ l => l.cost + 1
  | .assignIncDec _ _ _ l _ => l.cost + 1
  | .push b none _ => b.cost + b.pen + 1
  | .push b (some r) _ => b.cost + b.pen + r.cost + 1
  | .pop b => b.cost + b.pen + 1
  | .transfer r a => r.cost + r.pen + a.cost + a.pen + 1
  | .declMem _ _ none _ => 1
  | .declMem _ _ (some r) _ => r.cost + 2
  | .rebindMem _ r => r.cost + 1
  | .assignFromMem l p => l.cost + p.cost + 1
  | .assignMem l r => l.cost + r.cost + 1
  | .delete l => l.cost + 1
  | .deleteMem p _ => p.cost + 1
  | .assignNew l _ _ => l.cost + 7
  | .ite c thn els => c.cost + c.pen + max (Prog.weight thn) (Prog.weight els) + 2
  | .require c | .assert c => c.cost + c.pen + 2
  | .revert => 1

/-- The weight of a block: the sum of its statements'. -/
def Prog.weight : List (Stmt C) → Nat
  | [] => 0
  | s :: P => s.weight + Prog.weight P

end

/-! ## Every part costs something -/

/-- Example: `x` has penalty `1`, `x + 1` has `16`. -/
theorem Val.pen_pos {p : PrimTy} (v : Val C p) : 1 ≤ v.pen := by
  unfold Val.pen; split <;> omega
/-- Example: `alice` has penalty `1`, `people[i]` has `16`. -/
theorem SPath.pen_pos {T : Ty} (b : SPath C T) : 1 ≤ b.pen := by
  unfold SPath.pen; split <;> omega
/-- Example: a memory local `m` has penalty `1`, `m.inner` has `16`. -/
theorem MPath.pen_pos {T : Ty} (b : MPath C T) : 1 ≤ b.pen := by
  unfold MPath.pen; split <;> omega
/-- Example: no value is charged more than `16`, not even `a ? b : c`. -/
theorem Val.pen_le {p : PrimTy} (v : Val C p) : v.pen ≤ 16 := by
  unfold Val.pen; split <;> omega
/-- Example: no receiver is charged more than `16`, not even `people[i].account`. -/
theorem SPath.pen_le {T : Ty} (b : SPath C T) : b.pen ≤ 16 := by
  unfold SPath.pen; split <;> omega
/-- Example: no memory receiver is charged more than `16`. -/
theorem MPath.pen_le {T : Ty} (b : MPath C T) : b.pen ≤ 16 := by
  unfold MPath.pen; split <;> omega

/-- Example: the `x` of `total = x;` is charged `1`. -/
theorem Val.pen_simple {p : PrimTy} (s : Simple C p) : (Val.simple s).pen = 1 := rfl
/-- Example: the `sp` of `sp.age = 1;` is charged `1`. -/
theorem SPath.pen_alias {R : RefTy} (x : Var) : (SPath.alias (C := C) (R := R) x).pen = 1 := rfl
/-- Example: the `m` of `m.age = 1;` is charged `1`. -/
theorem MPath.pen_var {R : RefTy} (x : Var) : (MPath.var (C := C) (R := R) x).pen = 1 := rfl
/-- Example: the `alice` of `alice.age = 1;` is charged `1`. -/
theorem SPath.pen_root {T : Ty} (r : Name) (h : C.rootType r = some T) :
    (SPath.loc (Loc.root r h)).pen = 1 := rfl
/-- Example: the `alice.account` of `alice.account.balance = 1;` is charged `16`. -/
theorem SPath.pen_field {s : Name} {T : Ty} (b : SPath C (.struct s)) (f : Name)
    (h : C.fieldType s f = some T) : (SPath.loc (Loc.field b f h)).pen = 16 := rfl
/-- Example: the `people[i]` of `people[i].age = 1;` is charged `16`. -/
theorem SPath.pen_index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (b : SPath C (.ref R)) (i : Val C k) : (SPath.loc (Loc.index it b i)).pen = 16 := rfl
/-- Example: the `m.inner` of `m.inner.age = 1;` is charged `16`. -/
theorem MPath.pen_loc {T : Ty} (l : MLoc C T) : (MPath.loc l).pen = 16 := rfl
/-- Example: the `alice.age` of `total = alice.age;` is charged `16`. -/
theorem Val.pen_read {p : PrimTy} (l : Loc C (.prim p)) : (Val.read l).pen = 16 := rfl
/-- Example: the `m.age` of `total = m.age;` is charged `16`. -/
theorem Val.pen_readMem {p : PrimTy} (l : MLoc C (.prim p)) : (Val.readMem l).pen = 16 := rfl
/-- Example: the `x + 1` of `total = x + 1;` is charged `16`. -/
theorem Val.pen_binop {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
    (a b : Val C p) : (Val.binop op h hq a b).pen = 16 := rfl
/-- Example: the `!b` of `require(!b);` is charged `16`. -/
theorem Val.pen_unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
    (a : Val C p) : (Val.unop op h hq a).pen = 16 := rfl
/-- Example: the `values.length` of `total = values.length;` is charged `16`. -/
theorem Val.pen_len {p : PrimTy} {E : Ty} (b : SPath C (.array E)) (h : p = .uint) :
    (Val.len b h).pen = 16 := rfl
/-- Example: the `xs.length` of `total = xs.length;` is charged `16`. -/
theorem Val.pen_mlen {p : PrimTy} {E : Ty} (b : MPath C (.array E)) (h : p = .uint) :
    (Val.mlen b h).pen = 16 := rfl
/-- Example: the `c ? 1 : 2` of `total = c ? 1 : 2;` is charged `16`. -/
theorem Val.pen_ternary {p : PrimTy} (c : Val C .bool) (a b : Val C p) :
    (Val.ternary c a b).pen = 16 := rfl

/-- A receiver `Stmt.step` found simple is charged `1`.

Example: `sp` in `sp.age = 1;`. -/
theorem SPath.pen_eq_one {T : Ty} {b : SPath C T} (h : b.isSimple = true) : b.pen = 1 := by
  simp [SPath.pen, h]
/-- A receiver `Stmt.step` found not simple is charged `16`.

Example: `people[i]` in `people[i].age = 1;`. -/
theorem SPath.pen_eq_16 {T : Ty} {b : SPath C T} (h : ¬ b.isSimple = true) : b.pen = 16 := by
  simp [SPath.pen, h]
/-- A value `Stmt.step` found not simple is charged `16`.

Example: `x + 1` in `total = x + 1;`. -/
theorem Val.pen_eq_16 {p : PrimTy} {v : Val C p} (h : v.isSimple = false) : v.pen = 16 := by
  simp [Val.pen, h]

mutual
/-- Every part costs at least `1`.

Example: `alice` costs `1`, `people[i].age` costs `20`. -/
theorem SPath.cost_pos : {T : Ty} → (b : SPath C T) → 1 ≤ b.cost
  | _, .alias _ => by simp [SPath.cost]
  | _, .loc l => by simpa [SPath.cost] using l.cost_pos
/-- Example: `total` costs `1`. -/
theorem Loc.cost_pos : {T : Ty} → (l : Loc C T) → 1 ≤ l.cost
  | _, .root .. => by simp [Loc.cost]
  | _, .field b _ _ => by have := b.pen_pos; simp only [Loc.cost]; omega
  | _, .index _ b _ => by have := b.pen_pos; simp only [Loc.cost]; omega
/-- Example: a memory local `m` costs `1`. -/
theorem MPath.cost_pos : {T : Ty} → (b : MPath C T) → 1 ≤ b.cost
  | _, .var _ => by simp [MPath.cost]
  | _, .loc l => by simpa [MPath.cost] using l.cost_pos
/-- Example: `m.age` costs `2`. -/
theorem MLoc.cost_pos : {T : Ty} → (l : MLoc C T) → 1 ≤ l.cost
  | _, .field b _ _ => by have := b.pen_pos; simp only [MLoc.cost]; omega
  | _, .index _ b _ => by have := b.pen_pos; simp only [MLoc.cost]; omega
/-- Example: `1` and `x` cost `1`. -/
theorem Val.cost_pos : {p : PrimTy} → (v : Val C p) → 1 ≤ v.cost
  | _, .simple _ => by simp [Val.cost]
  | _, .read _ | _, .readMem _ | _, .ternary .. => by simp [Val.cost]
  | _, .binop _ _ _ a _ | _, .unop _ _ _ a => by have := a.pen_pos; simp only [Val.cost]; omega
  | _, .len b _ => by have := b.pen_pos; simp only [Val.cost]; omega
  | _, .mlen b _ => by have := b.pen_pos; simp only [Val.cost]; omega
end

/-- What a rule's premise owes the statement it replaces: new statements
weigh less, and each goal of a branch at least `2` less. -/
def Premise.Smaller (s : Stmt C) : Premise C → Prop
  | .update _ | .done _ => True
  | .unfold P => Prog.weight P < s.weight
  | .split _ _ P Q => Prog.weight P + 2 ≤ s.weight ∧ Prog.weight Q + 2 ≤ s.weight

/-- The rule leaves a premise smaller than its statement. -/
def Step.Small {k : Nat} {m : Modality} {s : Stmt C} (st : Step k m s) : Prop :=
  st.premise.Smaller s

/-! ## The obligations -/

open Lean Elab Tactic Meta in
/-- Give `omega` the bounds of every cost and penalty in the goal: a cost is
at least `1`, a penalty between `1` and `16`. -/
elab "cost_facts" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let table : List (Lean.Name × List Lean.Name) :=
    [(``SPath.cost, [``SPath.cost_pos]), (``Loc.cost, [``Loc.cost_pos]),
     (``MPath.cost, [``MPath.cost_pos]), (``MLoc.cost, [``MLoc.cost_pos]),
     (``Val.cost, [``Val.cost_pos]),
     (``Val.pen, [``Val.pen_pos, ``Val.pen_le]), (``SPath.pen, [``SPath.pen_pos, ``SPath.pen_le]),
     (``MPath.pen, [``MPath.pen_pos, ``MPath.pen_le])]
  let found ← IO.mkRef (#[] : Array Expr)
  tgt.forEachWhere (fun e => e.getAppNumArgs == 3 && !e.hasLooseBVars && table.any fun (n, _) => e.isAppOf n)
    fun e => found.modify (·.push e)
  let mut seen : Array Expr := #[]
  for e in (← found.get) do
    if seen.contains e then continue
    seen := seen.push e
    let some (_, lemmas) := table.find? fun (n, _) => e.isAppOf n | continue
    for l in lemmas do
      let fact ← mkAppM l #[e.appArg!]
      liftMetaTactic fun g => do
        let g ← g.assert `hc (← inferType fact) fact
        let (_, g) ← g.intro1P
        pure [g]

/-- The simp set that computes a weight down to its atoms, with the
penalties the branch facts fix, then `omega`. -/
syntax "weigh" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| weigh) => `(tactic| weigh [])
  | `(tactic| weigh [$ts,*]) => `(tactic| (
    simp only [Step.Small, Premise.Smaller, Prog.weight, Stmt.weight, List.cons_append,
      List.nil_append, Hole.fill, MHole.fill, VHole.fill, SPath.cost, Loc.cost, MPath.cost,
      MLoc.cost, Val.cost, Src.cost, ARhs.cost, MRhs.cost, MSrc.cost, OpLoc.cost, NewLhs.cost,
      NewLhs.fill, Val.pen_simple, Val.pen_len, Val.pen_mlen,
      SPath.pen_alias, MPath.pen_var, SPath.pen_root, SPath.pen_field, SPath.pen_index,
      MPath.pen_loc, Val.pen_read, Val.pen_readMem, Val.pen_binop, Val.pen_unop,
      Val.pen_ternary, $ts,*]
    cost_facts
    omega))

variable {k : Nat} {m : Modality}

/-- Step 1 on a storage read: an unfolded receiver or index costs its
declaration and less than the `16` it was charged.

Example: `x = people[i].age;` unfolds into `Person storage sp = people[i];
x = sp.age;`, of weights `6` and `4`, below the `22` it started from. -/
theorem Hole.readStep_small {T : Ty} (lhs : Hole C T) (ht : lhs.isTarget = true)
    {root : (r : Name) → (h : C.rootType r = some T) → Step k m (lhs.fill (.loc (.root r h)))}
    {field : {s : Name} → (sp : SPath C (.struct s)) → (f : Name) →
      (hf : C.fieldType s f = some T) → sp.isSimple = true →
      Step k m (lhs.fill (.loc (.field sp f hf)))}
    {index : {R : RefTy} → {kp : PrimTy} → (it : IndexTy R kp T) → (sp : SPath C (.ref R)) →
      (ie : Simple C kp) → sp.isSimple = true →
      Step k m (lhs.fill (.loc (.index it sp (.simple ie))))}
    (hr : ∀ r h, (root r h).Small)
    (hf : ∀ {s} (sp : SPath C (.struct s)) f hf hs, (field sp f hf hs).Small)
    (hi : ∀ {R kp} (it : IndexTy R kp T) sp ie hs, (index it sp ie hs).Small) :
    ∀ l, (lhs.readStep ht root field index l).Small
  | .root r h => hr r h
  | .field b f h => by
    simp only [Hole.readStep]
    split
    · exact hf b f h _
    · rename_i hb
      cases lhs <;> weigh [SPath.pen_eq_16 hb]
  | .index it b i => by
    simp only [Hole.readStep]
    split
    · rename_i hb
      cases i with
      | simple ie => exact hi it b ie hb
      | _ => cases lhs <;> weigh
    · rename_i hb
      cases lhs <;> weigh [SPath.pen_eq_16 hb]

/-- Step 1 on a memory read.

Example: `x = m.inner.age;` unfolds into `Inner memory mv = m.inner;
x = mv.age;`. -/
theorem MHole.readStep_small {T : Ty} (lhs : MHole C T) (ht : lhs.isTarget = true)
    {field : {s : Name} → (mv : Var) → (f : Name) → (hf : C.fieldType s f = some T) →
      Step k m (lhs.fill (.field (.var mv) f hf))}
    {index : {R : RefTy} → (a : ArrTy R T) → (mv : Var) → (ie : Simple C .uint) →
      Step k m (lhs.fill (.index a (.var mv) (.simple ie)))}
    (hf : ∀ {s} mv f (hf : C.fieldType s f = some T), (field mv f hf).Small)
    (hi : ∀ {R} (a : ArrTy R T) mv ie, (index a mv ie).Small) :
    ∀ l, (lhs.readStep ht field index l).Small
  | .field (.var _) _ _ => hf ..
  | .field (.loc _) _ _ => by simp only [MHole.readStep]; cases lhs <;> weigh
  | .index _ (.var _) (.simple _) => hi ..
  | .index _ (.var _) (.read _) | .index _ (.var _) (.binop ..) | .index _ (.var _) (.unop ..)
  | .index _ (.var _) (.ternary ..) | .index _ (.var _) (.readMem _) | .index _ (.var _) (.len ..)
  | .index _ (.var _) (.mlen ..) => by
    simp only [MHole.readStep]; cases lhs <;> weigh
  | .index _ (.loc _) _ => by simp only [MHole.readStep]; cases lhs <;> weigh

/-- A conditional lowered to a branch, or its condition captured.

Example: `x = c ? 1 : 2;`, `c` a `bool` local (weight `9`), becomes
`if (c) { x = 1; } else { x = 2; }` (weight `6`). -/
theorem ternaryStep_small {p : PrimTy} (lhs : VHole C p) (hl : lhs.isTarget = true)
    (c : Val C .bool) (a b : Val C p) : (ternaryStep (k := k) (m := m) lhs hl c a b).Small := by
  cases c <;> simp only [ternaryStep] <;> cases lhs <;> weigh

/-- Lowering a conditional first keeps a rule small.

Example: `people[i].age = b ? 1 : 2;` branches before it captures `people[i]`. -/
theorem VHole.lower_small {p : PrimTy} (lhs : VHole C p) (hl : lhs.isTarget = true)
    (e : Val C p) {other : e.notTernary = true → Step k m (lhs.fill e)}
    (h : ∀ ht, (other ht).Small) : (lhs.lower hl e other).Small := by
  cases e with
  | ternary c a b => exact ternaryStep_small lhs hl c a b
  | _ => exact h _

/-- A value written: a simple one by an update, any other captured.

Example: `total = x + 1;` becomes `uint se = x + 1; total = se;`. -/
theorem VHole.step_small {p : PrimTy} (lhs : VHole C p) (hl : lhs.isTarget = true)
    {simple : (se : Simple C p) → Step k m (lhs.fill (.simple se))}
    (hs : ∀ se, (simple se).Small) (e : Val C p)
    {capture : e.isSimple = false → e.notTernary = true → Step k m (lhs.fill e)}
    (hc : ∀ hn ht, (capture hn ht).Small) : (lhs.step hl simple e capture).Small := by
  cases e with
  | simple se => exact hs se
  | ternary c a b => exact ternaryStep_small lhs hl c a b
  | _ => exact hc _ _

/-- `&&` and `||` branch on their left operand, any other operator captures
its right one.

Example: `b = ok && people[i].adult;` becomes
`if (ok) { b = people[i].adult; b = b && true; } else { b = false; }`. -/
theorem binopRightStep_small {p q : PrimTy} (x : Var) (op : BinOp) (hop : op.accepts p = true)
    (hq : op.ret p = q) (se : Simple C p) (nse : Val C p) (hn : nse.isSimple = false) :
    (binopRightStep (k := k) (m := m) x op hop hq se nse hn).Small := by
  cases op <;> cases p <;> cases q <;>
    first
      | (unfold binopRightStep; weigh [Val.pen_eq_16 hn])
      | (exfalso; revert hop; decide)
      | (exfalso; revert hq; decide)

/-- A local assigned.

Example: `x = people[i].age;` (weight `22`) unfolds into
`Person storage sp = people[i]; x = sp.age;` (weights `6` and `4`). -/
theorem localStep_small {p : PrimTy} (x : Var) :
    ∀ v : Val C p, (localStep (k := k) (m := m) x v).Small
  | .simple _ => trivial
  | .read l => by
    simp only [localStep]
    refine Hole.readStep_small (.local x) rfl (fun _ _ => ?_) (fun _ _ _ _ => ?_)
      (fun it _ _ _ => ?_) l
    · trivial
    · trivial
    · cases it <;> trivial
  | .binop _ _ _ (.simple _) (.simple _) => trivial
  | .binop op hop hq (.simple se) (.read _) | .binop op hop hq (.simple se) (.binop ..)
  | .binop op hop hq (.simple se) (.unop ..) | .binop op hop hq (.simple se) (.ternary ..)
  | .binop op hop hq (.simple se) (.readMem _) | .binop op hop hq (.simple se) (.len ..)
  | .binop op hop hq (.simple se) (.mlen ..) => by
    simp only [localStep]; exact binopRightStep_small x op hop hq se _ rfl
  | .binop _ _ _ (.read _) _ | .binop _ _ _ (.binop ..) _ | .binop _ _ _ (.unop ..) _
  | .binop _ _ _ (.ternary ..) _ | .binop _ _ _ (.readMem _) _ | .binop _ _ _ (.len ..) _
  | .binop _ _ _ (.mlen ..) _ => by
    simp only [localStep]; weigh
  | .unop _ _ _ (.simple _) => trivial
  | .unop _ _ _ (.read _) | .unop _ _ _ (.binop ..) | .unop _ _ _ (.unop ..)
  | .unop _ _ _ (.ternary ..) | .unop _ _ _ (.readMem _) | .unop _ _ _ (.len ..)
  | .unop _ _ _ (.mlen ..) => by simp only [localStep]; weigh
  | .len b _ => by
    simp only [localStep]
    split
    · trivial
    · weigh [SPath.pen_eq_16 ‹_›]
  | .mlen (.var _) _ => trivial
  | .mlen (.loc _) _ => by simp only [localStep]; weigh
  | .ternary c a b => ternaryStep_small (.local x) rfl c a b
  | .readMem l => by
    simp only [localStep]
    refine MHole.readStep_small (.local x) rfl (fun _ _ _ => ?_) (fun _ _ _ => ?_) l <;> trivial

/-- An alias bound.

Example: `lsv = people[i].account;` unfolds into
`Person storage sp = people[i]; lsv = sp.account;`. -/
theorem rebindStep_small {R : RefTy} (x : Var) :
    ∀ r : ARhs C R, (rebindStep (k := k) (m := m) x r).Small
  | .path (.alias _) => trivial
  | .path (.loc l) => by
    simp only [rebindStep]
    refine Hole.readStep_small (.rebind x) rfl (fun _ _ => ?_) (fun _ _ _ _ => ?_)
      (fun it _ _ _ => ?_) l
    · trivial
    · trivial
    · cases it
      · trivial
      · dsimp only; split <;> trivial
  | .push b _ => by
    simp only [rebindStep]
    split
    · split <;> trivial
    · weigh [SPath.pen_eq_16 ‹_›]

/-- A storage copy into a member or an entry.

Example: `alice.account = bob.account;` binds the source first:
`Account storage sp = bob.account; alice.account = sp;`. -/
theorem copyStep_small {R : RefTy} (l : Loc C (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (hl : l.isTarget = true) (hr : l.isRoot = false)
    {copy : (sp2 : SPath C (.ref R)) → sp2.isSimple = true → Step k m (.assign l (.copy sp2 hm))}
    (hc : ∀ sp2 h, (copy sp2 h).Small) : ∀ sp2, (copyStep l hm hl hr copy sp2).Small
  | .alias _ => hc _ _
  | .loc l' => Hole.readStep_small (.copy l hm) hl (fun _ _ => hc _ _) (fun _ _ _ _ => by weigh)
      (fun _ _ _ _ => by weigh) l'

/-- A storage write: receiver, then index, then source.

Example: `people[i].age = 10;` (weight `23`) unfolds into
`uint se = 10; Person storage sp = people[i]; sp.age = se;`, of weights
`3`, `6` and `5`. -/
theorem assignStep_small {T : Ty} :
    ∀ (l : Loc C T) (r : Src C T), (assignStep (k := k) (m := m) l r).Small
  | .root r h, .val e => by
    simp only [assignStep]
    refine VHole.step_small _ rfl (fun _ => ?_) e (fun he _ => ?_)
    · trivial
    · weigh [Val.pen_eq_16 he]
  | .root _ _, .copy (.alias _) _ => trivial
  | .root r h, .copy (.loc l) hm => by
    simp only [assignStep]
    refine Hole.readStep_small (.copy (.root r h) hm) rfl (fun _ _ => ?_) (fun _ _ _ _ => ?_)
      (fun it _ _ _ => ?_) l
    · trivial
    · trivial
    · cases it <;> trivial
  | .field b f hf, .val e => by
    simp only [assignStep]
    split
    · rename_i hb
      refine VHole.step_small _ rfl (fun _ => ?_) e (fun he _ => ?_)
      · trivial
      · weigh [Val.pen_eq_16 he, SPath.pen_eq_one hb]
    · exact VHole.lower_small _ rfl e (fun _ => by weigh [SPath.pen_eq_16 ‹_›])
  | .field b f hf, .copy sp2 hm => by
    simp only [assignStep]
    split
    · exact copyStep_small _ hm _ rfl (fun _ _ => by trivial) sp2
    · weigh [SPath.pen_eq_16 ‹_›]
  | .index it b i, .val e => by
    simp only [assignStep]
    split
    · rename_i hb
      cases i with
      | simple ie =>
        refine VHole.step_small _ rfl (fun _ => ?_) e (fun he _ => ?_)
        · cases it <;> trivial
        · weigh [Val.pen_eq_16 he, SPath.pen_eq_one hb]
      | _ => exact VHole.lower_small _ rfl e (fun _ => by weigh [SPath.pen_eq_one hb])
    · exact VHole.lower_small _ rfl e (fun _ => by weigh [SPath.pen_eq_16 ‹_›])
  | .index it b i, .copy sp2 hm => by
    simp only [assignStep]
    split
    · rename_i hb
      cases i with
      | simple ie =>
        refine copyStep_small _ hm _ rfl (fun _ _ => ?_) sp2
        cases it <;> trivial
      | _ => weigh [SPath.pen_eq_one hb]
    · weigh [SPath.pen_eq_16 ‹_›]

/-- A storage location written from memory: receiver, then index.

Example: `people[i + 1] = m;` captures the index:
`uint ie = i + 1; people[ie] = m;`. -/
theorem assignFromMemStep_small {R : RefTy} :
    ∀ (l : Loc C (.ref R)) (p : MPath C (.ref R)), (assignFromMemStep (k := k) (m := m) l p).Small
  | .root _ _, _ => trivial
  | .field b _ _, _ => by
    simp only [assignFromMemStep]
    split
    · trivial
    · weigh [SPath.pen_eq_16 ‹_›]
  | .index it b i, _ => by
    simp only [assignFromMemStep]
    split
    · rename_i hb
      cases it <;> cases i <;> first | trivial | weigh [SPath.pen_eq_one hb]
    · weigh [SPath.pen_eq_16 ‹_›]

/-- `delete`: receiver, then index.

Example: `delete people[i].account;` unfolds into
`Person storage sp = people[i]; delete sp.account;`. -/
theorem deleteStep_small {T : Ty} : ∀ l : Loc C T, (deleteStep (k := k) (m := m) l).Small
  | .root _ _ => trivial
  | .field b _ _ => by
    simp only [deleteStep]
    split
    · trivial
    · weigh [SPath.pen_eq_16 ‹_›]
  | .index it b i => by
    simp only [deleteStep]
    split
    · rename_i hb
      cases it <;> cases i <;> first | trivial | weigh [SPath.pen_eq_one hb]
    · weigh [SPath.pen_eq_16 ‹_›]

/-- A compound assignment: source, then receiver.

Example: `people[i].age += x + 1;` captures the source first:
`uint se = x + 1; people[i].age += se;`. -/
theorem opStep_small {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C p) :
    ∀ r : Val C p, (opStep (k := k) (m := m) op hop hp l r).Small
  | .simple _ => by
    cases l with
    | field b _ _ =>
      simp only [opStep]
      split
      · trivial
      · weigh [SPath.pen_eq_16 ‹_›]
    | index it b _ =>
      simp only [opStep]
      split
      · cases it <;> trivial
      · weigh [SPath.pen_eq_16 ‹_›]
    | mfield b _ _ => cases b <;> simp only [opStep] <;> first | trivial | weigh
    | mindex _ b _ => cases b <;> simp only [opStep] <;> first | trivial | weigh
    | _ => trivial
  | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. => by
    simp only [opStep]; weigh

/-- `++`/`--`: the receiver first.

Example: `people[i].age++;` unfolds into
`Person storage sp = people[i]; sp.age++;`. -/
theorem incStep_small {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) :
    ∀ l : OpLoc C p, (incStep (k := k) (m := m) op hp l).Small
  | .field b _ _ => by
    simp only [incStep]
    split
    · trivial
    · weigh [SPath.pen_eq_16 ‹_›]
  | .index _ b _ => by
    simp only [incStep]
    split
    · trivial
    · weigh [SPath.pen_eq_16 ‹_›]
  | .mfield b _ _ => by cases b <;> simp only [incStep] <;> first | trivial | weigh
  | .mindex _ b _ => by cases b <;> simp only [incStep] <;> first | trivial | weigh
  | .local _ | .root _ _ => trivial

/-- `v = x++;`: always one update.

Example: `v = alice.age++;` leaves
`{ storage := save(…) ‖ v := alice.age++ }`. -/
theorem assignIncStep_small {p : PrimTy} (v : Var) (op : IncDec) (hp : p.isNumeric = true) :
    ∀ (l : OpLoc C p) (hs : l.recvSimple = true), (assignIncStep (k := k) (m := m) v op hp l hs).Small
  | .local _, _ | .root _ _, _ | .field _ _ _, _ | .index _ _ _, _ | .mfield (.var _) _ _, _
  | .mindex _ (.var _) _, _ => trivial
  | .mfield (.loc _) _ _, hs | .mindex _ (.loc _) _, hs => nomatch hs

/-- `push`: the receiver first, then the argument.

Example: `values.push(x + 1);` captures the argument:
`uint se = x + 1; values.push(se);`. -/
theorem pushStep_small {E : Ty} (b : SPath C (.array E)) (v : Option (Src C E))
    (hd : (v.isSome || E.defaultOkS) = true) : (pushStep (k := k) (m := m) b v hd).Small := by
  unfold pushStep
  split
  · rename_i hb
    rcases v with _ | (⟨e⟩ | ⟨_, _⟩)
    · dsimp only; split <;> trivial
    · cases e <;> first | trivial | weigh [SPath.pen_eq_one hb]
    · trivial
  · rename_i hb
    rcases v with _ | (_ | _) <;> weigh [SPath.pen_eq_16 hb]

/-- `pop`: the receiver first.

Example: `people[i].values.pop();` unfolds into
`Person storage sp = people[i]; sp.values.pop();`. -/
theorem popStep_small {E : Ty} (b : SPath C (.array E)) : (popStep (k := k) (m := m) b).Small := by
  unfold popStep
  split
  · split <;> trivial
  · weigh [SPath.pen_eq_16 ‹_›]

/-- `transfer`: the receiver first, then the amount.

Example: `people[i].wallet.transfer(x);` captures the receiver:
`uint se = people[i].wallet; se.transfer(x);`. -/
theorem transferStep_small : ∀ r a : Val C .uint, (transferStep (k := k) (m := m) r a).Small
  | .simple _, .simple _ => trivial
  | .simple _, .read _ | .simple _, .binop .. | .simple _, .unop .. | .simple _, .ternary ..
  | .simple _, .readMem _ | .simple _, .len .. | .simple _, .mlen .. => by
    simp only [transferStep]; weigh
  | .read _, _ | .binop .., _ | .unop .., _ | .ternary .., _ | .readMem _, _ | .len .., _
  | .mlen .., _ => by
    simp only [transferStep]; weigh

/-- A memory local bound.

Example: `m = n.items[i + 1];` captures the index first. -/
theorem rebindMemStep_small {R : RefTy} (x : Var) :
    ∀ r : MRhs C R, (rebindMemStep (k := k) (m := m) x r).Small
  | .alias (.var _) => trivial
  | .alias (.loc l) => by
    simp only [rebindMemStep]
    refine MHole.readStep_small (.rebind x) rfl (fun _ _ _ => ?_) (fun _ _ _ => ?_) l <;> trivial
  | .copy sp _ => by
    simp only [rebindMemStep]
    split
    · trivial
    · weigh [SPath.pen_eq_16 ‹_›]
  | .newArr _ _ => trivial

/-- A memory `delete`: a member or an element of a memory local is reset in
one update; any other receiver is bound first, a complex index captured.

Example: `delete m.inner.age;` unfolds into
`Inner memory mv = m.inner; delete mv.age;`. -/
theorem deleteMemStep_small {T : Ty} (p : MPath C T) (hd : T.defaultOkS = true) :
    (deleteMemStep (k := k) (m := m) p hd).Small := by
  cases p with
  | var _ => trivial
  | loc l =>
    cases l with
    | field b f hf =>
      cases b with
      | var _ => cases T <;> trivial
      | loc _ => simp only [deleteMemStep]; weigh
    | index a b i =>
      cases b with
      | var _ =>
        cases i with
        | simple _ => cases T <;> trivial
        | _ => simp only [deleteMemStep]; weigh
      | loc _ => simp only [deleteMemStep]; weigh

/-- A memory reference written: its source unfolded until it is bindable.

Example: `m.account = n.inner.account;` binds `n.inner` first. -/
theorem memRefStep_small {R : RefTy} (l : MLoc C (.ref R)) (hl : l.isTarget = true)
    {copy : (src : MPath C (.ref R)) → src.isBindable = true → Step k m (.assignMem l (.ref src))}
    (hc : ∀ src h, (copy src h).Small) : ∀ src, (memRefStep l hl copy src).Small
  | .var _ => hc _ _
  | .loc sl => by
    simp only [memRefStep]
    exact MHole.readStep_small (.write l) hl (fun _ _ _ => hc _ _) (fun _ _ _ => hc _ _) sl

/-- A memory write: receiver, then index, then source.

Example: `m.inner.age = 3;` unfolds into
`Inner memory mv = m.inner; mv.age = 3;`. -/
theorem assignMemStep_small {T : Ty} (l : MLoc C T) (r : MSrc C T) :
    (assignMemStep (k := k) (m := m) l r).Small := by
  -- `assignMemStep`'s match has no equation lemmas: it is reduced by `dsimp`
  -- once every discriminant is a constructor
  cases l with
  | field b f hf =>
    cases b with
    | var mv =>
      cases r with
      | val e =>
        refine VHole.step_small (VHole.mem (.field (.var mv) f hf)) rfl (fun _ => ?_) e
          (fun he _ => ?_)
        · trivial
        · weigh [Val.pen_eq_16 he]
      | ref src => exact memRefStep_small (.field (.var mv) f hf) rfl (fun _ _ => by trivial) src
    | loc _ => cases r <;> (delta assignMemStep; dsimp only; weigh)
  | index a b i =>
    cases b with
    | var mv =>
      cases i with
      | simple ie =>
        cases r with
        | val e =>
          refine VHole.step_small (VHole.mem (.index a (.var mv) (.simple ie))) rfl (fun _ => ?_) e
            (fun he _ => ?_)
          · trivial
          · weigh [Val.pen_eq_16 he]
        | ref src =>
          exact memRefStep_small (.index a (.var mv) (.simple ie)) rfl (fun _ _ => by trivial) src
      | _ => cases r <;> (delta assignMemStep; dsimp only; weigh)
    | loc _ => cases r <;> (delta assignMemStep; dsimp only; weigh)

/-- **Every rule makes the program smaller**: the premise `Stmt.step` fires
weighs less than its statement, and each goal of a branch at least `2` less.

Example: `people[i].age = 10;` (weight `23`) unfolds into three statements
of weights `3`, `6` and `5`; `if (c) { x = 1; } else { x = 2; }` (weight
`6`, `c` a `bool` local) splits into two goals of weight `2`. -/
theorem Stmt.step_smaller (k : Nat) (m : Modality) :
    ∀ s : Stmt C, (s.step k m).premise.Smaller s
  | .assign l r => assignStep_small l r
  | .rebind x r => rebindStep_small x r
  | .assignLocal x v => localStep_small x v
  | .declLocal _ _ none | .declMem _ _ none _ => trivial
  | .declStorage _ _ none | .declLocal _ _ (some _) | .declStorage _ _ (some _)
  | .declMem _ _ (some _) _ => by
    simp only [Stmt.step]; weigh
  | .opAssign op hop hp l r => opStep_small op hop hp l r
  | .incDec op hp l => incStep_small op hp l
  | .assignIncDec x op hp l hs => assignIncStep_small x op hp l hs
  | .push b v hd => pushStep_small b v hd
  | .pop b => popStep_small b
  | .transfer r a => transferStep_small r a
  | .rebindMem x r => rebindMemStep_small x r
  | .assignFromMem l p => assignFromMemStep_small l p
  | .assignMem l r => assignMemStep_small l r
  | .delete l => deleteStep_small l
  | .deleteMem p hd => deleteMemStep_small p hd
  | .assignNew l _ _ => by cases l <;> (simp only [Stmt.step]; weigh)
  | .ite (.simple _) _ _ | .require (.simple _) | .assert (.simple _) => by
    simp only [Stmt.step]; weigh
  | .ite (.read _) .. | .ite (.binop ..) .. | .ite (.unop ..) .. | .ite (.ternary ..) ..
  | .ite (.readMem _) .. | .require (.read _) | .require (.binop ..) | .require (.unop ..)
  | .require (.ternary ..) | .require (.readMem _) | .assert (.read _) | .assert (.binop ..)
  | .assert (.unop ..) | .assert (.ternary ..) | .assert (.readMem _) | .ite (.len ..) ..
  | .ite (.mlen ..) .. | .require (.len ..) | .require (.mlen ..) | .assert (.len ..)
  | .assert (.mlen ..) => by
    simp only [Stmt.step]; weigh
  | .revert => by cases m <;> trivial

/-- **Every rule makes the program smaller**, as a fact about the rules
rather than the dispatcher: any derivation of `s` is the one `Stmt.step`
fires (`Taclet.eq_step`).  `people[i].age = 10;` has only
`storageFieldWrite_unfold_leftFst`, whose three statements weigh `14`
against its `23`. -/
theorem Taclet.smaller {k : Nat} {m : Modality} {s : Stmt C} {p : Premise C}
    (d : Taclet C k m s p) : p.Smaller s := by
  rw [d.eq_step]
  exact Stmt.step_smaller k m s

/-! ## Certificates

A measure that every step decreases rules out infinite chains of steps. -/

/-- One step of the strategy, its fresh names numbered at any index. -/
def Fml.Step (φ ψ : Fml C) : Prop := ∃ k, φ.stepAt k = some ψ

/-- The obligation for a natural-number measure. -/
def StepDecreases (μ : Fml C → Nat) : Prop := ∀ {φ ψ : Fml C}, Fml.Step φ ψ → μ ψ < μ φ

/-- A decreasing measure rules out infinite chains of steps.

Example: `Fml.measure` of `dl!{ [ total = 1; ] total == 1 }` is `16`, so no
chain of steps from it is longer than `16`. -/
theorem step_wellFounded_of_decreases (μ : Fml C → Nat) (h : StepDecreases μ) :
    WellFounded (fun ψ φ : Fml C => Fml.Step φ ψ) :=
  Subrelation.wf (fun hs => h hs) (InvImage.wf μ Nat.lt_wfRel.wf)

/-- A checkable package: a measure, and that every step decreases it. -/
structure TerminationCertificate (C : Contract) where
  measure : Fml C → Nat
  decreases : StepDecreases measure

/-! ## The measure -/

/-- Every statement weighs at least `1`, so a rule that removes it lowers the
weight of the program.

Example: `revert();` weighs `1`, `x = 1;` weighs `2`. -/
theorem Stmt.weight_pos (s : Stmt C) : 0 < s.weight := by
  cases s with
  | declLocal _ _ i => cases i <;> simp only [Stmt.weight] <;> omega
  | declStorage _ _ i => cases i <;> simp only [Stmt.weight] <;> omega
  | declMem _ _ i _ => cases i <;> simp only [Stmt.weight] <;> omega
  | push _ v _ => cases v <;> simp only [Stmt.weight] <;> omega
  | _ => simp only [Stmt.weight] <;> omega

/-- The weight of two programs one after the other is the sum of their
weights.

Example: `total = 1; x = 1;` weighs `4 + 2 = 6`. -/
theorem Prog.weight_append (P Q : Prog C) :
    Prog.weight (P ++ Q) = Prog.weight P + Prog.weight Q := by
  induction P with
  | nil => simp [Prog.weight]
  | cons s P ih => simp [Prog.weight, ih, Nat.add_assoc]

/-- A modality costs `2 ^ weight` times what follows it; the hypothesis of an
implication and a negated formula cost nothing (no rule steps inside them).

Example: `dl!{ [ total = 1; ] total == 1 }` measures `2 ^ 4 * 1 = 16`. -/
def Fml.measure : Fml C → Nat
  | .modal _ P φ => 2 ^ Prog.weight P * (φ.measure + 1)
  | .upd _ _ φ | .imp _ φ => φ.measure
  | .and φ ψ => φ.measure + ψ.measure
  | .tt | .eq .. | .not _ => 0

/-- What a diamond branch owes besides its goals measures nothing.

Example: `¬(¬(se = true) ∧ ¬(se = false))` measures `0`. -/
theorem Premise.cover_measure (m : Modality) (c c' : Fml C) :
    (Premise.cover m c c').measure = 0 := by
  cases m <;> rfl

/-- A premise that weighs less than its statement lowers the measure of the
modality: an update, new statements, the two goals of a branch, or the
`true`/`false` of a revert, which measures `0`.

Example: `[ total = 1; ] total == 1` measures `16`, and the update
`storageRootWriteStore` leaves in its place measures `1`.  A branch on a
`bool` local `c`: `[ if (c) { x = 1; } else { x = 2; }; ] x == 1` measures
`2 ^ 6 = 64`, and its two goals `[ x = 1; ] …` and `[ x = 2; ] …` measure
`4 + 4 = 8`. -/
theorem Premise.measure_lt {m : Modality} {s : Stmt C} {p : Premise C} (h : p.Smaller s)
    (ω : Prog C) (φ : Fml C) : (p.fml m ω φ).measure < (Fml.modal m (s :: ω) φ).measure := by
  have hs := s.weight_pos
  have hM : 0 < φ.measure + 1 := Nat.succ_pos _
  cases p with
  | update U =>
    simp only [Premise.fml, Fml.measure, Prog.weight]
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) (by omega)) hM
  | unfold P =>
    simp only [Premise.Smaller] at h
    simp only [Premise.fml, Fml.measure, Prog.weight, Prog.weight_append]
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) (by omega)) hM
  | split c c' P Q =>
    simp only [Premise.Smaller] at h
    simp only [Premise.fml, Fml.measure, Prog.weight, Prog.weight_append,
      Premise.cover_measure, Nat.add_zero]
    -- both goals are below `X`, and the `if` is above `4 X`
    generalize Prog.weight ω = a
    generalize hX : 2 ^ (s.weight - 2 + a) = X
    have hP : 2 ^ (Prog.weight P + a) ≤ X := hX ▸ Nat.pow_le_pow_right (by decide) (by omega)
    have hQ : 2 ^ (Prog.weight Q + a) ≤ X := hX ▸ Nat.pow_le_pow_right (by decide) (by omega)
    have h4 : 4 * X = 2 ^ (s.weight + a) := by
      rw [← hX, show s.weight + a = s.weight - 2 + a + 2 by omega, Nat.pow_succ, Nat.pow_succ]
      omega
    have hXM : 0 < X * (φ.measure + 1) := Nat.mul_pos (hX ▸ Nat.pow_pos (by decide)) hM
    calc 2 ^ (Prog.weight P + a) * (φ.measure + 1) + 2 ^ (Prog.weight Q + a) * (φ.measure + 1)
        ≤ X * (φ.measure + 1) + X * (φ.measure + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hP) (Nat.mul_le_mul_right _ hQ)
      _ < 4 * X * (φ.measure + 1) := by rw [Nat.mul_assoc]; omega
      _ = 2 ^ (s.weight + a) * (φ.measure + 1) := by rw [h4]
  | done b =>
    have : 0 < 2 ^ (s.weight + Prog.weight ω) * (φ.measure + 1) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) hM
    cases b <;> simpa [Premise.fml, Fml.measure, Prog.weight] using this

/-- Every step decreases the measure, whatever index its fresh names get.

Example: `dl!{ [ total = 1; ] total == 1 }` (measure `16`) steps to
`{ storage := store(storage, total, 1) } [ ] select(storage, total) = 1`
(measure `1`). -/
theorem Fml.stepAt_decreases {k : Nat} :
    ∀ {φ ψ : Fml C}, φ.stepAt k = some ψ → ψ.measure < φ.measure
  | .upd _ _ φ, _, h | .imp _ φ, _, h => by
    simp only [Fml.stepAt, Option.map_eq_some_iff] at h
    obtain ⟨_, h, rfl⟩ := h
    simpa [Fml.measure] using Fml.stepAt_decreases h
  | .and φ₁ φ₂, _, h => by
    simp only [Fml.stepAt] at h
    split at h <;> simp only [Option.map_eq_some_iff] at h <;> obtain ⟨_, h, rfl⟩ := h
    · have := Fml.stepAt_decreases h; simp only [Fml.measure]; omega
    · have := Fml.stepAt_decreases h; simp only [Fml.measure]; omega
  | .modal _ [] φ, _, h => by
    simp only [Fml.stepAt, Option.some.injEq] at h
    subst h
    simp [Fml.measure, Prog.weight]
  | .modal m (s :: ω) φ, _, h => by
    simp only [Fml.stepAt, Option.some.injEq] at h
    subst h
    exact Premise.measure_lt (Stmt.step_smaller k m s) ω φ
  | .tt, _, h | .eq .., _, h | .not _, _, h => by simp [Fml.stepAt] at h

/-- `Fml.measure` is a termination certificate: every step lowers it.

Example: the steps for `total = x + 1;` take the measure
`2 ^ 22 → 2 ^ 10 → 2 ^ 9 → 2 ^ 4 → 1 → 0`: capture, drop the declaration,
the two updates, and the empty modality. -/
theorem Fml.step_decreases : StepDecreases (Fml.measure (C := C)) :=
  fun ⟨_, h⟩ => Fml.stepAt_decreases h

/-- The certificate. -/
def terminationCertificate : TerminationCertificate C := ⟨Fml.measure, Fml.step_decreases⟩

/-- **Termination.**  No formula has an infinite chain of steps, whatever
indices the fresh names get.

Example: the steps from
`dl!{ [ if (a == b) { x = 1; } else { x = 2; }; ] x == 1 }` stop, although
`ifElseSplit` copies the postcondition into both branches. -/
theorem Fml.step_wellFounded : WellFounded (fun ψ φ : Fml C => Fml.Step φ ψ) :=
  step_wellFounded_of_decreases _ terminationCertificate.decreases

/-! ## Normalization: the strategy ends first order -/

/-- A formula with a modality left has a positive measure.

Example: `{ x := 1 } [ ] x = 1` still has the empty modality and measures
`1`; a formula of measure `0`, such as `{ x := 1 } x = 1`, is first order. -/
theorem Fml.measure_pos : ∀ {φ : Fml C}, φ.active = true → 0 < φ.measure
  | .modal .., _ => Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.succ_pos _)
  | .upd _ _ φ, h | .imp _ φ, h => Fml.measure_pos (φ := φ) (by simpa [Fml.active] using h)
  | .and φ ψ, h => by
    simp only [Fml.active, Bool.or_eq_true] at h
    rcases h with h | h <;> have := Fml.measure_pos h <;> simp only [Fml.measure] <;> omega
  | .tt, h | .eq .., h | .not _, h => by simp [Fml.active] at h

/-- **Normalization.**  Given as much fuel as its measure, the strategy leaves
no modality in a formula: symbolic execution always runs to the end.

Example: `dl!{ [ total = 1; ] total == 1 }` measures `16`, so `symex 16`
leaves it first order. -/
theorem symex_normalizes : ∀ (n : Nat) (φ : Fml C), φ.measure ≤ n → (symex n φ).active = false
  | 0, φ, h => by
    simp only [symex]
    cases ha : φ.active
    · rfl
    · exact absurd (Fml.measure_pos ha) (by omega)
  | n + 1, φ, h => by
    simp only [symex]
    split
    · rename_i ψ hs
      have := Fml.stepAt_decreases hs
      exact symex_normalizes n ψ (by omega)
    · exact Fml.step_eq_none (by assumption)

/-- Fuel equal to the measure is enough.

Example: `symex` with fuel the measure of `dl!{ [ total = 1; ] total == 1 }`
runs it to the end. -/
theorem symex_measure (φ : Fml C) : (symex φ.measure φ).active = false :=
  symex_normalizes _ φ (Nat.le_refl _)

/-- **Symbolic execution terminates**: every formula has a fuel after which
no modality is left.

Example: for `dl!{ [ if (a == b) { x = 1; } else { x = 2; }; ] x == 1 }`
some `n` (its measure, `2 ^ 24`) runs both branches to the end. -/
theorem symex_terminates (φ : Fml C) : ∃ n, (symex n φ).active = false :=
  ⟨_, symex_measure φ⟩

/-! ## Try it -/

section Examples

local instance : InContract := ⟨StandardExample⟩

-- a write to a state variable weighs `4` (the target `1`, the simple source
-- `1 + 1`, the statement `1`), so it measures `2 ^ 4`
/-- info: 16 -/
#guard_msgs in
#eval (dl!{ [ total = 1; ] total == 1 }).measure

-- the strategy lowers it at every step, and ends first order
#guard (List.range 7).map (fun n => (symex n dl!{ [ total = x + 1; ] total == 1 }).measure) ==
  [2 ^ 22, 2 ^ 10, 2 ^ 9, 2 ^ 4, 1, 0, 0]

-- fuel equal to the measure is enough, by the theorem
example : (symex 16 dl!{ [ total = 1; ] total == 1 }).active = false :=
  symex_normalizes _ _ (by decide)

end Examples

end Solidity
