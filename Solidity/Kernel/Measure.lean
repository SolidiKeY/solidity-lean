import Solidity.Kernel.Step

/-!
# Every rule makes the program smaller

Phase 5 of `docs/kernel-port.md`, after mini-solkey's `Stmt.weight` and
`Premise.Smaller` (`Ch06_Taclets`, `Ch12_Termination`).  Each statement has a
size, and every rule's premise is `Smaller` than the statement it replaces:

* an unfolding rule replaces it by at most four statements, each of strictly
  smaller size;
* a split continues with one branch per goal, each of smaller total size;
* an update or a closed goal removes it.

That is what the measure of a goal, `Σ 5 ^ size` over its statements, needs
to fall at every step (four parts each at most `5 ^ (n - 1)` weigh less than
one part of `5 ^ n`), which phase 5 turns into well-foundedness of the step
relation on formulas.  The sizes are chosen so that the obligations are
linear: a storage write costs two more than its parts, a read one, a unary
operator two, and an `if` one more than its larger branch.
-/

namespace Solidity
namespace Kernel

open Semantics

variable {C : Contract}

/-! ## Sizes -/

def Simple.size {Γ : Ctx} {p : PrimTy} (_ : Simple C Γ p) : Nat := 1

/-- A short-circuiting operator with a right operand that is not simple costs
four more: its rule branches, and each branch re-applies the operator to a
simple operand. -/
def scCost {Γ : Ctx} {p : PrimTy} (op : BinOp) (b : Val C Γ p) : Nat :=
  if op.shortCircuits && !b.isSimple then 4 else 0

mutual

def SPath.size {Γ : Ctx} : {T : Ty} → SPath C Γ T → Nat
  | _, .alias .. => 1
  | _, .loc l => l.size

def Loc.size {Γ : Ctx} : {T : Ty} → Loc C Γ T → Nat
  | _, .root .. => 1
  | _, .field b _ _ => b.size + 1
  | _, .index _ b i => b.size + i.size + 1

def Val.size {Γ : Ctx} : {p : PrimTy} → Val C Γ p → Nat
  | _, .simple _ => 1
  | _, .read l => l.size + 1
  | _, .binop op _ _ a b => a.size + b.size + 1 + scCost op b
  | _, .unop _ _ _ a => a.size + 2

end

def Src.size {Γ : Ctx} {T : Ty} : Src C Γ T → Nat
  | .val v => v.size
  | .copy p _ => p.size

/-- A compound assignment's target: a local or a state variable one, a
member or an entry one more than its receiver (and index). -/
def OpLoc.size {Γ : Ctx} {p : PrimTy} : OpLoc C Γ p → Nat
  | .local .. | .root .. => 1
  | .field b _ _ => b.size + 1
  | .index _ b _ => b.size + 2

mutual

def Stmt.size {Γ Γ' : Ctx} : Stmt C Γ Γ' → Nat
  | .assign l r => l.size + r.size + 2
  | .opAssign _ _ _ l r => l.size + r.size + 2
  | .incDec _ _ l | .assignIncDec _ _ _ _ l _ => l.size + 1
  | .rebind _ _ p => p.size + 1
  | .assignLocal _ _ v => v.size + 1
  | .declLocal _ _ _ init =>
    match init with
    | none => 1
    | some e => e.size + 2
  | .declStorage _ _ _ _ p => p.size + 1
  | .delete l => l.size + 1
  | .ite _ thn els => max thn.size els.size + 1
  | .require _ | .assert _ => 2
  | .revert => 1

/-- The total size of a block. -/
def Prog.size {Γ Γ' : Ctx} : Prog C Γ Γ' → Nat
  | .nil => 0
  | .cons s P => s.size + P.size

end

/-- The sizes of a block's statements. -/
def Prog.sizes {Γ Γ' : Ctx} : Prog C Γ Γ' → List Nat
  | .nil => []
  | .cons s P => s.size :: P.sizes

/-- What a rule's premise owes the statement it replaces. -/
def Premise.Smaller {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Premise C Γ Γ' → Prop
  | .update _ => True
  | .unfold _ P _ => P.sizes.length ≤ 4 ∧ ∀ n ∈ P.sizes, n < s.size
  | .split _ P Q => P.size < s.size ∧ Q.size < s.size
  | .done _ => True

/-! ## Facts the obligations use -/

@[simp] theorem scCost_simple {Γ : Ctx} {p : PrimTy} (op : BinOp) (s : Simple C Γ p) :
    scCost op (.simple s) = 0 := by simp [scCost, Val.isSimple]

theorem scCost_and {Γ : Ctx} {p : PrimTy} {b : Val C Γ p} (hb : b.isSimple = false) :
    scCost .and b = 4 := by simp [scCost, BinOp.shortCircuits, hb]

theorem scCost_or {Γ : Ctx} {p : PrimTy} {b : Val C Γ p} (hb : b.isSimple = false) :
    scCost .or b = 4 := by simp [scCost, BinOp.shortCircuits, hb]

mutual

/-- Weakening keeps a path's size. -/
@[simp] theorem SPath.size_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') :
    {T : Ty} → (p : SPath C Γ T) → (p.weaken h).size = p.size
  | _, .alias .. => rfl
  | _, .loc l => l.size_weaken h

@[simp] theorem Loc.size_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') :
    {T : Ty} → (l : Loc C Γ T) → (l.weaken h).size = l.size
  | _, .root .. => rfl
  | _, .field b _ _ => by simp only [Loc.weaken, Loc.size, b.size_weaken h]
  | _, .index _ b i => by simp only [Loc.weaken, Loc.size, b.size_weaken h, i.size_weaken h]

@[simp] theorem Val.size_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') :
    {p : PrimTy} → (v : Val C Γ p) → (v.weaken h).size = v.size
  | _, .simple _ => rfl
  | _, .read l => by simp only [Val.weaken, Val.size, l.size_weaken h]
  | _, .binop op _ _ a b => by
    simp only [Val.weaken, Val.size, a.size_weaken h, b.size_weaken h]
    congr 1
    cases b <;> rfl
  | _, .unop _ _ _ a => by simp only [Val.weaken, Val.size, a.size_weaken h]

end

@[simp] theorem scCost_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') {p : PrimTy} (op : BinOp)
    (b : Val C Γ p) : scCost op (b.weaken h) = scCost op b := by
  cases b <;> rfl

@[simp] theorem Src.size_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') {T : Ty} (r : Src C Γ T) :
    (r.weaken h).size = r.size := by
  cases r <;> simp [Src.weaken, Src.size]

theorem Loc.one_le_size {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : 1 ≤ l.size := by
  cases l <;> simp [Loc.size]

theorem SPath.one_le_size {Γ : Ctx} {T : Ty} (p : SPath C Γ T) : 1 ≤ p.size := by
  cases p with
  | alias => simp [SPath.size]
  | loc l => exact l.one_le_size

/-- A path that is not simple is a member or an entry: size at least two. -/
theorem SPath.two_le_size {Γ : Ctx} {T : Ty} {p : SPath C Γ T} (h : p.isSimple = false) :
    2 ≤ p.size := by
  match p, h with
  | .loc (.field b _ _), _ => simp only [SPath.size, Loc.size]; have := b.one_le_size; omega
  | .loc (.index _ b i), _ => simp only [SPath.size, Loc.size]; have := b.one_le_size; omega

/-- Every value has size at least one. -/
theorem Val.one_le_size {Γ : Ctx} {p : PrimTy} (v : Val C Γ p) : 1 ≤ v.size := by
  cases v <;> simp [Val.size] <;> omega

/-- A value that is not simple has size at least two. -/
theorem Val.two_le_size {Γ : Ctx} {p : PrimTy} {v : Val C Γ p} (h : v.isSimple = false) :
    2 ≤ v.size := by
  match v, h with
  | .read l, _ => simp only [Val.size]; have := l.one_le_size; omega
  | .binop _ _ _ a b, _ => simp only [Val.size]; have := a.one_le_size; have := b.one_le_size; omega
  | .unop _ _ _ a, _ => simp only [Val.size]; omega

/-- One less than a size.  The obligations rewrite `v.size` to `v.sz + 1`,
which shows `omega` the lower bound on an atom it cannot unfold. -/
def Val.sz {Γ : Ctx} {p : PrimTy} (v : Val C Γ p) : Nat := v.size - 1
def SPath.sz {Γ : Ctx} {T : Ty} (v : SPath C Γ T) : Nat := v.size - 1
def Loc.sz {Γ : Ctx} {T : Ty} (v : Loc C Γ T) : Nat := v.size - 1

theorem Val.size_sz {Γ : Ctx} {p : PrimTy} (v : Val C Γ p) : v.size = v.sz + 1 := by
  have := v.one_le_size; simp only [Val.sz]; omega
theorem SPath.size_sz {Γ : Ctx} {T : Ty} (v : SPath C Γ T) : v.size = v.sz + 1 := by
  have := v.one_le_size; simp only [SPath.sz]; omega
theorem Loc.size_sz {Γ : Ctx} {T : Ty} (v : Loc C Γ T) : v.size = v.sz + 1 := by
  have := v.one_le_size; simp only [Loc.sz]; omega

/-! ## Holes -/

/-- What a hole's statement weighs beyond the path in it. -/
def Hole.extra {Γ Γ' : Ctx} {T : Ty} : Hole C Γ Γ' T → Nat
  | .local .. => 2
  | .rebind .. | .decl .. => 1
  | .copy l _ => l.size + 2

theorem Hole.fill_size {Γ Γ' : Ctx} {T : Ty} (k : Hole C Γ Γ' T) (p : SPath C Γ T) :
    (k.fill p).size = p.size + k.extra := by
  cases k with
  | «local» => cases p with
    | loc l => simp [Hole.fill, Stmt.size, Val.size, SPath.size, Hole.extra]
  | rebind | decl => simp [Hole.fill, Stmt.size, Hole.extra]
  | copy l h => simp [Hole.fill, Stmt.size, Src.size, Hole.extra]; omega

@[simp] theorem Hole.extend_extra {Γ Γ' : Ctx} {T : Ty} (y : Name) (b : BTy)
    (hy : isFresh C Γ' y = true) (k : Hole C Γ Γ' T) : (k.extend y b hy).extra = k.extra := by
  cases k <;> simp [Hole.extend, Hole.extra]

/-- One less than a hole's extra weight (it is at least one). -/
def Hole.ex {Γ Γ' : Ctx} {T : Ty} (k : Hole C Γ Γ' T) : Nat := k.extra - 1

theorem Hole.extra_ex {Γ Γ' : Ctx} {T : Ty} (k : Hole C Γ Γ' T) : k.extra = k.ex + 1 := by
  cases k <;> simp [Hole.ex, Hole.extra]

/-! ## The obligations -/

@[simp] theorem OpLoc.size_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') {p : PrimTy} (l : OpLoc C Γ p) :
    (l.weaken h).size = l.size := by
  cases l <;> simp only [OpLoc.weaken, OpLoc.size, SPath.size_weaken]

@[simp] theorem OpLoc.size_local {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) :
    (OpLoc.local (C := C) x h).size = 1 := rfl
@[simp] theorem OpLoc.size_root {Γ : Ctx} {p : PrimTy} (r : Name) (hΓ : lookupBy r Γ = none)
    (h : C.rootType r = some (.prim p)) : (OpLoc.root r hΓ h).size = 1 := rfl
@[simp] theorem OpLoc.size_field {Γ : Ctx} {s : Name} {p : PrimTy} (b : SPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.prim p)) : (OpLoc.field b f h).size = b.size + 1 := rfl
@[simp] theorem OpLoc.size_index {Γ : Ctx} {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p))
    (b : SPath C Γ (.ref R)) (i : Simple C Γ k) : (OpLoc.index it b i).size = b.size + 2 := rfl

theorem OpLoc.one_le_size {Γ : Ctx} {p : PrimTy} (l : OpLoc C Γ p) : 1 ≤ l.size := by
  cases l <;> simp only [OpLoc.size] <;> omega

set_option linter.unusedSimpArgs false in
/-- **Every rule makes the program smaller.**  `people[i].age = 10;` (size 7)
unfolds into `uint se = 10; Person storage sp = people[i]; sp.age = se;`, of
sizes 3, 4 and 5; `if (c) { … } else { … }` splits into its branches, each
smaller than the `if`. -/
theorem Taclet.smaller {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) : pr.Smaller s := by
  cases d
  all_goals (try have := SPath.two_le_size (by assumption))
  all_goals (try have := Val.two_le_size (by assumption))
  all_goals (try have := OpLoc.one_le_size (by assumption))
  all_goals simp only [Premise.Smaller, Prog.sizes, Prog.size, Stmt.size, Src.size, Val.size,
    SPath.size, Loc.size, Simple.size, Hole.fill_size, Hole.extend_extra, SPath.new, Simple.new,
    SPath.size_weaken, Loc.size_weaken, Val.size_weaken, Src.size_weaken, OpLoc.size_weaken,
    OpLoc.size_local, OpLoc.size_root, OpLoc.size_field, OpLoc.size_index, List.length,
    List.mem_cons, List.not_mem_nil, forall_eq_or_imp, and_true, true_and, false_implies,
    implies_true, Loc.weaken, SPath.weaken, List.mem_nil_iff, forall_const, scCost_simple,
    scCost_weaken,
    Simple.weaken] at *
  all_goals (try rw [scCost_and (by assumption)] at *)
  all_goals (try rw [scCost_or (by assumption)] at *)
  all_goals (try simp only [Val.size_sz, SPath.size_sz, Loc.size_sz, Hole.extra_ex] at *)
  all_goals (try simp only [Nat.max_def] at *)
  all_goals (repeat' split) <;> omega

end Kernel
end Solidity
