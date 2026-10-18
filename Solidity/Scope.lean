import Solidity.AST

/-!
# Scopes: contexts and positions

The vocabulary of the intrinsic syntax (`Syntax/Scoped.lean`, `docs/intrinsic.md`):
a context `Ctx` lists the types of the locals in scope, innermost first, and
a local is read by its position `Idx Γ t` (a de Bruijn index), which carries
its type.  Names are not in the index (Gate G0, condition 3): a binder
carries its `Var` as a label, and a printer keeps the names beside the
context, aligned with it.

Two ways one context sits in another:

* `Ext Γ Δ`: `Δ` is `Γ` with locals pushed on top.  It is what a scope end
  pops (a block, a branch, a call's frame), and what the interpreter drops
  (condition 5).  Its functions are written with `Ext.casesOn` and structural
  recursion, since the kernel evaluates them (condition 1).
* `Thin Γ Δ`: an order-preserving embedding, `Γ`'s locals among `Δ`'s.  It
  weakens a statement into a context with more locals (`Stmt.wk`).
  `Stmt.wk`/`Prog.wk` and `Idx.wk` use `match` and are also evaluated by
  the kernel, once per `ifElseUnfold`, call or invariant rule fired: the
  documented exceptions to condition 1 (`Calculus/Step.lean`).

`Binders ρ` and `CodeBinder κ` are the names a statement binds in a context
`ρ` of its own (a `try`'s returned values and `Panic` code), in the order it
binds them.
-/

namespace Solidity

/-- What a local holds: a value of a primitive type, a storage alias, a
memory reference, or (in a specification) the storage or ledger before the
call, solkey's `old`; or a logical variable of KeY's `int`, an unbounded
integer (`kint`: a formula's parameter read beside the ledger), which no
statement reads or binds. -/
inductive LTy where
  | val (p : PrimTy)
  | alias (R : RefTy)
  | mem (R : RefTy)
  | old
  | oldNet
  | kint
  deriving DecidableEq, Repr, Inhabited

/-- The types of the locals in scope, innermost first. -/
abbrev Ctx := List LTy

/-! ## Positions -/

/-- A local of type `t` in `Γ`, by its position: `here` is the innermost. -/
inductive Idx : Ctx → LTy → Type where
  | here {t : LTy} {Γ : Ctx} : Idx (t :: Γ) t
  | there {u t : LTy} {Γ : Ctx} (i : Idx Γ t) : Idx (u :: Γ) t
  deriving Repr

namespace Idx

/-- The position as a number: `0` for the innermost local. -/
def toNat {Γ : Ctx} {t : LTy} : Idx Γ t → Nat
  | .here => 0
  | .there i => i.toNat + 1

theorem toNat_lt {Γ : Ctx} {t : LTy} (i : Idx Γ t) : i.toNat < Γ.length := by
  induction i with
  | here => exact Nat.succ_pos _
  | there i ih => exact Nat.succ_lt_succ ih

/-- The context has `t` where the position points. -/
theorem getElem?_toNat {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Γ[i.toNat]? = some t := by
  induction i with
  | here => rfl
  | there i ih => exact ih

theorem toNat_inj {Γ : Ctx} {t : LTy} : (i j : Idx Γ t) → i.toNat = j.toNat → i = j
  | .here, .here, _ => rfl
  | .there i, .there j, h => congrArg Idx.there (toNat_inj i j (Nat.succ.inj h))
  | .here, .there _, h => nomatch h
  | .there _, .here, h => nomatch h

instance {Γ : Ctx} {t : LTy} : DecidableEq (Idx Γ t) := fun i j =>
  if h : i.toNat = j.toNat then isTrue (toNat_inj i j h)
  else isFalse fun e => h (congrArg toNat e)

/-- The name of the local, from the names `ns` kept beside the context. -/
def name {Γ : Ctx} {t : LTy} (ns : List Var) (i : Idx Γ t) : Var :=
  ns.getD i.toNat (.user "_")

end Idx

/-- The local at position `n` of `Γ`, if it has type `t`: what a resolver
looks a name up as. -/
def Ctx.idx? : (Γ : Ctx) → Nat → (t : LTy) → Option (Idx Γ t)
  | [], _, _ => none
  | u :: _, 0, t => if h : u = t then some (h ▸ .here) else none
  | _ :: Γ, n + 1, t => (Ctx.idx? Γ n t).map .there

theorem Ctx.idx?_toNat {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Γ.idx? i.toNat t = some i := by
  induction i with
  | here => simp only [Idx.toNat, Ctx.idx?, dite_true]
  | there i ih => simp only [Idx.toNat, Ctx.idx?, ih, Option.map_some]

/-! ## Suffixes: what a scope end pops -/

/-- `Δ` is `Γ` with locals pushed on top. -/
inductive Ext (Γ : Ctx) : Ctx → Type where
  | refl : Ext Γ Γ
  | push {t : LTy} {Δ : Ctx} (h : Ext Γ Δ) : Ext Γ (t :: Δ)
  deriving Repr

namespace Ext

def trans {Γ Δ : Ctx} (a : Ext Γ Δ) : {Ε : Ctx} → Ext Δ Ε → Ext Γ Ε
  | _, b => Ext.casesOn (motive := fun Ε _ => Ext Γ Ε) b a (fun h => .push (Ext.trans a h))
  termination_by structural _ b => b

/-- The locals `ρ` pushed on `Γ`. -/
def append (Γ : Ctx) : (ρ : Ctx) → Ext Γ (ρ ++ Γ)
  | [] => .refl
  | _ :: ρ => .push (append Γ ρ)

/-- How many locals are pushed. -/
def depth {Γ : Ctx} : {Δ : Ctx} → Ext Γ Δ → Nat
  | _, h => Ext.casesOn (motive := fun _ _ => Nat) h 0 (fun h => Ext.depth h + 1)
  termination_by structural _ h => h

end Ext

/-- A local of `Γ`, read in `Δ`: its position moves past the pushed ones. -/
def Idx.ext {Γ : Ctx} {t : LTy} (i : Idx Γ t) : {Δ : Ctx} → Ext Γ Δ → Idx Δ t
  | _, h => Ext.casesOn (motive := fun Δ _ => Idx Δ t) h i (fun h => .there (Idx.ext i h))
  termination_by structural _ h => h

namespace Ext

theorem trans_push {Γ Δ Ε : Ctx} {t : LTy} (a : Ext Γ Δ) (b : Ext Δ Ε) :
    a.trans (.push (t := t) b) = .push (a.trans b) := rfl

theorem refl_trans {Γ Δ : Ctx} (b : Ext Γ Δ) : Ext.refl.trans b = b := by
  induction b with
  | refl => rfl
  | push b ih => rw [trans_push, ih]

theorem trans_assoc {Γ Δ Ε Ζ : Ctx} (a : Ext Γ Δ) (b : Ext Δ Ε) (c : Ext Ε Ζ) :
    (a.trans b).trans c = a.trans (b.trans c) := by
  induction c with
  | refl => rfl
  | push c ih => rw [trans_push, trans_push, trans_push, ih]

theorem length_eq {Γ Δ : Ctx} (h : Ext Γ Δ) : Δ.length = Γ.length + h.depth := by
  induction h with
  | refl => rfl
  | push h ih =>
    show _ + 1 = _ + (h.depth + 1)
    rw [ih, Nat.add_assoc]

theorem toNat_idx {Γ Δ : Ctx} {t : LTy} (h : Ext Γ Δ) (i : Idx Γ t) :
    (i.ext h).toNat = i.toNat + h.depth := by
  induction h with
  | refl => rfl
  | push h ih =>
    show (i.ext h).toNat + 1 = i.toNat + (h.depth + 1)
    rw [ih, Nat.add_assoc]

/-- Two suffix witnesses of the same contexts are equal: an `Ext` is proof-like
data, and a scope end has only one way to pop. -/
theorem eq_of_depth {Γ Δ : Ctx} : (a b : Ext Γ Δ) → a = b := by
  intro a b
  induction a with
  | refl =>
    cases b with
    | refl => rfl
    | push b =>
      have := b.length_eq
      simp only [List.length_cons] at this
      omega
  | push a ih =>
    cases b with
    | refl =>
      have := a.length_eq
      simp only [List.length_cons] at this
      omega
    | push b => rw [ih b]

instance {Γ Δ : Ctx} : Subsingleton (Ext Γ Δ) := ⟨eq_of_depth⟩

end Ext

/-! ## Thinnings: weakening -/

/-- `Γ`'s locals, in order, among `Δ`'s: `keep` one of both, `drop` one of
`Δ`'s only. -/
inductive Thin : Ctx → Ctx → Type where
  | refl {Γ : Ctx} : Thin Γ Γ
  | keep {t : LTy} {Γ Δ : Ctx} (h : Thin Γ Δ) : Thin (t :: Γ) (t :: Δ)
  | drop {t : LTy} {Γ Δ : Ctx} (h : Thin Γ Δ) : Thin Γ (t :: Δ)
  deriving Repr

namespace Thin

def trans : {Γ Δ Ε : Ctx} → Thin Γ Δ → Thin Δ Ε → Thin Γ Ε
  | _, _, _, t, .refl => t
  | _, _, _, t, .drop h => .drop (t.trans h)
  | _, _, _, .refl, .keep h => .keep h
  | _, _, _, .keep t, .keep h => .keep (t.trans h)
  | _, _, _, .drop t, .keep h => .drop (t.trans h)

/-- The locals `ρ` kept on top of a thinning: a scope of its own (a `try`'s
returned values, a call's exported returns) weakened with its context. -/
def keepAll {Γ Δ : Ctx} : (ρ : Ctx) → Thin Γ Δ → Thin (ρ ++ Γ) (ρ ++ Δ)
  | [], h => h
  | _ :: ρ, h => .keep (keepAll ρ h)

/-- A suffix is a thinning: every pushed local dropped. -/
def ofExt {Γ : Ctx} : {Δ : Ctx} → Ext Γ Δ → Thin Γ Δ
  | _, .refl => .refl
  | _, .push h => .drop (ofExt h)

theorem length_le : {Γ Δ : Ctx} → Thin Γ Δ → Γ.length ≤ Δ.length
  | _, _, .refl => Nat.le_refl _
  | _, _, .keep h => Nat.succ_le_succ h.length_le
  | _, _, .drop h => Nat.le_succ_of_le h.length_le

end Thin

/-- A local of `Γ`, read in a context `Δ` that `Γ` thins into. -/
def Idx.wk : {Γ Δ : Ctx} → {t : LTy} → Thin Γ Δ → Idx Γ t → Idx Δ t
  | _, _, _, .refl, i => i
  | _, _, _, .keep _, .here => .here
  | _, _, _, .keep h, .there i => .there (i.wk h)
  | _, _, _, .drop h, i => .there (i.wk h)

theorem Idx.wk_refl {Γ : Ctx} {t : LTy} (i : Idx Γ t) : i.wk .refl = i := by
  cases i <;> rfl

theorem Idx.wk_trans {Γ Δ Ε : Ctx} {t : LTy} (a : Thin Γ Δ) (b : Thin Δ Ε) (i : Idx Γ t) :
    i.wk (a.trans b) = (i.wk a).wk b := by
  induction b generalizing Γ with
  | refl => cases a <;> cases i <;> rfl
  | drop b ih => rw [Thin.trans]; exact congrArg Idx.there (ih a i)
  | keep b ih =>
    cases a with
    | refl => cases i <;> rfl
    | keep a =>
      cases i with
      | here => rfl
      | there i => exact congrArg Idx.there (ih a i)
    | drop a => exact congrArg Idx.there (ih a i)

theorem Idx.wk_ofExt {Γ Δ : Ctx} {t : LTy} (h : Ext Γ Δ) (i : Idx Γ t) :
    i.wk (Thin.ofExt h) = i.ext h := by
  induction h with
  | refl => cases i <;> rfl
  | push h ih => exact congrArg Idx.there ih

/-! ## Binders -/

/-- The primitive locals a statement binds in a scope of its own, in the
order it binds them: the last bound is innermost.  `[uint a, bool b]` is
`(nil.snoc .uint a).snoc .bool b`, of context `[.val .bool, .val .uint]`. -/
inductive Binders : Ctx → Type where
  | nil : Binders []
  | snoc {ρ : Ctx} (bs : Binders ρ) (p : PrimTy) (x : Var) : Binders (.val p :: ρ)
  deriving Repr

/-- The binders in the order they are bound, with their types. -/
def Binders.toList {ρ : Ctx} : Binders ρ → List (PrimTy × Var)
  | .nil => []
  | .snoc bs p x => bs.toList ++ [(p, x)]

/-- Their names, innermost first, as a printer keeps them beside `ρ`. -/
def Binders.names {ρ : Ctx} : Binders ρ → List Var
  | .nil => []
  | .snoc bs _ x => x :: bs.names

/-- The `Panic` clause's code, a `uint`, if the clause names it. -/
inductive CodeBinder : Ctx → Type where
  | none : CodeBinder []
  | some (x : Var) : CodeBinder [.val .uint]
  deriving Repr

def CodeBinder.names {κ : Ctx} : CodeBinder κ → List Var
  | .none => []
  | .some x => [x]

end Solidity
