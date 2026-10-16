import Solidity.Calculus.Lower

/-!
# Shifting a rule's schema variables under its fresh locals

A rule that declares fresh locals (`T se = nse; v = se ⊕ e;`) reads the
parts of its `\find` under them: every local one further down per fresh
local (`.local i ↦ .local i.there`).  This is `wk up` without the thinning:
`Idx.wk` matches on `Thin` and `Idx`, both indexed by contexts, and the
kernel would run it on every capture (Gate G0, condition 1).  The functions
here match only on the expression families, whose context is a parameter;
`*.up_eq` says each is `wk up`.
-/

namespace Solidity

variable {C : Contract}

/-- A part read in `Γ`, read with one local more on top. -/
abbrev up {Γ : Ctx} {t : LTy} : Thin Γ (t :: Γ) := .drop .refl

/-! ## Shifting by one

A rule's schema variables, read under the fresh local it declares: every
local one further down (`.local i ↦ .local i.there`).  This is `wk up`
without the thinning: `Idx.wk` matches on `Thin` and `Idx`, both indexed by
contexts, and the kernel would run it on every capture (Gate G0,
condition 1).  These match only on the expression families, whose context
is a parameter; `*.up_eq` says each is `wk up`. -/

section Shift

theorem Idx.up_eq {Γ : Ctx} {t u : LTy} (i : Idx Γ t) : i.wk (up (t := u)) = i.there :=
  congrArg Idx.there (Idx.wk_refl i)

def Simple.up {Γ : Ctx} {t : LTy} {p : PrimTy} : Simple C Γ p → Simple C (t :: Γ) p
  | .lit n hr => .lit n hr
  | .bool b => .bool b
  | .local i => .local i.there
  | .env k hp => .env k hp

theorem Simple.up_eq {Γ : Ctx} {t : LTy} {p : PrimTy} (s : Simple C Γ p) :
    s.up (t := t) = s.wk Solidity.up := by
  cases s with
  | «local» i => exact congrArg Simple.local (Idx.up_eq i).symm
  | _ => rfl

mutual

def SPath.up {Γ : Ctx} {t : LTy} {T : Ty} : SPath C Γ T → SPath C (t :: Γ) T
  | .alias i => .alias i.there
  | .loc l => .loc l.up

def Loc.up {Γ : Ctx} {t : LTy} {T : Ty} : Loc C Γ T → Loc C (t :: Γ) T
  | .root r hr => .root r hr
  | .field b f hf => .field b.up f hf
  | .index it b i => .index it b.up i.up

def MPath.up {Γ : Ctx} {t : LTy} {T : Ty} : MPath C Γ T → MPath C (t :: Γ) T
  | .var i hm => .var i.there hm
  | .loc l => .loc l.up

def MLoc.up {Γ : Ctx} {t : LTy} {T : Ty} : MLoc C Γ T → MLoc C (t :: Γ) T
  | .field b f hf => .field b.up f hf
  | .index a b i => .index a b.up i.up

def Val.up {Γ : Ctx} {t : LTy} {p : PrimTy} : Val C Γ p → Val C (t :: Γ) p
  | .simple s => .simple s.up
  | .read l => .read l.up
  | .binop op ha hq a b => .binop op ha hq a.up b.up
  | .unop op ha hq a => .unop op ha hq a.up
  | .ternary c a b => .ternary c.up a.up b.up
  | .readMem l => .readMem l.up
  | .len b hp => .len b.up hp
  | .mlen b hp => .mlen b.up hp
  | .modular op a b k => .modular op a.up b.up k.up

end

def ARhs.up {Γ : Ctx} {t : LTy} {R : RefTy} : ARhs C Γ R → ARhs C (t :: Γ) R
  | .path p => .path p.up
  | .push b hd => .push b.up hd

mutual

theorem SPath.up_eq {Γ : Ctx} {t : LTy} {T : Ty} :
    (b : SPath C Γ T) → b.up (t := t) = b.wk Solidity.up
  | .alias i => congrArg SPath.alias (Idx.up_eq i).symm
  | .loc l => congrArg SPath.loc (Loc.up_eq l)

theorem Loc.up_eq {Γ : Ctx} {t : LTy} {T : Ty} :
    (l : Loc C Γ T) → l.up (t := t) = l.wk Solidity.up
  | .root _ _ => rfl
  | .field b f hf => congrArg (Loc.field · f hf) (SPath.up_eq b)
  | .index it b i => by
    show Loc.index it b.up i.up = Loc.index it (b.wk Solidity.up) (i.wk Solidity.up)
    rw [SPath.up_eq b, Val.up_eq i]

theorem MPath.up_eq {Γ : Ctx} {t : LTy} {T : Ty} :
    (b : MPath C Γ T) → b.up (t := t) = b.wk Solidity.up
  | .var i hm => congrArg (MPath.var · hm) (Idx.up_eq i).symm
  | .loc l => congrArg MPath.loc (MLoc.up_eq l)

theorem MLoc.up_eq {Γ : Ctx} {t : LTy} {T : Ty} :
    (l : MLoc C Γ T) → l.up (t := t) = l.wk Solidity.up
  | .field b f hf => congrArg (MLoc.field · f hf) (MPath.up_eq b)
  | .index a b i => by
    show MLoc.index a b.up i.up = MLoc.index a (b.wk Solidity.up) (i.wk Solidity.up)
    rw [MPath.up_eq b, Val.up_eq i]

theorem Val.up_eq {Γ : Ctx} {t : LTy} {p : PrimTy} :
    (v : Val C Γ p) → v.up (t := t) = v.wk Solidity.up
  | .simple s => congrArg Val.simple (Simple.up_eq s)
  | .read l => congrArg Val.read (Loc.up_eq l)
  | .binop op ha hq a b => by
    show Val.binop op ha hq a.up b.up = Val.binop op ha hq (a.wk Solidity.up) (b.wk Solidity.up)
    rw [Val.up_eq a, Val.up_eq b]
  | .unop op ha hq a => congrArg (Val.unop op ha hq) (Val.up_eq a)
  | .ternary c a b => by
    show Val.ternary c.up a.up b.up = Val.ternary (c.wk Solidity.up) (a.wk Solidity.up) (b.wk Solidity.up)
    rw [Val.up_eq c, Val.up_eq a, Val.up_eq b]
  | .readMem l => congrArg Val.readMem (MLoc.up_eq l)
  | .len b hp => congrArg (Val.len · hp) (SPath.up_eq b)
  | .mlen b hp => congrArg (Val.mlen · hp) (MPath.up_eq b)
  | .modular op a b k => by
    show Val.modular op a.up b.up k.up =
      Val.modular op (a.wk Solidity.up) (b.wk Solidity.up) (k.wk Solidity.up)
    rw [Val.up_eq a, Val.up_eq b, Val.up_eq k]

end

theorem ARhs.up_eq {Γ : Ctx} {t : LTy} {R : RefTy} (r : ARhs C Γ R) :
    r.up (t := t) = r.wk Solidity.up := by
  cases r with
  | path p => exact congrArg ARhs.path (SPath.up_eq p)
  | push b hd => exact congrArg (ARhs.push · hd) (SPath.up_eq b)

end Shift

/-! ## The other parts a statement carries -/

section ShiftMore

def Src.up {Γ : Ctx} {t : LTy} {T : Ty} : Src C Γ T → Src C (t :: Γ) T
  | .val v => .val v.up
  | .copy p hm => .copy p.up hm
  | .fixedCopy p shape hm => .fixedCopy p.up shape hm
  | .copyMem p => .copyMem p.up

def MSrc.up {Γ : Ctx} {t : LTy} {T : Ty} : MSrc C Γ T → MSrc C (t :: Γ) T
  | .val v => .val v.up
  | .ref p => .ref p.up

def MRhs.up {Γ : Ctx} {t : LTy} {R : RefTy} : MRhs C Γ R → MRhs C (t :: Γ) R
  | .alias p => .alias p.up
  | .copy p hm => .copy p.up hm
  | .newArr n h => .newArr n.up h

def NewLhs.up {Γ : Ctx} {t : LTy} {R : RefTy} : NewLhs C Γ R → NewLhs C (t :: Γ) R
  | .store l => .store l.up
  | .mem l => .mem l.up

def OpLoc.up {Γ : Ctx} {t : LTy} {p : PrimTy} : OpLoc C Γ p → OpLoc C (t :: Γ) p
  | .local i => .local i.there
  | .root r h => .root r h
  | .field b f h => .field b.up f h
  | .index it b i => .index it b.up i.up
  | .mfield b f h => .mfield b.up f h
  | .mindex a b i => .mindex a b.up i.up

theorem Src.up_eq {Γ : Ctx} {t : LTy} {T : Ty} (r : Src C Γ T) : r.up (t := t) = r.wk Solidity.up := by
  cases r with
  | val v => exact congrArg Src.val (Val.up_eq v)
  | copy p hm => exact congrArg (Src.copy · hm) (SPath.up_eq p)
  | fixedCopy p shape hm => exact congrArg (Src.fixedCopy · shape hm) (SPath.up_eq p)
  | copyMem p => exact congrArg Src.copyMem (MPath.up_eq p)

theorem MSrc.up_eq {Γ : Ctx} {t : LTy} {T : Ty} (r : MSrc C Γ T) :
    r.up (t := t) = r.wk Solidity.up := by
  cases r with
  | val v => exact congrArg MSrc.val (Val.up_eq v)
  | ref p => exact congrArg MSrc.ref (MPath.up_eq p)

theorem MRhs.up_eq {Γ : Ctx} {t : LTy} {R : RefTy} (r : MRhs C Γ R) :
    r.up (t := t) = r.wk Solidity.up := by
  cases r with
  | alias p => exact congrArg MRhs.alias (MPath.up_eq p)
  | copy p hm => exact congrArg (MRhs.copy · hm) (SPath.up_eq p)
  | newArr n h => exact congrArg (MRhs.newArr · h) (Simple.up_eq n)

theorem NewLhs.up_eq {Γ : Ctx} {t : LTy} {R : RefTy} (l : NewLhs C Γ R) :
    l.up (t := t) = l.wk Solidity.up := by
  cases l with
  | store l => exact congrArg NewLhs.store (Loc.up_eq l)
  | mem l => exact congrArg NewLhs.mem (MLoc.up_eq l)

theorem OpLoc.up_eq {Γ : Ctx} {t : LTy} {p : PrimTy} (l : OpLoc C Γ p) :
    l.up (t := t) = l.wk Solidity.up := by
  cases l with
  | «local» i => exact congrArg OpLoc.local (Idx.up_eq i).symm
  | root => rfl
  | field b f h => exact congrArg (OpLoc.field · f h) (SPath.up_eq b)
  | index it b i =>
    show OpLoc.index it b.up i.up = OpLoc.index it (b.wk Solidity.up) (i.wk Solidity.up)
    rw [SPath.up_eq b, Simple.up_eq i]
  | mfield b f h => exact congrArg (OpLoc.mfield · f h) (MPath.up_eq b)
  | mindex a b i =>
    show OpLoc.mindex a b.up i.up = OpLoc.mindex a (b.wk Solidity.up) (i.wk Solidity.up)
    rw [MPath.up_eq b, Simple.up_eq i]

theorem SPath.isSimple_up {Γ : Ctx} {t : LTy} {T : Ty} (b : SPath C Γ T) :
    (b.up (t := t)).isSimple = b.isSimple := by
  rw [SPath.up_eq]; exact SPath.isSimple_wk _ b

end ShiftMore

/-! ## Shifting under a block

A call's body is read under the parameters and return variables it
declares in its caller (`Thin.atop`): its positions keep their numbers, the
caller's locals sit under them.  `Idx.under` moves a caller's local over
the locals `ρ` pushed on it, by recursion on the list `ρ`, which is not an
indexed family. -/

/-- Nothing kept, `Γ` added. -/
def Thin.nilTo : (Γ : Ctx) → Thin [] Γ
  | [] => .refl
  | _ :: Γ => .drop (Thin.nilTo Γ)

/-- `ρ`'s locals kept, the context `Γ` under them added. -/
def Thin.atop : (ρ Γ : Ctx) → Thin ρ (ρ ++ Γ)
  | [], Γ => Thin.nilTo Γ
  | _ :: ρ, Γ => .keep (Thin.atop ρ Γ)

/-- A local of `Γ`, read with the locals `ρ` pushed on it. -/
def Idx.under {Γ : Ctx} {t : LTy} (i : Idx Γ t) : (ρ : Ctx) → Idx (ρ ++ Γ) t
  | [] => i
  | _ :: ρ => .there (Idx.under i ρ)

end Solidity
