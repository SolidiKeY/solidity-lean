import Solidity.Calculus.Core.Fml

/-!
# Lowering scoped expressions to terms

`Update.lean`'s lowering (Maude's `lower(LV, C)`) on the scoped syntax: a
program expression read in `Γ` becomes a term read in `Γ`, a local its
position.  `lower_erase` says it is the old lowering of the erased
expression, the bridge `Fml.erase` needs for an update rule's premise.
-/

namespace Solidity.Core

open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

def Simple.lower {Γ : Ctx} {p : PrimTy} : Simple C Γ p → Tm C Γ .val
  | .lit n _ => .app0 (.lit (.int n))
  | .bool b => .app0 (.lit (.bool b))
  | .local i => .pvV i
  | .env k _ => .app0 (.env k)

/-- An index of key type `k` as the word it is hashed as: a `bool` key `b`
is `b ? 1 : 0` (`Term.keyAt`). -/
def Tm.keyAt {Γ : Ctx} : PrimTy → Tm C Γ .val → Tm C Γ .val
  | .bool, t => .app3 .ite t (.app0 (.lit (.int 1))) (.app0 (.lit (.int 0)))
  | .uint, t => t
  | .int, t => t

mutual

def SPath.lower {Γ : Ctx} : {T : Ty} → SPath C Γ T → Tm C Γ .path
  | _, .alias i => .pvP i
  | _, .loc l => l.lower

def Loc.lower {Γ : Ctx} : {T : Ty} → Loc C Γ T → Tm C Γ .path
  | _, .root r _ => .app0 (.root r)
  | _, .field b f _ => .app1 (.field f) rfl b.lower
  | _, .index (k := k) _ b i => .app2 .at b.lower (Tm.keyAt k i.lower)

def MPath.lower {Γ : Ctx} : {T : Ty} → MPath C Γ T → Tm C Γ .ident
  | _, .var i _ => .pvI i
  | _, .loc l => .app2 .iread (.app0 .memory) l.lower

def MLoc.lower {Γ : Ctx} : {T : Ty} → MLoc C Γ T → Tm C Γ .addr
  | _, .field b f _ => .app1 (.mfield f) rfl b.lower
  | _, .index _ b i => .app2 .mat b.lower i.lower

def Val.lower {Γ : Ctx} : {p : PrimTy} → Val C Γ p → Tm C Γ .val
  | _, .simple s => s.lower
  | _, .read l => .app2 .find (.app0 .storage) l.lower
  | _, @Val.binop _ _ p _ op _ _ a b => .app2 (.binop op p) a.lower b.lower
  | _, @Val.unop _ _ p _ op _ _ a => .app1 (.unop op p) rfl a.lower
  | _, .ternary c a b => .app3 .ite c.lower a.lower b.lower
  | _, .readMem l => .app2 .read (.app0 .memory) l.lower
  | _, .len b _ => .app2 .len (.app0 .storage) b.lower
  | _, .mlen b _ => .app2 .mlen (.app0 .memory) b.lower

end

/-- An index's term: the word its key is hashed as (`Tm.keyAt`), what
`Loc.lower` writes; a rule names it so, and it prints as the index. -/
@[reducible] def Simple.keyLower {Γ : Ctx} {k : PrimTy} (s : Simple C Γ k) : Tm C Γ .val :=
  Tm.keyAt k s.lower
@[reducible] def Val.keyLower {Γ : Ctx} {k : PrimTy} (v : Val C Γ k) : Tm C Γ .val :=
  Tm.keyAt k v.lower

/-- A write's source as a storage value: the value, or the copied subtree. -/
def Src.lower {Γ : Ctx} {T : Ty} : Src C Γ T → Tm C Γ .sv
  | .val v => .app1 .sval rfl v.lower
  | .copy p _ => .app2 .sfind (.app0 .storage) p.lower

/-- A memory write's source. -/
def MSrc.lower {Γ : Ctx} {T : Ty} : MSrc C Γ T → Tm C Γ .mv
  | .val v => .app1 .mval rfl v.lower
  | .ref p => .app1 .ref rfl p.lower

/-! ## Lowering commutes with erasure -/

theorem Tm.keyAt_erase {Γ : Ctx} (ns : List Var) (k : PrimTy) (t : Tm C Γ .val) :
    (Tm.keyAt k t).erase ns = Solidity.Term.keyAt k (t.erase ns) := by
  cases k <;> rfl

theorem Simple.lower_erase {Γ : Ctx} {p : PrimTy} (ns : List Var) (s : Simple C Γ p) :
    s.lower.erase ns = (s.erase ns).lower := by
  cases s <;> rfl

mutual

theorem SPath.lower_erase {Γ : Ctx} (ns : List Var) : {T : Ty} → (b : SPath C Γ T) →
    b.lower.erase ns = (b.erase ns).lower
  | _, .alias _ => rfl
  | _, .loc l => l.lower_erase ns

theorem Loc.lower_erase {Γ : Ctx} (ns : List Var) : {T : Ty} → (l : Loc C Γ T) →
    l.lower.erase ns = (l.erase ns).lower
  | _, .root .. => rfl
  | _, .field b f _ => by
    show Surface.Tm.app1 _ (b.lower.erase ns) = _
    rw [b.lower_erase ns]; rfl
  | _, .index (k := k) _ b i => by
    show Surface.Tm.app2 _ (b.lower.erase ns) ((Tm.keyAt k i.lower).erase ns) = _
    rw [b.lower_erase ns, Tm.keyAt_erase, i.lower_erase ns]; rfl

theorem MPath.lower_erase {Γ : Ctx} (ns : List Var) : {T : Ty} → (b : MPath C Γ T) →
    b.lower.erase ns = (b.erase ns).lower
  | _, .var .. => rfl
  | _, .loc l => by
    show Surface.Tm.app2 _ _ (l.lower.erase ns) = _
    rw [l.lower_erase ns]; rfl

theorem MLoc.lower_erase {Γ : Ctx} (ns : List Var) : {T : Ty} → (l : MLoc C Γ T) →
    l.lower.erase ns = (l.erase ns).lower
  | _, .field b f _ => by
    show Surface.Tm.app1 _ (b.lower.erase ns) = _
    rw [b.lower_erase ns]; rfl
  | _, .index _ b i => by
    show Surface.Tm.app2 _ (b.lower.erase ns) (i.lower.erase ns) = _
    rw [b.lower_erase ns, i.lower_erase ns]; rfl

theorem Val.lower_erase {Γ : Ctx} (ns : List Var) : {p : PrimTy} → (v : Val C Γ p) →
    v.lower.erase ns = (v.erase ns).lower
  | _, .simple s => s.lower_erase ns
  | _, .read l => by
    show Surface.Tm.app2 _ _ (l.lower.erase ns) = _
    rw [l.lower_erase ns]; rfl
  | _, .binop _ _ _ a b => by
    show Surface.Tm.app2 _ (a.lower.erase ns) (b.lower.erase ns) = _
    rw [a.lower_erase ns, b.lower_erase ns]; rfl
  | _, .unop _ _ _ a => by
    show Surface.Tm.app1 _ (a.lower.erase ns) = _
    rw [a.lower_erase ns]; rfl
  | _, .ternary c a b => by
    show Surface.Tm.app3 _ (c.lower.erase ns) (a.lower.erase ns) (b.lower.erase ns) = _
    rw [c.lower_erase ns, a.lower_erase ns, b.lower_erase ns]; rfl
  | _, .readMem l => by
    show Surface.Tm.app2 _ _ (l.lower.erase ns) = _
    rw [l.lower_erase ns]; rfl
  | _, .len b _ => by
    show Surface.Tm.app2 _ _ (b.lower.erase ns) = _
    rw [b.lower_erase ns]; rfl
  | _, .mlen b _ => by
    show Surface.Tm.app2 _ _ (b.lower.erase ns) = _
    rw [b.lower_erase ns]; rfl

end

theorem Src.lower_erase {Γ : Ctx} {T : Ty} (ns : List Var) (s : Src C Γ T) :
    s.lower.erase ns = (s.erase ns).lower := by
  cases s with
  | val v => show Surface.Tm.app1 _ (v.lower.erase ns) = _; rw [v.lower_erase ns]; rfl
  | copy p _ => show Surface.Tm.app2 _ _ (p.lower.erase ns) = _; rw [p.lower_erase ns]; rfl

theorem MSrc.lower_erase {Γ : Ctx} {T : Ty} (ns : List Var) (s : MSrc C Γ T) :
    s.lower.erase ns = (s.erase ns).lower := by
  cases s with
  | val v => show Surface.Tm.app1 _ (v.lower.erase ns) = _; rw [v.lower_erase ns]; rfl
  | ref p => show Surface.Tm.app1 _ (p.lower.erase ns) = _; rw [p.lower_erase ns]; rfl

end Solidity.Core
