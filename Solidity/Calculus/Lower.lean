import Solidity.Calculus.Fml

/-!
# Lowering scoped expressions to terms

`Update.lean`'s lowering (Maude's `lower(LV, C)`) on the scoped syntax: a
program expression read in `Γ` becomes a term read in `Γ`, a local its
position.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

def Simple.lower {Γ : Ctx} {p : PrimTy} : Simple C Γ p → Tm C Γ .val
  | .lit n _ => .app0 (.lit (.int n))
  | .bool b => .app0 (.lit (.bool b))
  | .local i => .pvV i
  | .env k _ => .app0 (.env k)

/-- An index of key type `k` as the word it is hashed as: a `bool` key `b`
is `b ? 1 : 0`, as solc pads it (`Value.keyAt`). -/
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

end Solidity
