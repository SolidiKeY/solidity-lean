import Solidity.Calculus.Shift
import Solidity.Syntax.PushSource

/-!
# Expressions available to the upstream program rules

Native modular builtins are Lean-only. This recursive check also inspects
array indices and reference paths: unfolding a containing expression must
not expose a native assignment in a SolKey-only derivation.
-/

namespace Solidity
variable {C : Contract}

mutual

def SPath.keyValue {Γ : Ctx} {T : Ty} : SPath C Γ T → Bool
  | .alias _ => true
  | .loc l => l.keyValue

def Loc.keyValue {Γ : Ctx} {T : Ty} : Loc C Γ T → Bool
  | .root .. => true
  | .field b _ _ => b.keyValue
  | .index _ b i => b.keyValue && i.keyValue

def MPath.keyValue {Γ : Ctx} {T : Ty} : MPath C Γ T → Bool
  | .var .. => true
  | .loc l => l.keyValue

def MLoc.keyValue {Γ : Ctx} {T : Ty} : MLoc C Γ T → Bool
  | .field b _ _ => b.keyValue
  | .index _ b i => b.keyValue && i.keyValue

def Val.keyValue {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .simple _ => true
  | .read l | .readMem l => l.keyValue
  | .binop _ _ _ a b => a.keyValue && b.keyValue
  | .unop _ _ _ a => a.keyValue
  | .ternary c a b => c.keyValue && a.keyValue && b.keyValue
  | .len b _ | .mlen b _ | .keccak b _ => b.keyValue
  | .modular .. => false

end

def Src.keyValue {Γ : Ctx} {T : Ty} : Src C Γ T → Bool
  | .val v => v.keyValue
  | .copy p _ | .copyMem p => p.keyValue
  | .fixedCopy .. => false

/-- A fixed-array shape adapter is outside the conservative upstream
program fragment until it has a direct same-sort source representation. -/
theorem Src.keyValue_ofFixedCopy {Γ : Ctx} {T : Ty} {r : Src C Γ T}
    (h : r.isFixedCopy = true) : r.keyValue = false := by
  cases r <;> first | rfl | cases h

/-- An upstream-fragment source needs no fixed-shape adapter. -/
theorem Src.notFixedCopy_of_keyValue {Γ : Ctx} {T : Ty} {r : Src C Γ T}
    (h : r.keyValue = true) : r.isFixedCopy = false := by
  cases r <;> first | rfl | cases h

def ARhs.keyValue {Γ : Ctx} {R : RefTy} : ARhs C Γ R → Bool
  | .path p | .push p _ => p.keyValue

def MRhs.keyValue {Γ : Ctx} {R : RefTy} : MRhs C Γ R → Bool
  | .alias p | .copy p _ => p.keyValue
  | .newArr .. => true

def NewLhs.keyValue {Γ : Ctx} {R : RefTy} : NewLhs C Γ R → Bool
  | .store l | .mem l => l.keyValue

def MSrc.keyValue {Γ : Ctx} {T : Ty} : MSrc C Γ T → Bool
  | .val v => v.keyValue
  | .ref p => p.keyValue

def OpLoc.keyValue {Γ : Ctx} {p : PrimTy} : OpLoc C Γ p → Bool
  | .local _ | .root .. => true
  | .field b _ _ | .index _ b _ => b.keyValue
  | .mfield b _ _ | .mindex _ b _ => b.keyValue

def Args.keyValues {Γ : Ctx} : {ps : Ctx} → Args C Γ ps → Bool
  | _, .nil => true
  | _, .snoc as _ _ e => as.keyValues && e.keyValue
  | _, .snocStorage as _ _ e => as.keyValues && e.keyValue
  | _, .snocMemory as _ _ e => as.keyValues && e.keyValue

mutual

theorem SPath.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} :
    (e : SPath C Γ T) → (e.wk h).keyValue = e.keyValue
  | .alias _ => rfl
  | .loc l => Loc.keyValue_wk h l

theorem Loc.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} :
    (e : Loc C Γ T) → (e.wk h).keyValue = e.keyValue
  | .root .. => rfl
  | .field b _ _ => SPath.keyValue_wk h b
  | .index _ b i => by
    show ((b.wk h).keyValue && (i.wk h).keyValue) = _
    rw [SPath.keyValue_wk h b, Val.keyValue_wk h i]; rfl

theorem MPath.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} :
    (e : MPath C Γ T) → (e.wk h).keyValue = e.keyValue
  | .var .. => rfl
  | .loc l => MLoc.keyValue_wk h l

theorem MLoc.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} :
    (e : MLoc C Γ T) → (e.wk h).keyValue = e.keyValue
  | .field b _ _ => MPath.keyValue_wk h b
  | .index _ b i => by
    show ((b.wk h).keyValue && (i.wk h).keyValue) = _
    rw [MPath.keyValue_wk h b, Val.keyValue_wk h i]; rfl

theorem Val.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} :
    (e : Val C Γ p) → (e.wk h).keyValue = e.keyValue
  | .simple _ | .modular .. => rfl
  | .read l => Loc.keyValue_wk h l
  | .readMem l => MLoc.keyValue_wk h l
  | .binop _ _ _ a b => by
    show ((a.wk h).keyValue && (b.wk h).keyValue) = _
    rw [Val.keyValue_wk h a, Val.keyValue_wk h b]; rfl
  | .unop _ _ _ a => Val.keyValue_wk h a
  | .ternary c a b => by
    show ((c.wk h).keyValue && (a.wk h).keyValue && (b.wk h).keyValue) = _
    rw [Val.keyValue_wk h c, Val.keyValue_wk h a, Val.keyValue_wk h b]; rfl
  | .len b _ => SPath.keyValue_wk h b
  | .mlen b _ => MPath.keyValue_wk h b
  | .keccak b _ => MPath.keyValue_wk h b

end

theorem Src.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} (e : Src C Γ T) :
    (e.wk h).keyValue = e.keyValue := by
  cases e <;> simp only [Src.wk, Src.keyValue, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk]

theorem ARhs.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} (e : ARhs C Γ R) :
    (e.wk h).keyValue = e.keyValue := by
  cases e <;> simp only [ARhs.wk, ARhs.keyValue, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk]

theorem MRhs.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} (e : MRhs C Γ R) :
    (e.wk h).keyValue = e.keyValue := by
  cases e <;> simp only [MRhs.wk, MRhs.keyValue, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk]

theorem NewLhs.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} (e : NewLhs C Γ R) :
    (e.wk h).keyValue = e.keyValue := by
  cases e <;> simp only [NewLhs.wk, NewLhs.keyValue, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk]

theorem MSrc.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} (e : MSrc C Γ T) :
    (e.wk h).keyValue = e.keyValue := by
  cases e <;> simp only [MSrc.wk, MSrc.keyValue, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk]

theorem OpLoc.keyValue_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} (e : OpLoc C Γ p) :
    (e.wk h).keyValue = e.keyValue := by
  cases e <;> simp only [OpLoc.wk, OpLoc.keyValue, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk]

theorem Args.keyValues_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {ps : Ctx} (args : Args C Γ ps) :
    (args.wk h).keyValues = args.keyValues := by
  induction args with
  | nil => rfl
  | snoc as p x e ih =>
    show ((as.wk h).keyValues && (e.wk h).keyValue) = _
    rw [ih, Val.keyValue_wk]; rfl
  | snocStorage as R x e ih =>
    show ((as.wk h).keyValues && (e.wk h).keyValue) = _
    rw [ih, SPath.keyValue_wk]; rfl
  | snocMemory as R x e ih =>
    show ((as.wk h).keyValues && (e.wk h).keyValue) = _
    rw [ih, MPath.keyValue_wk]; rfl

end Solidity
