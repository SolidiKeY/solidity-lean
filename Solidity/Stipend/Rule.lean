import Solidity.Syntax.Scoped
import Solidity.Roadmap.Evm

namespace Solidity.Stipend

open Solidity.Roadmap.Evm (StipendRule Pin pinned)

variable {C : Contract}

structure CostModel where
  unit : Nat
  reserve : Nat

def osakaCold : CostModel := ⟨50, 300⟩

def addC (a b : Option Nat) : Option Nat := do let x ← a; let y ← b; some (x + y)

example (a : Option Nat) : addC none a = none := rfl

example (a : Option Nat) : addC a none = none := by cases a <;> rfl

def maxC (a b : Option Nat) : Option Nat := do let x ← a; let y ← b; some (max x y)

def valCost {Γ : Ctx} : {p : PrimTy} → Val C Γ p → Option Nat
  | _, .simple _ => some 1
  | _, .binop op _ _ a b =>
    if op = .pow ∨ op = .powW then none else addC (some 1) (addC (valCost a) (valCost b))
  | _, .unop _ _ _ a => addC (some 1) (valCost a)
  | _, .ternary c a b => addC (some 1) (addC (valCost c) (maxC (valCost a) (valCost b)))
  | _, .modular _ a b k => addC (some 1) (addC (valCost a) (addC (valCost b) (valCost k)))
  | _, .read _ | _, .readMem _ | _, .len _ _ | _, .mlen _ _ | _, .hash _ _ _ => none

example {Γ : Ctx} {p : PrimTy} (l : Loc C Γ (.prim p)) :
    valCost (.read l) = none := rfl

example {Γ : Ctx} {p : PrimTy} (l : MLoc C Γ (.prim p)) :
    valCost (.readMem l) = none := rfl

example {Γ : Ctx} {R : RefTy} (k : HashKind) (b : MPath C Γ (.ref R)) :
    valCost (.hash k b rfl) = none := rfl

def argsCost {Γ : Ctx} : {ps : Ctx} → Args C Γ ps → Option Nat
  | _, .nil => some 0
  | _, .snoc as _ _ e => addC (argsCost as) (valCost e)
  | _, .snocStorage .. | _, .snocMemory .. => none

def revPartCost {Γ : Ctx} : RevPart C Γ → Option Nat
  | .bytes bs => some (bs.length / 32 + 1)
  | .sel _ => some 1
  | .word v => (valCost v)
  | .mem _ _ => none

example {Γ : Ctx} (kind : CatchKind) (src : Idx Γ (.mem bytesR)) :
    revPartCost (.mem kind src : RevPart C Γ) = none := rfl

def revListCost {Γ : Ctx} : List (RevPart C Γ) → Option Nat
  | [] => some 0
  | d :: ds => addC (revPartCost d) (revListCost ds)

def retOk {Γ rs Γ' : Ctx} : CallRet Γ rs Γ' → Bool
  | .none | .val .. => true
  | .rets _ | .mem .. | .storage .. => false

mutual

def stmtCost : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Option Nat
  | _, _, .assignLocal _ r => addC (some 1) (valCost r)
  | _, _, .declLocal _ _ none => some 1
  | _, _, .declLocal _ _ (some v) => addC (some 1) (valCost v)
  | _, _, .require c => addC (some 1) (valCost c)
  | _, _, .assert c => addC (some 1) (valCost c)
  | _, _, .revert => some 1
  | _, _, .assumeFalse => some 1
  | _, _, .revertData d => addC (some 1) (revListCost d)
  | _, _, .ite c t e => addC (some 1) (addC (valCost c) (maxC (progCost t) (progCost e)))
  | _, _, .block b => progCost b
  | _, _, .call _ args ret body =>
    if retOk ret then addC (some 1) (addC (argsCost args) (progCost body)) else none
  | _, _, .assign .. | _, _, .rebind .. | _, _, .declStorage .. | _, _, .opAssign .. => none
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .assignLocalPush .. | _, _, .push .. => none
  | _, _, .pop .. | _, _, .transfer .. | _, _, .send .. | _, _, .declMem .. => none
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete .. => none
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .tryCall .. | _, _, .loop .. => none
  | _, _, .pushOpAssign .. | _, _, .pushIncDec .. | _, _, .callReceiver .. => none
  | _, _, .callReceiverPush .. | _, _, .callRec .. | _, _, .catchData .. => none

def progCost : {Γ Γ' : Ctx} → Prog C Γ Γ' → Option Nat
  | _, _, .nil => some 0
  | _, _, .cons s P => addC (stmtCost s) (progCost P)

end

structure Body (C : Contract) where
  {out : Ctx}
  prog : Prog C [] out

def fitsWith (M : CostModel) (s : Nat) (b : Body C) : Bool :=
  match progCost b.prog with
  | some c => M.unit * c + M.reserve ≤ s
  | none => false

def rule (C : Contract) : StipendRule (Body C) where
  fits b := fitsWith osakaCold pinned.stipend b = true

instance (b : Body C) : Decidable ((rule C).fits b) := by unfold rule; infer_instance

def Enforced {Body : Type} (R : StipendRule Body) (failsUnderStipend : Body → Prop) : Prop :=
  ∀ b, ¬R.fits b → failsUnderStipend b

def Obligation (C : Contract) (gasUsed : Body C → Nat) (failsUnderStipend : Body C → Prop) :
    Prop :=
  (rule C).Fitted pinned gasUsed ∧ Enforced (rule C) failsUnderStipend

theorem fits_iff (b : Body C) : (rule C).fits b ↔ ∃ c, progCost b.prog = some c ∧ c ≤ 40 := by
  show fitsWith osakaCold pinned.stipend b = true ↔ _
  unfold fitsWith
  cases h : progCost b.prog with
  | none => simp only [Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
  | some c =>
    simp only [Option.some.injEq, exists_eq_left', decide_eq_true_eq]
    show 50 * c + 300 ≤ 2300 ↔ c ≤ 40
    omega

theorem not_fits_cons {Γ₁ : Ctx} {out : Ctx} (s : Stmt C [] Γ₁) (P : Prog C Γ₁ out)
    (h : stmtCost s = none) : ¬(rule C).fits ⟨.cons s P⟩ := by
  rw [fits_iff]
  rintro ⟨c, hc, -⟩
  simp only [progCost, h, addC, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hc

theorem empty_fits : (rule C).fits ⟨(.nil : Prog C [] [])⟩ :=
  (fits_iff _).2 ⟨0, rfl, by decide⟩

def requireValue : Prog C [] [] :=
  .cons (.require (.binop .neB rfl rfl (.simple (.env .msgValue rfl)) (.simple (.lit 0 rfl)))) .nil

theorem requireValue_fits : (rule C).fits ⟨(requireValue : Prog C [] [])⟩ :=
  (fits_iff _).2 ⟨4, rfl, by decide⟩

theorem transfer_not_fits :
    ¬(rule C).fits ⟨(.cons (.transfer (.simple (.env .msgSender rfl)) (.simple (.lit 1 rfl))) .nil :
      Prog C [] [])⟩ :=
  not_fits_cons _ _ rfl

theorem loop_not_fits (a : LoopAnn C []) :
    ¬(rule C).fits ⟨(.cons (.loop a (.simple (.bool false)) .nil) .nil : Prog C [] [])⟩ :=
  not_fits_cons _ _ rfl

theorem assign_not_fits {T : Ty} (l : Loc C [] T) (r : Src C [] T) :
    ¬(rule C).fits ⟨(.cons (.assign l r) .nil : Prog C [] [])⟩ :=
  not_fits_cons _ _ rfl

theorem read_not_fits {p : PrimTy} (l : Loc C [] (.prim p)) :
    ¬(rule C).fits ⟨(.cons (.require (.binop .eqB rfl rfl (.read l) (.read l))) .nil :
      Prog C [] [])⟩ := by
  rw [fits_iff]
  rintro ⟨c, hc, -⟩
  cases hc

def requires : Nat → Prog C [] []
  | 0 => .nil
  | n + 1 => .cons (.require (.binop .neB rfl rfl (.simple (.env .msgValue rfl))
      (.simple (.lit 0 rfl)))) (requires n)

theorem requires_cost (n : Nat) : progCost (requires n : Prog C [] []) = some (4 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show addC (some 4) (progCost (requires n : Prog C [] [])) = some (4 * (n + 1))
    rw [ih]
    show some (4 + 4 * n) = some (4 * (n + 1))
    rw [Nat.mul_succ, Nat.add_comm]

theorem requires_ten_fits : (rule C).fits ⟨(requires 10 : Prog C [] [])⟩ :=
  (fits_iff _).2 ⟨40, requires_cost 10, by decide⟩

theorem requires_eleven_not_fits : ¬(rule C).fits ⟨(requires 11 : Prog C [] [])⟩ := by
  rw [fits_iff, requires_cost]
  rintro ⟨c, hc, hle⟩
  cases hc
  omega

theorem pow_not_fits {p : PrimTy} (x : Var) (a b : Val C [] p) (h : BinOp.pow.accepts p = true)
    (hq : BinOp.pow.ret p = .uint) :
    ¬(rule C).fits ⟨(.cons (.declLocal .uint x (some (.binop .pow h hq a b))) .nil :
      Prog C [] [.val .uint])⟩ := by
  rw [fits_iff]
  rintro ⟨c, hc, -⟩
  simp only [progCost, stmtCost, valCost, true_or, if_true, addC, Option.bind_eq_bind,
    Option.bind_none, Option.bind_some, reduceCtorEq] at hc

end Solidity.Stipend

/-- info: 'Solidity.Stipend.fits_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Stipend.fits_iff
/-- info: 'Solidity.Stipend.requires_eleven_not_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Stipend.requires_eleven_not_fits

