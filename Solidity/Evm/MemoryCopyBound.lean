import Solidity.Evm.MemoryStorageStructCopy

/-!
# Storage representation bounds for reached memory copies

A storage representation has an explicit strict array-length bound L. A
memory-to-storage copy must fit that same bound. This source-computed demand
follows only reached copies, skips copy-free suffixes, and costs zero for all
previously admitted programs; it is separate from allocation capacity.
-/
namespace Solidity.Evm.Memory
variable {C : Contract}

private def arrayCopyKind : RefTy → Bool
  | .array (.prim _) => true
  | _ => false

private def arrayCopyTargetKind {Γ : Ctx} {R : RefTy} (_dst : Loc C Γ (.ref R)) : Bool := arrayCopyKind R

/-- A failed destination never reaches the payload copy. -/
private def arrayCopyDemand {Γ : Ctx} : {R : RefTy} → Loc C Γ (.ref R) →
    MPath C Γ (.ref R) → State C Γ → Nat
  | .array (.prim _), dst, src, σ => match src.mvalT σ with
    | .error _ => 0
    | .ok r => match dst.resolveT σ with
      | .error _ => 0
      | .ok _ => σ.heap.len r .dyn + 1
  | _, _, _, _ => 0

private def fixedDynamicKind {E : Ty} {n : Nat} {R : RefTy} (_shape : FixedCopy E n R) : Bool :=
  match E, R with | .prim _, .array _ => true | _, _ => false

private def sourceArrayKind {Γ : Ctx} {T : Ty} (rhs : Src C Γ T) : Bool :=
  Src.casesOn (motive := fun _ _ => Bool) rhs
    (val := fun _ => false) (copy := fun _ _ => false)
    (fixedCopy := fun _ _ _ => false) (copyMem := fun _ => false)
    (fixedCopyMem := fun _ shape => fixedDynamicKind shape)

private def fixedDynamicDemand {Γ : Ctx} : {E : Ty} → {n : Nat} → {R : RefTy} →
    (shape : FixedCopy E n R) → Loc C Γ (.ref R) →
    MPath C Γ (.ref (.fixed E n)) → State C Γ → Nat
  | .prim _, n, _, shape, dst, src, σ =>
    FixedCopy.casesOn (motive := fun R _ => Loc C Γ (.ref R) → Nat) shape
      (dynamic := fun _ dst => match src.mvalT σ with
        | .error _ => 0
        | .ok _ => match dst.resolveT σ with | .error _ => 0 | .ok _ => n + 1)
      (fixed := fun _ _ _ => 0) dst
  | .ref _, _, _, _, _, _, _ => 0

private def sourceCopyDemand {Γ : Ctx} {T : Ty} (dst : Loc C Γ T)
    (rhs : Src C Γ T) : State C Γ → Nat :=
  Src.casesOn (motive := fun T _ => Loc C Γ T → State C Γ → Nat) rhs
    (val := fun _ _ _ => 0) (copy := fun _ _ _ _ => 0)
    (fixedCopy := fun _ _ _ _ _ => 0) (copyMem := fun _ _ _ => 0)
    (fixedCopyMem := fun src shape dst => fixedDynamicDemand shape dst src) dst

mutual
def hasArrayCopyStmt : {Γ Δ : Ctx} → Stmt C Γ Δ → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ rhs => sourceArrayKind rhs)
    (rebind := fun _ _ => false)
    (assignLocal := fun _ _ => false)
    (declLocal := fun _ _ _ => false)
    (declStorage := fun _ _ _ => false)
    (opAssign := fun _ _ _ _ _ => false)
    (incDec := fun _ _ _ => false)
    (assignIncDec := fun _ _ _ _ _ => false)
    (assignLocalPush := fun _ _ => false)
    (pushOpAssign := fun _ _ _ _ _ => false)
    (pushIncDec := fun _ _ _ => false)
    (push := fun _ _ _ => false)
    (pop := fun _ => false)
    (transfer := fun _ _ => false)
    (send := fun _ _ _ _ => false)
    (declMem := fun _ _ _ _ _ => false)
    (rebindMem := fun _ _ => false)
    (assignFromMem := fun dst _ => arrayCopyTargetKind dst)
    (assignMem := fun _ _ => false)
    (delete := fun _ => false)
    (deleteMem := fun _ _ => false)
    (assignNew := fun _ _ _ => false)
    (ite := fun _ P Q => hasArrayCopy P || hasArrayCopy Q)
    (require := fun _ => false)
    (assert := fun _ => false)
    (revert := false)
    (assumeFalse := false)
    (call := fun _ _ _ _ => false)
    (callReceiver := fun _ _ _ _ _ => false)
    (callReceiverPush := fun _ _ _ _ _ _ => false)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ => false)
    (loop := fun _ _ _ => false)
    (block := fun P => hasArrayCopy P)
    (callRec := fun _ _ _ _ _ => false)
    (revertData := fun _ => false)
    (catchData := fun _ _ _ _ _ _ _ _ => false)
  termination_by structural _ _ s => s

def hasArrayCopy : {Γ Δ : Ctx} → Prog C Γ Δ → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P false
      (fun s P => hasArrayCopyStmt s || hasArrayCopy P)
  termination_by structural _ _ P => P
end

mutual
private def rawCopyBoundStmt : {Γ Δ : Ctx} → Stmt C Γ Δ → State C Γ → Nat
  | _, _, s => Stmt.casesOn (motive_1 := fun Γ _ _ => State C Γ → Nat) s
    (assign := fun dst rhs => sourceCopyDemand dst rhs)
    (rebind := fun _ _ => fun _ => 0)
    (assignLocal := fun _ _ => fun _ => 0)
    (declLocal := fun _ _ _ => fun _ => 0)
    (declStorage := fun _ _ _ => fun _ => 0)
    (opAssign := fun _ _ _ _ _ => fun _ => 0)
    (incDec := fun _ _ _ => fun _ => 0)
    (assignIncDec := fun _ _ _ _ _ => fun _ => 0)
    (assignLocalPush := fun _ _ => fun _ => 0)
    (pushOpAssign := fun _ _ _ _ _ => fun _ => 0)
    (pushIncDec := fun _ _ _ => fun _ => 0)
    (push := fun _ _ _ => fun _ => 0)
    (pop := fun _ => fun _ => 0)
    (transfer := fun _ _ => fun _ => 0)
    (send := fun _ _ _ _ => fun _ => 0)
    (declMem := fun _ _ _ _ _ => fun _ => 0)
    (rebindMem := fun _ _ => fun _ => 0)
    (assignFromMem := fun dst src => arrayCopyDemand dst src)
    (assignMem := fun _ _ => fun _ => 0)
    (delete := fun _ => fun _ => 0)
    (deleteMem := fun _ _ => fun _ => 0)
    (assignNew := fun _ _ _ => fun _ => 0)
    (ite := fun c P Q σ => match c.evalT σ with | .ok v => if boolT v then copyBoundProg P σ else copyBoundProg Q σ | .error _ => 0)
    (require := fun _ => fun _ => 0)
    (assert := fun _ => fun _ => 0)
    (revert := fun _ => 0)
    (assumeFalse := fun _ => 0)
    (call := fun _ _ _ _ => fun _ => 0)
    (callReceiver := fun _ _ _ _ _ => fun _ => 0)
    (callReceiverPush := fun _ _ _ _ _ _ => fun _ => 0)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ => fun _ => 0)
    (loop := fun _ _ _ => fun _ => 0)
    (block := fun P σ => copyBoundProg P σ)
    (callRec := fun _ _ _ _ _ => fun _ => 0)
    (revertData := fun _ => fun _ => 0)
    (catchData := fun _ _ _ _ _ _ _ _ => fun _ => 0)
  termination_by structural _ _ s => s

def copyBoundProg : {Γ Δ : Ctx} → Prog C Γ Δ → State C Γ → Nat
  | _, _, P => Prog.casesOn (motive_2 := fun Γ _ _ => State C Γ → Nat) P (fun _ => 0)
      (fun s P σ => max (if hasArrayCopyStmt s then rawCopyBoundStmt s σ else 0)
        (if hasArrayCopy P then match s.run σ with
          | .ok o => copyBoundProg P o.st
          | .error _ => 0
         else 0))
  termination_by structural _ _ P => P
end

/-- Named constructor equations keep simplification away from recursor lambdas. -/
theorem hasArrayCopy_nil {Γ : Ctx} : hasArrayCopy (Prog.nil (C := C) (Γ := Γ)) = false := rfl
theorem hasArrayCopy_cons {Γ Δ Ξ : Ctx} (s : Stmt C Γ Δ) (P : Prog C Δ Ξ) :
    hasArrayCopy (.cons s P) = (hasArrayCopyStmt s || hasArrayCopy P) := rfl
theorem hasArrayCopyStmt_block {Γ Δ : Ctx} (P : Prog C Γ Δ) :
    hasArrayCopyStmt (.block P) = hasArrayCopy P := rfl
theorem hasArrayCopyStmt_ite {Γ Δ Ξ : Ctx} (c : Val C Γ .bool)
    (P : Prog C Γ Δ) (Q : Prog C Γ Ξ) :
    hasArrayCopyStmt (.ite c P Q) = (hasArrayCopy P || hasArrayCopy Q) := rfl
theorem copyBoundProg_nil {Γ : Ctx} (σ : State C Γ) : copyBoundProg .nil σ = 0 := rfl

def copyBoundStmt {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) : Nat :=
  if hasArrayCopyStmt s then rawCopyBoundStmt s σ else 0

theorem copyBoundProg_zero {Γ Δ : Ctx} (P : Prog C Γ Δ)
    (h : hasArrayCopy P = false) (σ : State C Γ) : copyBoundProg P σ = 0 := by
  cases P with
  | nil => rfl
  | cons s P =>
    change (hasArrayCopyStmt s || hasArrayCopy P) = false at h
    have hh := Bool.or_eq_false_iff.mp h
    rw [copyBoundProg]
    simp only [hh.1, hh.2, Bool.false_eq_true, if_false, Nat.max_self]

theorem copyBoundProg_cons {Γ Δ Ξ : Ctx} (s : Stmt C Γ Δ) (P : Prog C Δ Ξ) (σ : State C Γ) :
    copyBoundProg (.cons s P) σ = max (copyBoundStmt s σ)
      (match s.run σ with | .ok o => copyBoundProg P o.st | .error _ => 0) := by
  rw [copyBoundProg]
  change max (copyBoundStmt s σ) _ = _
  congr 1
  cases ht : hasArrayCopy P with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    cases s.run σ with
    | ok o => exact (copyBoundProg_zero P ht o.st).symm
    | error _ => rfl
  | true => simp only [if_true]

theorem copyBoundStmt_block {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) :
    copyBoundStmt (.block P) σ = copyBoundProg P σ := by
  simp only [copyBoundStmt, hasArrayCopyStmt, rawCopyBoundStmt]
  rcases Bool.eq_false_or_eq_true (hasArrayCopy P) with hh | hh
  · simp only [hh, ite_true]
  · simp only [hh, Bool.false_eq_true, ite_false]
    exact (copyBoundProg_zero P hh σ).symm

theorem copyBoundStmt_ite {Γ Δ Ξ : Ctx} (c : Val C Γ .bool)
    (P : Prog C Γ Δ) (Q : Prog C Γ Ξ) (σ : State C Γ) :
    copyBoundStmt (.ite c P Q) σ = match c.evalT σ with
      | .ok v => if boolT v then copyBoundProg P σ else copyBoundProg Q σ
      | .error _ => 0 := by
  simp only [copyBoundStmt, hasArrayCopyStmt, rawCopyBoundStmt]
  rcases Bool.eq_false_or_eq_true (hasArrayCopy P) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (hasArrayCopy Q) with hq | hq
  all_goals simp only [hp, hq, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
    ite_true, Bool.false_eq_true, ite_false]
  rw [copyBoundProg_zero P hp, copyBoundProg_zero Q hq]
  cases c.evalT σ with
  | error _ => rfl
  | ok v => simp only [ite_self]

theorem copyBoundStmt_array {Γ : Ctx} {p : PrimTy}
    (dst : Loc C Γ (.ref (.array (.prim p)))) (src : MPath C Γ (.ref (.array (.prim p))))
    (σ : State C Γ) (L : Nat) (h : copyBoundStmt (.assignFromMem dst src) σ ≤ L) :
    ∀ r sr, src.mvalT σ = .ok r → dst.resolveT σ = .ok sr → σ.heap.len r .dyn < L := by
  intro r sr hr hd
  simp only [copyBoundStmt, hasArrayCopyStmt, arrayCopyTargetKind, arrayCopyKind, if_true, rawCopyBoundStmt, arrayCopyDemand, hr, hd] at h
  omega

theorem copyBoundStmt_fixedDynamic {Γ : Ctx} {p : PrimTy} {n : Nat}
    (dst : Loc C Γ (.ref (.array (.prim p)))) (src : MPath C Γ (.ref (.fixed (.prim p) n)))
    (hn : n < W) (σ : State C Γ) (L : Nat)
    (h : copyBoundStmt (.assign dst (.fixedCopyMem src (.dynamic hn))) σ ≤ L) :
    ∀ r sr, src.mvalT σ = .ok r → dst.resolveT σ = .ok sr → n < L := by
  intro r sr hr hd
  simp only [copyBoundStmt, hasArrayCopyStmt, sourceArrayKind, fixedDynamicKind, if_true,
    rawCopyBoundStmt, sourceCopyDemand, fixedDynamicDemand, hr, hd] at h
  omega

end Solidity.Evm.Memory
