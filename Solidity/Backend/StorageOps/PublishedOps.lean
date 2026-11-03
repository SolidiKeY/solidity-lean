import Solidity.Evm.Stmt

/-! Checked operation adapters over the published ordinary intrinsic compiler.
These do not extend its fragment or relate recursive graph values to its store.
The returned code is the existing compiler's code, certified against independent
TRun semantics using the published Sim relation. -/

namespace Solidity.Backend.StorageOps.Published

open Solidity Evm

private def checked (allowed : Bool) (code : List Instr) : Option (List Instr) :=
  if allowed then some code else none

private theorem checked_some {allowed : Bool} {code result : List Instr}
    (accepted : checked allowed code = some result) : allowed = true ∧ code = result := by
  unfold checked at accepted
  split at accepted
  · exact ⟨by assumption, Option.some.inj accepted⟩
  · cases accepted

def read {C : Contract} {Γ : Ctx} {p : PrimTy} (b : Nat) (F : Frag Γ)
    (l : Solidity.Loc C Γ (.prim p)) : Option (List Instr) :=
  checked (valIn F (.read l)) (compileVal b (.read l))

def write {C : Contract} {Γ : Ctx} {p : PrimTy} (b : Nat) (F : Frag Γ)
    (l : Solidity.Loc C Γ (.prim p)) (v : Solidity.Val C Γ p) : Option (List Instr) :=
  checked (locIn F false l && valIn F v)
    (compileVal b v ++ compileLoc b l ++ [.sstore])

def copy {C : Contract} {Γ : Ctx} {R : RefTy} (b : Nat) (F : Frag Γ)
    (l : Solidity.Loc C Γ (.ref R)) (q : Solidity.SPath C Γ (.ref R)) : Option (List Instr) :=
  checked (static (.ref R) && leavesFit (.ref R) && spathIn F false q && locIn F false l)
    (compileSPath b q ++ loadLeaves (leaves (.ref R)) ++ [.pop] ++ compileLoc b l ++
      storeLeaves (leaves (.ref R)).reverse ++ [.pop])

def push {C : Contract} {Γ : Ctx} {E : Ty} (b : Nat) (F : Frag Γ)
    (q : Solidity.SPath C Γ (.array E)) (v : Option (Solidity.Src C Γ E)) : Option (List Instr) :=
  checked (pushIn F v q) (pushCode b v q)

def pop {C : Contract} {Γ : Ctx} {E : Ty} (b : Nat) (F : Frag Γ)
    (q : Solidity.SPath C Γ (.array E)) : Option (List Instr) :=
  checked (spathIn F false q) (compileSPath b q ++ popCode)

def delete {C : Contract} {Γ : Ctx} {T : Ty} (b : Nat) (F : Frag Γ)
    (l : Solidity.Loc C Γ T) : Option (List Instr) :=
  checked (leavesFit T && locIn F false l) (compileLoc b l ++ zeroCode (leaves T) ++ [.pop])

/-- Alias compilation returns the actual resulting Frag as well as code. -/
def rebind {C : Contract} {Γ : Ctx} {R : RefTy} (b : Nat) (F : Frag Γ)
    (i : Idx Γ (.alias R)) (q : Solidity.SPath C Γ (.ref R)) :
    Option (Frag Γ × List Instr) :=
  ((bindFl F q).map (F.set i)).map fun next =>
    (next, compileSPath b q ++ [.mstore (cellOf b i)])

variable {C : Contract} {Γ : Ctx} {L b : Nat} {F : Frag Γ}
  {σ : State C Γ} {m : Machine} {code : List Instr}

theorem read_sound {p : PrimTy} (l : Solidity.Loc C Γ (.prim p))
    (accepted : read b F l = some code) (hm : Sim C L b F σ m) :
    ValOutT p ((Solidity.Val.read l).evalT σ) (run code m) m := by
  obtain ⟨allowed, rfl⟩ := checked_some accepted
  exact val_sim (.read l) hm allowed

theorem write_sound {p : PrimTy} (l : Solidity.Loc C Γ (.prim p))
    (v : Solidity.Val C Γ p) (accepted : write b F l v = some code)
    (hm : Sim C L b F σ m) :
    StmtOut C L b F false false false (TRun.assign l (.val v) σ) (run code m) m := by
  obtain ⟨allowed, rfl⟩ := checked_some accepted
  obtain ⟨hl, hv⟩ := Bool.and_eq_true_iff.mp allowed
  exact assign_sim l v hm hl hv

theorem copy_sound {R : RefTy} (l : Solidity.Loc C Γ (.ref R))
    (q : Solidity.SPath C Γ (.ref R)) (mapFree : (Ty.ref R).mapFree = true)
    (accepted : copy b F l q = some code) (hm : Sim C L b F σ m) :
    StmtOut C L b F false false false (TRun.assign l (.copy q mapFree) σ) (run code m) m := by
  obtain ⟨allowed, rfl⟩ := checked_some accepted
  obtain ⟨hsf, hl⟩ := Bool.and_eq_true_iff.mp allowed
  obtain ⟨hs, hq⟩ := Bool.and_eq_true_iff.mp hsf
  obtain ⟨hst, hfit⟩ := Bool.and_eq_true_iff.mp hs
  exact copy_sim l q mapFree hst hfit hm hq hl

theorem push_sound {E : Ty} (q : Solidity.SPath C Γ (.array E))
    (v : Option (Solidity.Src C Γ E)) (accepted : push b F q v = some code)
    (hm : Sim C L b F σ m) (room : L + 1 ≤ Lmax) :
    StmtOut C (L + 1) b F false false false (TRun.push q v σ) (run code m) m := by
  obtain ⟨allowed, rfl⟩ := checked_some accepted
  exact push_sim q v hm allowed room

theorem pop_sound {E : Ty} (q : Solidity.SPath C Γ (.array E))
    (accepted : pop b F q = some code) (hm : Sim C L b F σ m) :
    StmtOut C L b F.dropFragile true false false (TRun.pop q σ) (run code m) m := by
  obtain ⟨allowed, rfl⟩ := checked_some accepted
  exact pop_sim q hm allowed

theorem delete_sound {T : Ty} (l : Solidity.Loc C Γ T)
    (accepted : delete b F l = some code) (hm : Sim C L b F σ m) :
    StmtOut C L b F.dropFragile true false false (TRun.delete l σ) (run code m) m := by
  obtain ⟨allowed, rfl⟩ := checked_some accepted
  obtain ⟨hf, hl⟩ := Bool.and_eq_true_iff.mp allowed
  exact delete_sim l hm hf hl

theorem rebind_sound {R : RefTy} (i : Idx Γ (.alias R))
    (q : Solidity.SPath C Γ (.ref R)) (next : Frag Γ)
    (accepted : rebind b F i q = some (next, code)) (hm : Sim C L b F σ m) :
    StmtOut C L b next false false false (TRun.rebind i (.path q) σ) (run code m) m := by
  unfold rebind at accepted
  cases bound : (bindFl F q).map (F.set i) with
  | none => simp only [bound, Option.map_none] at accepted; cases accepted
  | some actual =>
    simp only [bound, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact rebind_sim i q hm bound

/-- Concrete published gap: no dynamic array copy certificate is returned,
regardless of source/destination validity. No refusal/profile is weakened. -/
theorem dynamic_copy_rejected {E : Ty}
    (l : Solidity.Loc C Γ (.array E)) (q : Solidity.SPath C Γ (.array E)) :
    copy b F l q = none := rfl

/-- Existing aggregate default-push gap is preserved rather than assuming an
unpublished representation bridge. -/
theorem aggregate_push_rejected {R : RefTy}
    (q : Solidity.SPath C Γ (.array (.ref R))) : push b F q none = none := rfl

end Solidity.Backend.StorageOps.Published
