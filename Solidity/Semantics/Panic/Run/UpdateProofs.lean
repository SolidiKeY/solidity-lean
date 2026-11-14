import Solidity.Semantics.Panic.Run.Updates

namespace Solidity.Semantics.Panic.Run

variable {C : Contract} {Γ : Ctx}

/-- Every RHS halt, including resource failure, precedes target evaluation. -/
theorem assign_rhs_error {T : Ty} (l : Loc C Γ T) (r : Src C Γ T)
    (σ : State C Γ) (halt : Halt Raised) (h : source σ r = .error halt) :
    assign l r σ = .error halt := by
  simp only [assign, h]
  rfl

theorem opAssign_rhs_error {p : PrimTy} (op : BinOp) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (r : Val C Γ p) (σ : State C Γ) (halt : Halt Raised)
    (h : value σ r = .error halt) : opAssign op hp l r σ = .error halt := by
  simp only [opAssign, h]
  rfl

theorem assignMem_rhs_error {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T)
    (σ : State C Γ) (halt : Halt Raised) (h : msource σ r = .error halt) :
    assignMem l r σ = .error halt := by
  simp only [assignMem, h]
  rfl

/-- Exhaustion stays a resource failure and is not replaced by arithmetic panic. -/
theorem pushOpAssign_exhausted {p : PrimTy} (op : BinOp) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (rhs : Val C Γ p) (σ : State C Γ)
    (v : p.Denote) (ref : SRef C (.ref (.array (.prim p))))
    (hv : value σ rhs = .ok v) (hr : path σ b = .ok ref)
    (full : σ.storage.full ref = true) : pushOpAssign op hp b rhs σ = .error .exhausted := by
  simp only [pushOpAssign, hv, hr]
  change (if σ.storage.full ref then _ else _) = _
  simp only [full, if_true]

/-- Pop retains the witness from the actual storage object it evaluated. -/
theorem pop_origin {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) (hr : path σ b = .ok ref)
    (origin : Solidity.Panic.Origin (.pop σ.storage E.isMapping ref) .emptyPop) :
    pop b σ = .error (.intrinsic .popEmpty
      (Raised.ofOrigin (.pop σ.storage E.isMapping ref) .emptyPop origin)) := by
  simp only [pop, hr]
  change (evalProducer (.pop σ.storage E.isMapping ref) >>= _) = _
  rw [evalProducer_origin _ _ origin]
  rfl

/-- Memory read failures cannot be lost in an attempted write-back. -/
theorem opMem_read_error {p : PrimTy} (σ : State C Γ) (op : BinOp)
    (hp : p.isNumeric = true) (a : MAddr σ.H (.prim p)) (v : p.Denote)
    (halt : Halt Raised) (h : memoryRead σ.heap a = .error halt) :
    opMem σ op hp a v = .error halt := by
  simp only [opMem, h]
  rfl

theorem bumpMem_read_error {p : PrimTy} (σ : State C Γ) (op : IncDec)
    (hp : p.isNumeric = true) (a : MAddr σ.H (.prim p))
    (halt : Halt Raised) (h : memoryRead σ.heap a = .error halt) :
    bumpMem σ op hp a = .error halt := by
  simp only [bumpMem, h]
  rfl

/-- A write-only indexed destination raises the actual heap's bounds origin. -/
theorem memoryWrite_index_origin {H : HTy} {R : RefTy} {T : Ty} (hp : Heap H)
    (ref : HRef H R) (array : ArrTy R T) (i : PrimTy.uint.Denote) (v : MVal H T)
    (origin : Solidity.Panic.Origin (.index hp ref array i) .bounds) :
    memoryWrite hp (.index ref array i) v = .error (.intrinsic .index
      (Raised.ofOrigin (.index hp ref array i) .bounds origin)) := by
  simp only [memoryWrite, memoryRead, evalProducer_origin _ _ origin]
  rfl

/-- Plain assignment propagates destination failures after its RHS succeeds. -/
theorem assignMem_target_error {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T)
    (σ : State C Γ) (v : MVal σ.H T) (a : MAddr σ.H T) (halt : Halt Raised)
    (hv : msource σ r = .ok v) (ha : mloc σ l = .ok a)
    (failed : memoryRead σ.heap a = .error halt) : assignMem l r σ = .error halt := by
  simp only [assignMem, hv, ha]
  change (memoryWrite σ.heap a v >>= _) = _
  simp only [memoryWrite, failed]
  rfl

/-- Deleting a primitive memory element checks its destination bounds. -/
theorem clear_prim_error {p : PrimTy} (σ : State C Γ) (a : MAddr σ.H (.prim p))
    (halt : Halt Raised) (failed : memoryRead σ.heap a = .error halt) :
    clear σ a rfl = .error halt := by
  simp only [clear, memoryWrite, failed]
  rfl

/-- Reference deletion checks the weakened destination after allocating its default. -/
theorem clear_ref_error {R : RefTy} (σ : State C Γ) (a : MAddr σ.H (.ref R))
    (hm : (Ty.ref R).mapFree = true) (halt : Halt Raised)
    (failed : let g := σ.allocDefaultG R hm
      memoryRead g.st.heap (a.wk g.ext) = .error halt) : clear σ a hm = .error halt := by
  simp only [clear, memoryWrite, failed]
  rfl

/-- New-array assignment validates its destination in the allocated heap. -/
theorem assignNew_mem_error {R : RefTy} (l : MLoc C Γ (.ref R))
    (n : Simple C Γ .uint) (h : R.newArrOk = true) (σ : State C Γ)
    (halt : Halt Raised)
    (failed : let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
      ∀ a, mloc g.st l = .ok a → memoryRead g.st.heap a = .error halt)
    (found : let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
      ∃ a, mloc g.st l = .ok a) : assignNew (.mem l) n h σ = .error halt := by
  obtain ⟨a, ha⟩ := found
  simp only [assignNew, ha]
  change (memoryWrite _ a _ >>= _) = _
  simp only [memoryWrite, failed a ha]
  rfl

end Solidity.Semantics.Panic.Run
