import Solidity.Backend.Passes.Frame
import Solidity.Backend.Passes.EmittedTail

/-!
# Capture certificates with separated frames and typed context extension

All code comes from the published Memory StmtFrag capture constructors.
Input heap ownership, fragment, frame separation and allocator implications
are retained; no tuple or Source-reference lowering is supplied here.
-/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Memory

variable {C : Contract} {Γ : Ctx} {b L frame frame' : Nat} {F : Frag Γ}
  {σ : State C Γ} {base : Nat → Fin W} {m : Machine}

/-- Complete local capture transport at a separately reserved frame and arbitrary tail. -/
theorem capture_local_frame
    {p : PrimTy} (dst src : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (hrecv : (OpLoc.local (C := C) src).recvSimple = true)
    (value step : List Instr)
    (hv : ValFrag (C := C) b F (bumpResultValue op hp (.simple (.local src))) value)
    (hs : StmtFrag (C := C) b F F (.incDec op hp (.local src)) step)
    (h : StateRepr L b frame F σ base m)
    (capacity : b + Γ.length ≤ frame')
    (arrays : ∀ {q : PrimTy} (r : HRef σ.H (.array (.prim q))), frame' ≤ (base r.id).val)
    (structs : ∀ {s : Name} (r : HRef σ.H (.struct s)), frame' ≤ (base r.id).val)
    (tail : List Word) :
    GrowingResult L b frame' 0 F σ base {m with stack := tail}
      ((Stmt.assignIncDec dst op hp (.local src) hrecv).run σ)
      (run (value ++ step ++ [.mstore (cellOf b dst)]) {m with stack := tail}) := by
  have hc := StmtFrag.captureLocal (C := C) F dst op hp src hrecv value step hv hs
  have fit : b + frameNeedStmt (Stmt.assignIncDec dst op hp (.local src) hrecv) ≤ frame' := by
    change b + max Γ.length (max Γ.length 0) ≤ frame'
    simpa only [Nat.max_zero, Nat.max_self] using capacity
  exact hc.correct ((memory_frame h capacity arrays structs).stack tail) fit (.inl rfl)

/-- Complete memory capture transport at a separately reserved frame and arbitrary tail. -/
theorem capture_memory_frame
    {p : PrimTy} {R : RefTy} (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (a : ArrTy R (.prim p)) (src : MPath C Γ (.ref R)) (i : Simple C Γ .uint)
    (hrecv : (OpLoc.mindex a src i).recvSimple = true) (value step : List Instr)
    (hv : ValFrag (C := C) b F (bumpResultValue op hp (.readMem (.index a src (.simple i)))) value)
    (hs : StmtFrag (C := C) b F F (.incDec op hp (.mindex a src i)) step)
    (h : StateRepr L b frame F σ base m)
    (capacity : b + Γ.length ≤ frame')
    (arrays : ∀ {q : PrimTy} (r : HRef σ.H (.array (.prim q))), frame' ≤ (base r.id).val)
    (structs : ∀ {s : Name} (r : HRef σ.H (.struct s)), frame' ≤ (base r.id).val)
    (tail : List Word) :
    GrowingResult L b frame' 0 F σ base {m with stack := tail}
      ((Stmt.assignIncDec dst op hp (.mindex a src i) hrecv).run σ)
      (run (value ++ step ++ [.mstore (cellOf b dst)]) {m with stack := tail}) := by
  have hc := StmtFrag.captureMemory F dst op hp a src i hrecv value step hv hs
  have fit : b + frameNeedStmt (Stmt.assignIncDec dst op hp (.mindex a src i) hrecv) ≤ frame' := by
    change b + max Γ.length (max Γ.length 0) ≤ frame'
    simpa only [Nat.max_zero, Nat.max_self] using capacity
  exact hc.correct ((memory_frame h capacity arrays structs).stack tail) fit (.inl rfl)

/-- Complete field capture transport at a separately reserved frame and arbitrary tail. -/
theorem capture_field_frame
    {p : PrimTy} {s : Name} (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (src : MPath C Γ (.struct s)) (f : Name) (hf : C.fieldType s f = some (.prim p))
    (hrecv : (OpLoc.mfield src f hf).recvSimple = true) (value step : List Instr)
    (hv : ValFrag (C := C) b F (bumpResultValue op hp (.readMem (.field src f hf))) value)
    (hs : StmtFrag (C := C) b F F (.incDec op hp (.mfield src f hf)) step)
    (h : StateRepr L b frame F σ base m)
    (capacity : b + Γ.length ≤ frame')
    (arrays : ∀ {q : PrimTy} (r : HRef σ.H (.array (.prim q))), frame' ≤ (base r.id).val)
    (structs : ∀ {s : Name} (r : HRef σ.H (.struct s)), frame' ≤ (base r.id).val)
    (tail : List Word) :
    GrowingResult L b frame' 0 F σ base {m with stack := tail}
      ((Stmt.assignIncDec dst op hp (.mfield src f hf) hrecv).run σ)
      (run (value ++ step ++ [.mstore (cellOf b dst)]) {m with stack := tail}) := by
  have hc := StmtFrag.captureField F dst op hp src f hf hrecv value step hv hs
  have fit : b + frameNeedStmt (Stmt.assignIncDec dst op hp (.mfield src f hf) hrecv) ≤ frame' := by
    change b + max Γ.length (max Γ.length 0) ≤ frame'
    simpa only [Nat.max_zero, Nat.max_self] using capacity
  exact hc.correct ((memory_frame h capacity arrays structs).stack tail) fit (.inl rfl)

/-- A capture followed by a real typed memory-alias declaration. The
new reference local and every old alias share the full represented heap. -/
theorem capture_then_alias_frame
    {p : PrimTy} (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (loc : OpLoc C Γ p) (hrecv : loc.recvSimple = true) (code : List Instr)
    (capture : StmtFrag (C := C) b F F (.assignIncDec dst op hp loc hrecv) code)
    {R : RefTy} (name : Var) (src : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (h : StateRepr L b frame F σ base m)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {q : PrimTy} (r : HRef σ.H (.array (.prim q))), frame' ≤ (base r.id).val)
    (structs : ∀ {s : Name} (r : HRef σ.H (.struct s)), frame' ≤ (base r.id).val)
    (tail : List Word) :
    GrowingResult L b frame' 0 (F.push (.mem R) .ok) σ base {m with stack := tail}
      ((Prog.cons (.assignIncDec dst op hp loc hrecv)
        (.cons (.declMem R name (some (.alias (.var src hm))) rfl hm) .nil)).run σ)
      (run (code ++ (declareAliasCode b src ++ [])) {m with stack := tail}) := by
  let P := Prog.cons (.assignIncDec dst op hp loc hrecv)
    (.cons (.declMem R name (some (.alias (.var src hm))) rfl hm) .nil)
  have cert : ProgFrag b F (F.push (.mem R) .ok) P
      (code ++ (declareAliasCode b src ++ [])) :=
    .cons capture (.cons (.declareAlias F name src hm) (.nil _))
  have fit : b + frameNeedProg P ≤ frame' := by
    change b + max (max Γ.length (max Γ.length 0))
      (max (max Γ.length (max (Γ.length + 1) 0)) (Γ.length + 1)) ≤ frame'
    omega
  have cost : allocationCostProg P σ = 0 := allocationCostProg_zero P rfl σ
  simpa only [ProgFrag.cost, cost] using
    cert.correct ((memory_frame h (by omega) arrays structs).stack tail) fit (.inl cost)

/-- A capture followed by a fresh primitive local whose expression is
evaluated after the capture effect, with its original ValFrag certificate. -/
theorem capture_then_value_frame
    {p : PrimTy} (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (loc : OpLoc C Γ p) (hrecv : loc.recvSimple = true) (code : List Instr)
    (capture : StmtFrag (C := C) b F F (.assignIncDec dst op hp loc hrecv) code)
    {q : PrimTy} (name : Var) (value : Val C Γ q) (valueCode : List Instr)
    (hv : ValFrag (C := C) b F value valueCode)
    (h : StateRepr L b frame F σ base m)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {r : PrimTy} (ref : HRef σ.H (.array (.prim r))), frame' ≤ (base ref.id).val)
    (structs : ∀ {s : Name} (ref : HRef σ.H (.struct s)), frame' ≤ (base ref.id).val)
    (tail : List Word) :
    GrowingResult L b frame' 0 (F.push (.val q) .ok) σ base {m with stack := tail}
      ((Prog.cons (.assignIncDec dst op hp loc hrecv)
        (.cons (.declLocal q name (some value)) .nil)).run σ)
      (run (code ++ ((valueCode ++ [.mstore (cell (b + Γ.length))]) ++ []))
        {m with stack := tail}) := by
  let P := Prog.cons (.assignIncDec dst op hp loc hrecv)
    (.cons (.declLocal q name (some value)) .nil)
  have cert : ProgFrag b F (F.push (.val q) .ok) P
      (code ++ ((valueCode ++ [.mstore (cell (b + Γ.length))]) ++ [])) :=
    .cons capture (.cons (.declare F name value valueCode hv) (.nil _))
  have fit : b + frameNeedProg P ≤ frame' := by
    change b + max (max Γ.length (max Γ.length 0))
      (max (max Γ.length (max (Γ.length + 1) 0)) (Γ.length + 1)) ≤ frame'
    omega
  have cost : allocationCostProg P σ = 0 := allocationCostProg_zero P rfl σ
  simpa only [ProgFrag.cost, cost] using
    cert.correct ((memory_frame h (by omega) arrays structs).stack tail) fit (.inl cost)

end Solidity.Backend.Passes
