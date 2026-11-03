import Solidity.Lowering.V07.ContextMap

/-! P12 CAPTURE-REFERENCE: actual typed alias declarations retain pointer
identity. No snapshot-to-SVal substitution, copy/delete/lifetime validity or
Source graph admission is asserted. Source bytes clauses expose actual local
reads; initial pointer/content correspondence belongs to the caller relation. -/
namespace Solidity.Lowering.V07

def memoryCapture {C : Contract} {Γ : Ctx} {R : RefTy}
    (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) : Prog C Γ (.mem R :: Γ) :=
  .cons (.declMem R (.user "v07_reference") (some (.alias (.var i hm))) rfl hm) .nil

def storageCapture {C : Contract} {Γ : Ctx} {R : RefTy}
    (i : Idx Γ (.alias R)) : Prog C Γ (.alias R :: Γ) :=
  .cons (.declStorage R (.user "v07_reference") (some (.path (.alias i)))) .nil

theorem memory_capture_run {C : Contract} {Γ : Ctx} {R : RefTy}
    (target : State C Γ) (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (r : HRef target.H R) (read : TEnv.get i target.env = some r) :
    (memoryCapture i hm).run target =
      .ok (⟨target.push (t := .mem R) (some r),List.prefix_refl _⟩) := by
  have init : (MRhs.alias (.var i hm)).evalT target =
      .ok (⟨target,List.prefix_refl _,r⟩ : Grew C Γ target.H (HRef · R)) := by
    dsimp only [MRhs.evalT,MPath.mvalT]
    rw [read]
    rfl
  have step : (Stmt.declMem R (.user "v07_reference") (some (.alias (.var i hm))) rfl hm).run target =
      .ok (⟨target.push (t := .mem R) (some r),List.prefix_refl _⟩) := by
    change (do
      let g ← (MRhs.alias (.var i hm)).evalT target
      pure (⟨g.st.push (t := .mem R) (some g.val),g.ext⟩ : Out C target.H (.mem R :: Γ))) = _
    rw [init]
    rfl
  unfold memoryCapture
  rw [Prog.run_cons_ok step,Prog.run_nil]
  rfl

theorem storage_capture_run {C : Contract} {Γ : Ctx} {R : RefTy}
    (target : State C Γ) (i : Idx Γ (.alias R))
    (r : SRef C (.ref R)) (read : TEnv.get i target.env = some r) :
    (storageCapture i).run target =
      .ok (⟨target.push (t := .alias R) (some r),List.prefix_refl _⟩) := by
  have init : (ARhs.path (.alias i)).evalT target = .ok (target.storage,r) := by
    dsimp only [ARhs.evalT,SPath.resolveT]
    rw [read]
    rfl
  have step : (Stmt.declStorage R (.user "v07_reference") (some (.path (.alias i)))).run target =
      .ok (⟨target.push (t := .alias R) (some r),List.prefix_refl _⟩) := by
    change (do
      let (st,ref) ← (ARhs.path (.alias i)).evalT target
      pure (⟨(target.withStorage st).push (t := .alias R) (some ref),List.prefix_refl _⟩ :
        Out C target.H (.alias R :: Γ))) = _
    rw [init]
    rfl
  unfold storageCapture
  rw [Prog.run_cons_ok step,Prog.run_nil]
  rfl

theorem source_local_value_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i : Source.Idx Γ τ) (v : Source.Val E.layout τ) (read : source.1.get i = v) :
    (Source.evalE G F (fuel+1) (.local i)).run source = (.ok (.val v),source) := by
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [read]

theorem capture_memory_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (i : Source.Idx srcΓ (.bytes .memory)) (j : Idx Γ (.mem bytesR)) (address : Nat)
    (r : HRef target.H bytesR) (sourceRead : source.1.get i = .memRef rfl address)
    (targetRead : TEnv.get j target.env = some r) :
    (Source.evalE G F (fuel+1) (.local i)).run source =
      (.ok (.val (.memRef rfl address)),source) ∧
    (memoryCapture j rfl).run target =
      .ok (⟨target.push (t := .mem bytesR) (some r),List.prefix_refl _⟩) ∧
    (MPath.var .here rfl : MPath C (.mem bytesR :: Γ) (.ref bytesR)).mvalT
      (target.push (t := .mem bytesR) (some r)) = .ok r :=
  ⟨source_local_value_run G F fuel source i _ sourceRead,
    memory_capture_run target j rfl r targetRead,rfl⟩

theorem capture_storage_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (i : Source.Idx srcΓ (.bytes .storage)) (j : Idx Γ (.alias bytesR)) (path : Source.SPath)
    (r : SRef C (.ref bytesR)) (sourceRead : source.1.get i = .storRef rfl path)
    (targetRead : TEnv.get j target.env = some r) :
    (Source.evalE G F (fuel+1) (.local i)).run source =
      (.ok (.val (.storRef rfl path)),source) ∧
    (storageCapture j).run target =
      .ok (⟨target.push (t := .alias bytesR) (some r),List.prefix_refl _⟩) ∧
    (SPath.alias .here : SPath C (.alias bytesR :: Γ) (.ref bytesR)).resolveT
      (target.push (t := .alias bytesR) (some r)) = .ok r :=
  ⟨source_local_value_run G F fuel source i _ sourceRead,
    storage_capture_run target j r targetRead,rfl⟩

/-- A capture adds only an intrinsic temporary. All old aligned Source
bindings retain their positions and values; R says nothing about execution. -/
theorem memory_capture_context {D : Source.Layout} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {R : RefTy} (m : ContextMap srcΓ Γ) (target : State C Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C target.H → Prop)
    (source : Source.Locals D srcΓ) (aligned : m.Related Rel source target.env)
    (r : HRef target.H R) :
    (m.wk (Thin.drop (t := .mem R) .refl)).Related Rel source
      (target.push (t := .mem R) (some r)).env := by
  intro τ i
  exact aligned i

theorem storage_capture_context {D : Source.Layout} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {R : RefTy} (m : ContextMap srcΓ Γ) (target : State C Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C target.H → Prop)
    (source : Source.Locals D srcΓ) (aligned : m.Related Rel source target.env)
    (r : SRef C (.ref R)) :
    (m.wk (Thin.drop (t := .alias R) .refl)).Related Rel source
      (target.push (t := .alias R) (some r)).env := by
  intro τ i
  exact aligned i

theorem capture_fresh_position {srcΓ : Source.RCtx} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) {τ : Source.STy} (i : Source.Idx srcΓ τ) (u : LTy) :
    ((m.wk (Thin.drop (t := u) .refl)).slot i).2.toNat ≠ 0 := by
  change (m.slot i).2.toNat+1 ≠ 0
  omega

end Solidity.Lowering.V07
