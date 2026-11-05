import Solidity.Yul.Views.RepeatedCellWrites

/-! Finite different-path typed Source setters in one fixed frame. Requests
pair existing ScalarPath registrations with actual intrinsic values; they are
not a new source AST. Bank selection is actual declaration metadata. Registry
membership is physical-domain evidence, not a Source admission restriction. -/
namespace Solidity.Yul.Views.FiniteCellWrites

abbrev Request (E : Source.Env) (a : Roadmap.Address) :=
  (c : ScalarPath E.layout (E.lay a)) × Source.Val E.layout (E.cellTy c.path)

def Registered {E a} (ps ts : List (ScalarPath E.layout (E.lay a))) (request : Request E a) : Prop :=
  (E.transientRoot request.1.path=false → request.1 ∈ ps) ∧
  (E.transientRoot request.1.path=true → request.1 ∈ ts)

def program {E Γ} (F : Source.Fr) : List (Request E F.this) → Source.EM E Γ Unit
  | [] => pure ()
  | request::rest => do Source.setCell F request.1.path (some request.2); program F rest

def patch {E a} (request : Request E a) (maps : SlotView × SlotView) : SlotView × SlotView :=
  if E.transientRoot request.1.path then (maps.1,PackedCellUpdate.raw request.1 request.2 maps.2)
  else (PackedCellUpdate.raw request.1 request.2 maps.1,maps.2)

def raw {E a} (requests : List (Request E a)) (maps : SlotView × SlotView) := requests.foldl (fun maps request => patch request maps) maps

def Views {E Γ} (F : Source.Fr) (ps ts : List (ScalarPath E.layout (E.lay F.this)))
    (source : Source.EMState E Γ) (maps : SlotView × SlotView) : Prop :=
  finiteView ps (source.2.ex.world.accounts F.this).storage maps.1 ∧
  finiteView ts (source.2.ex.transient.cells F.this) maps.2

theorem step {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (request : Request E F.this) (registered : Registered ps ts request)
    (maps : SlotView × SlotView) (before : Views F ps ts s maps) (allowed : F.static=false) :
    Views F ps ts ((Source.setCell F request.1.path (some request.2)).run s).2 (patch request maps) := by
  first | (simp only;done) | skip
  cases bank : E.transientRoot request.1.path
  · simp only [Views,patch,bank,Bool.false_eq_true,if_false]
    refine ⟨PackedCellUpdate.source_view F s ps request.1 (registered.1 bank) psep maps.1 before.1 request.2 bank allowed,?_⟩
    rw [PackedCellUpdate.source F s request.1 request.2 bank allowed]
    exact before.2
  · simp only [Views,patch,bank,if_true]
    refine ⟨?_,TransientCellUpdate.view F s ts request.1 (registered.2 bank) tsep maps.2 before.2 request.2 bank allowed⟩
    rw [TransientCellUpdate.source F s request.1 request.2 bank allowed]
    exact before.1

theorem step_complement {E a} (ps ts : List (ScalarPath E.layout (E.lay a)))
    (request : Request E a) (registered : Registered ps ts request) (maps : SlotView × SlotView) :
    packedMask ps (patch request maps).1=packedMask ps maps.1 ∧
    packedMask ts (patch request maps).2=packedMask ts maps.2 := by
  first | (simp only;done) | skip
  cases bank : E.transientRoot request.1.path
  · simp only [patch,bank,Bool.false_eq_true,if_false]
    exact ⟨PackedCellUpdate.complement ps request.1 (registered.1 bank) request.2 maps.1,True.intro⟩
  · simp only [patch,bank,if_true]
    exact ⟨True.intro,PackedCellUpdate.complement ts request.1 (registered.2 bank) request.2 maps.2⟩

theorem complement {E a} (ps ts : List (ScalarPath E.layout (E.lay a))) (requests : List (Request E a))
    (registered : ∀ request ∈ requests, Registered ps ts request) (maps : SlotView × SlotView) :
    packedMask ps (raw requests maps).1=packedMask ps maps.1 ∧
    packedMask ts (raw requests maps).2=packedMask ts maps.2 := by
  first | (simp only;done) | skip
  induction requests generalizing maps with
  | nil => exact ⟨rfl,rfl⟩
  | cons request rest ih =>
    have next := ih (fun q member => registered q (List.mem_cons_of_mem _ member)) (patch request maps)
    have same := step_complement ps ts request (registered request List.mem_cons_self) maps
    exact ⟨next.1.trans same.1,next.2.trans same.2⟩

theorem view {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (requests : List (Request E F.this)) (registered : ∀ request ∈ requests, Registered ps ts request)
    (maps : SlotView × SlotView) (before : Views F ps ts s maps) (allowed : F.static=false) :
    Views F ps ts ((program F requests).run s).2 (raw requests maps) := by
  first | (simp only;done) | skip
  induction requests generalizing s maps with
  | nil => exact before
  | cons request rest ih =>
    have next := step F s ps ts psep tsep request (registered request List.mem_cons_self) maps before allowed
    rw [program,Source.Hoare.run_bind,RepeatedCellWrites.one F s request.1 request.2 allowed]
    dsimp only
    apply ih (s:=(s.1,{s.2 with ex:=s.2.ex.apply (RepeatedCellWrites.operation F request.1 request.2)}))
      (fun q member => registered q (List.mem_cons_of_mem _ member)) (patch request maps)
    simpa only [RepeatedCellWrites.one F s request.1 request.2 allowed] using next

theorem reencode {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (requests : List (Request E F.this)) (registered : ∀ request ∈ requests, Registered ps ts request)
    (maps : SlotView × SlotView) (before : Views F ps ts s maps) (allowed : F.static=false) :
    let reached := (program F requests).run s
    finiteEncode ps (reached.2.2.ex.world.accounts F.this).storage (packedMask ps maps.1)=some (raw requests maps).1 ∧
    finiteEncode ts (reached.2.2.ex.transient.cells F.this) (packedMask ts maps.2)=some (raw requests maps).2 := by
  first | (simp only;done) | skip
  have after := view F s ps ts psep tsep requests registered maps before allowed
  have masks := complement ps ts requests registered maps
  dsimp only
  rw [←masks.1,←masks.2]
  exact ⟨finiteEncode_fromComplement ps _ _ psep after.1,finiteEncode_fromComplement ts _ _ tsep after.2⟩

theorem run {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (requests : List (Request E F.this)) (allowed : F.static=false) :
    (program F requests).run s=(.ok (),(s.1,{s.2 with ex:=(s.2.ex.run (requests.map (fun request => RepeatedCellWrites.operation F request.1 request.2)))})) := by
  first | (simp only;done) | skip
  induction requests generalizing s with
  | nil => rfl
  | cons request rest ih =>
    rw [program,Source.Hoare.run_bind,RepeatedCellWrites.one F s request.1 request.2 allowed]
    dsimp only
    rw [ih]
    rfl

theorem preserves {E Γ} (F : Source.Fr) (requests : List (Request E F.this)) (H : Source.HeapTy) :
    Source.Hoare (Source.MemOK E H) (program (Γ:=Γ) F requests)
      (fun _ state => Source.MemOK E H state) (fun _ state => Source.MemOK E H state) := by
  induction requests with
  | nil => exact Source.Hoare.pure' (fun _ safe => safe)
  | cons request rest ih => exact Source.Hoare.bind (Source.setCell_mem F request.1.path (some request.2)) (fun _ => ih)
theorem MemOK {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (requests : List (Request E F.this)) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((program F requests).run s).2 := by
  first | (simp only;done) | skip
  have safe := preserves F requests H s ok
  rcases actual : (program F requests).run s with ⟨result,state⟩
  rw [actual] at safe
  cases result <;> exact safe

theorem static {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (request : Request E F.this) (rest : List (Request E F.this)) (blocked : F.static=true) :
    (program F (request::rest)).run s=(.error (.revert []),s) := by
  simp only [program,Source.Hoare.run_bind,Source.setCell]
  cases bank : E.transientRoot request.1.path <;>
    simp only [Bool.false_eq_true,if_false,if_true,Source.applyOp,blocked] <;> rfl

theorem rollback {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (requests : List (Request E F.this)) (residual : ResidualJournal complementCarrierOwnership)
    (allowed : F.static=false) :
    companionRollback (companionEnter (⟨s.2.ex,residual⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
      F.this F.sender F.value F.cd F.static)
      ⟨((program F requests).run s).2.2.ex,residual⟩=⟨s.2.ex,residual⟩ := by
  rw [run F s requests allowed]
  let ops : List (Source.Op E.layout E.lay E.lay) := requests.map
    (fun (request : Request E F.this) => @RepeatedCellWrites.operation E F request.1 request.2)
  change companionRollback (companionEnter (⟨s.2.ex,residual⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
    F.this F.sender F.value F.cd F.static) ⟨s.2.ex.run ops,residual⟩=⟨s.2.ex,residual⟩
  simpa only [companionRunResidual,companionRunSource,residualRun] using
    (@companionRollback_run E.layout E.lay E.lay complementCarrierOwnership ⟨s.2.ex,residual⟩ ops []
      F.this F.sender F.value F.cd F.static)
end Solidity.Yul.Views.FiniteCellWrites
