import Solidity.Correctness.Panic.Provenance.Control
import Solidity.Semantics.Panic.Run.Updates

/-!
# Panic code provenance: the update leaves

Every update helper of `Semantics/Panic/Run/Checked.lean` and
`Semantics/Panic/Run/Updates.lean`, and every update step, fails only with a
coded halt: its intrinsic halts come from the evaluator leaves or from
`evalProducer` (checked compound arithmetic, increment and decrement, `pop`).
A step is coded in the sense of `Provenance/Control.lean` (`StepCoded`).
-/

namespace Solidity.Correctness.Panic

open Solidity.Semantics.Panic

open ErrCoded

/-- A full array halts with `exhausted`, which carries no code. -/
theorem full_coded {α : Type} (c : Prop) [Decidable c] {r : EvalResult α}
    (hr : ErrCoded r) : ErrCoded (if c then .error .exhausted else r) := by
  split
  · exact error _ fun _ _ e => nomatch e
  · exact hr

theorem compound_coded (op : BinOp) (p : PrimTy) (hp : p.isNumeric = true)
    (x y : p.Denote) : ErrCoded (compound op p hp x y) := by
  unfold compound
  split <;> first | exact evalProducer _ | exact ErrCoded.ofOpt _

theorem bump_coded (op : IncDec) (p : PrimTy) (hp : p.isNumeric = true)
    (x : p.Denote) : ErrCoded (bump op p hp x) := by
  unfold bump
  split <;> exact evalProducer _

theorem memoryWrite_coded {H : HTy} (hp : Heap H) {T : Ty} (a : MAddr H T)
    (v : MVal H T) : ErrCoded (memoryWrite hp a v) :=
  bind (memoryRead_coded hp a) fun _ => ofOpt _

variable {C : Contract} {Γ : Ctx}

theorem arhs_coded (σ : State C Γ) {R : RefTy} (r : ARhs C Γ R) :
    ErrCoded (arhs σ r) := by
  cases r with
  | path p => exact bind (path_coded σ p) fun _ => ok _
  | push b _ =>
    exact bind (path_coded σ b) fun _ => full_coded _ (bind (ofOpt _) fun _ => ok _)

theorem mrhs_coded (σ : State C Γ) {R : RefTy} (r : MRhs C Γ R) :
    ErrCoded (mrhs σ r) := by
  cases r with
  | alias p => exact bind (mpath_coded σ p) fun _ => ok _
  | copy p _ => exact bind (path_coded σ p) fun _ => bind (ofOpt _) fun _ => ok _
  | newArr => exact ok _

theorem opStore_coded (σ : State C Γ) (op : BinOp) {p : PrimTy} (hp : p.isNumeric = true)
    (r : SRef C (.prim p)) (v : p.Denote) : ErrCoded (opStore σ op hp r v) :=
  bind (ofOpt _) fun _ => bind (compound_coded _ _ _ _ _) fun _ =>
    bind (ofOpt _) fun _ => ok _

theorem opMem_coded (σ : State C Γ) (op : BinOp) {p : PrimTy} (hp : p.isNumeric = true)
    (a : MAddr σ.H (.prim p)) (v : p.Denote) : ErrCoded (opMem σ op hp a v) :=
  bind (memoryRead_coded _ _) fun _ => bind (compound_coded _ _ _ _ _) fun _ =>
    bind (ofOpt _) fun _ => ok _

theorem opLocStore_coded (σ : State C Γ) (op : BinOp) {p : PrimTy} (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (v : p.Denote) : ErrCoded (opLocStore σ op hp l v) := by
  cases l with
  | «local» => exact bind (compound_coded _ _ _ _ _) fun _ => ok _
  | root => exact opStore_coded _ _ _ _ _
  | field => exact bind (loc_coded σ _) fun _ => opStore_coded _ _ _ _ _
  | index => exact bind (loc_coded σ _) fun _ => opStore_coded _ _ _ _ _
  | mfield => exact bind (mloc_coded σ _) fun _ => opMem_coded _ _ _ _ _
  | mindex => exact bind (mloc_coded σ _) fun _ => opMem_coded _ _ _ _ _

theorem bumpStore_coded (σ : State C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (r : SRef C (.prim p)) : ErrCoded (bumpStore σ op hp r) :=
  bind (ofOpt _) fun _ => bind (bump_coded _ _ _ _) fun _ =>
    bind (ofOpt _) fun _ => ok _

theorem bumpMem_coded (σ : State C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (a : MAddr σ.H (.prim p)) : ErrCoded (bumpMem σ op hp a) :=
  bind (memoryRead_coded _ _) fun _ => bind (bump_coded _ _ _ _) fun _ =>
    bind (ofOpt _) fun _ => ok _

theorem opLocBump_coded (σ : State C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) : ErrCoded (opLocBump σ op hp l) := by
  cases l with
  | «local» => exact bind (bump_coded _ _ _ _) fun _ => ok _
  | root => exact bumpStore_coded _ _ _ _
  | field => exact bind (loc_coded σ _) fun _ => bumpStore_coded _ _ _ _
  | index => exact bind (loc_coded σ _) fun _ => bumpStore_coded _ _ _ _
  | mfield => exact bind (mloc_coded σ _) fun _ => bumpMem_coded _ _ _ _
  | mindex => exact bind (mloc_coded σ _) fun _ => bumpMem_coded _ _ _ _

namespace Run

theorem clear_coded (σ : State C Γ) {T : Ty} (a : MAddr σ.H T) (hm : T.mapFree = true) :
    ErrCoded (Run.clear σ a hm) := by
  cases T with
  | prim => exact bind (memoryWrite_coded _ _ _) fun _ => ok _
  | ref => exact bind (memoryWrite_coded _ _ _) fun _ => ok _

theorem assign_coded {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : StepCoded (Run.assign l r) :=
  fun σ => bind (source_coded σ r) fun _ => bind (loc_coded σ l) fun _ =>
    bind (ofOpt _) fun _ => ok _

theorem rebind_coded {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    StepCoded (Run.rebind i r) :=
  fun σ => bind (arhs_coded σ r) fun _ => ok _

theorem assignLocal_coded {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    StepCoded (Run.assignLocal i r) :=
  fun σ => bind (value_coded σ r) fun _ => ok _

theorem declLocal_coded (p : PrimTy) (init : Option (Val C Γ p)) :
    StepCoded (Run.declLocal p init) := fun σ => by
  cases init with
  | none => exact ok _
  | some e => exact bind (value_coded σ e) fun _ => ok _

theorem declStorage_coded (R : RefTy) (init : Option (ARhs C Γ R)) :
    StepCoded (Run.declStorage R init) := fun σ => by
  cases init with
  | none => exact ok _
  | some r => exact bind (arhs_coded σ r) fun _ => ok _

theorem opAssign_coded {p : PrimTy} (op : BinOp) (hp : p.isNumeric = true) (l : OpLoc C Γ p)
    (r : Val C Γ p) : StepCoded (Run.opAssign op hp l r) :=
  fun σ => bind (value_coded σ r) fun _ => opLocStore_coded _ _ _ _ _

theorem incDec_coded {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    StepCoded (Run.incDec op hp l) :=
  fun _ => bind (opLocBump_coded _ _ _ _) fun _ => ok _

theorem assignIncDec_coded {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) : StepCoded (Run.assignIncDec i op hp l) :=
  fun _ => bind (opLocBump_coded _ _ _ _) fun _ => ok _

theorem push_coded {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    StepCoded (Run.push b v) := fun σ => by
  refine ErrCoded.bind (path_coded σ b) fun _ => ?_
  cases v with
  | none => exact full_coded _ (ErrCoded.bind (ErrCoded.ofOpt _) fun _ => ok _)
  | some r => exact ErrCoded.bind (source_coded σ r) fun _ =>
      full_coded _ (ErrCoded.bind (ErrCoded.ofOpt _) fun _ => ok _)

theorem assignLocalPush_coded {p : PrimTy} (i : Idx Γ (.val p)) (b : SPath C Γ (.array (.prim p))) :
    StepCoded (Run.assignLocalPush i b) :=
  fun σ => bind (push_coded b none σ) fun _ => ok _

theorem pushOpAssign_coded {p : PrimTy} (op : BinOp) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (rhs : Val C Γ p) :
    StepCoded (Run.pushOpAssign op hp b rhs) :=
  fun σ => bind (value_coded σ rhs) fun _ => bind (path_coded σ b) fun _ =>
    full_coded _ (bind (ofOpt _) fun _ => opStore_coded _ _ _ _ _)

theorem pushIncDec_coded {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) : StepCoded (Run.pushIncDec op hp b) :=
  fun σ => bind (path_coded σ b) fun _ =>
    full_coded _ (bind (ofOpt _) fun _ => bind (bumpStore_coded _ _ _ _) fun _ => ok _)

theorem pop_coded {E : Ty} (b : SPath C Γ (.array E)) : StepCoded (Run.pop b) :=
  fun σ => bind (path_coded σ b) fun _ => bind (evalProducer _) fun _ => ok _

theorem transfer_coded (r a : Val C Γ .uint) : StepCoded (Run.transfer r a) :=
  fun σ => bind (value_coded σ r) fun _ => bind (value_coded σ a) fun _ => by
    split
    · exact ok _
    · exact revert

theorem send_coded (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) : StepCoded (Run.send pv r a) :=
  fun σ => bind (value_coded σ r) fun _ => bind (value_coded σ a) fun _ => ok _

theorem declMem_coded (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true) :
    StepCoded (Run.declMem R init hm) := fun σ => by
  cases init with
  | none => exact ok _
  | some r => exact bind (mrhs_coded σ r) fun _ => ok _

theorem rebindMem_coded {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    StepCoded (Run.rebindMem i r) :=
  fun σ => bind (mrhs_coded σ r) fun _ => ok _

theorem assignFromMem_coded {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    StepCoded (Run.assignFromMem l p) :=
  fun σ => bind (mpath_coded σ p) fun _ => bind (loc_coded σ l) fun _ =>
    bind (ofOpt _) fun _ => ok _

theorem assignMem_coded {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : StepCoded (Run.assignMem l r) :=
  fun σ => bind (msource_coded σ r) fun _ => bind (mloc_coded σ l) fun _ =>
    bind (memoryWrite_coded _ _ _) fun _ => ok _

theorem delete_coded {T : Ty} (l : Loc C Γ T) : StepCoded (Run.delete l) :=
  fun σ => bind (loc_coded σ l) fun _ => bind (ofOpt _) fun _ => ok _

theorem deleteMem_coded {T : Ty} (p : MPath C Γ T) : StepCoded (Run.deleteMem p) := fun σ => by
  cases p with
  | var => exact ok _
  | loc l => exact bind (mloc_coded σ l) fun _ => clear_coded _ _ _

theorem assignNew_coded {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    StepCoded (Run.assignNew l n h) := fun σ => by
  cases l with
  | store l => exact bind (loc_coded _ l) fun _ => bind (ofOpt _) fun _ => ok _
  | mem l => exact bind (mloc_coded _ l) fun _ => bind (memoryWrite_coded _ _ _) fun _ => ok _

end Run

end Solidity.Correctness.Panic
