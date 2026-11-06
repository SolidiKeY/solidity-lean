import Solidity.Yul.Composition.RuntimeBlockPhysical

/-! Actual Source unchecked and while constructors over the existing canonical
alias/rethrow leaves. Contextual construction respects intrinsic SCtx indices;
no evaluator, raw-local semantics, arithmetic choice or general coverage claim. -/
namespace Solidity.Yul.Composition.UncheckedLoopPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

/-- Same two resolved leaves at the context indices required by each constructor. -/
def items {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (index : Source.Idx Γ (.bytes .memory)) : Source.RItems E R M k Γ (.bytes .memory::Γ) :=
  .stmt (.declInit (.local index) rfl) (.stmt (.rethrow .here) .nil)

theorem existing_items {E : Source.Env} {Γ : Source.RCtx} (index : Source.Idx Γ (.bytes .memory)) :
    (items index : Source.RItems E [] false ⟨false,false⟩ _ _) = RuntimeBlockPhysical.aliasItems index := rfl

theorem declare {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.declInit (.local index) rfl : Source.RStmt E R M k Γ (.bytes .memory::Γ)) inside).run (.nil,state) =
      (.ok (.normal (.cons (inside.get index) inside)),(.nil,state)) := by
  rw [Source.execS]
  rfl

theorem rethrow {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (state : Source.St E) (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+1) nps ph (.rethrow index : Source.RStmt E R M k Γ Γ) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  rw [Source.execS,reference]
  change (do let data ← Source.heapBytes address; Source.EM.halt (.revert data) : Source.EM E [] _).run (.nil,state) = _
  rw [Source.Hoare.run_bind]
  have read : (Source.heapBytes address : Source.EM E [] _).run (.nil,state) = (.ok bytes,(.nil,state)) :=
    HeapCatchPhysical.bytesOf_ref_run F address bytes .nil state found
  rw [read]
  rfl

theorem items_run {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (state : Source.St E) (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+3) nps ph (items index : Source.RItems E R M k _ _) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  unfold items
  rw [Source.execItems,Source.Hoare.run_bind,declare]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,
    rethrow G F fuel nps address ph bytes .here _ state reference found]

def unchecked {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l}
    (index : Source.Idx Γ (.bytes .memory)) (rest : Source.RItems E R M ⟨l,false⟩ Γ Δ) :=
  Source.RItems.unchecked (items index) rest

/-- Arbitrary well-typed rest is unreachable on the actual full-byte revert.
The checked frame is changed only for the real inner evaluation. -/
theorem unchecked_run {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (rest : Source.RItems E R M ⟨l,false⟩ Γ Δ) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+4) nps ph (unchecked index rest) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  unfold unchecked
  rw [Source.execItems,Source.Hoare.run_bind,items_run G {F with checked:=false} fuel nps address ph bytes index inside state reference found]

def loop {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (flag : Bool) (index : Source.Idx Γ (.bytes .memory)) : Source.RStmt E R M ⟨l,u⟩ Γ Γ :=
  .whileLoop (.bool flag) (.block (items index))

/-- The condition is ACTUALLY evaluated; no supplied condition outcome. -/
theorem while_false {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph (loop (R:=R) (M:=M) (l:=l) (u:=u) false index) inside).run (.nil,state) =
      (.ok (.normal inside),(.nil,state)) := rfl

theorem while_true {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (state : Source.St E) (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+5) nps ph (loop (R:=R) (M:=M) (l:=l) (u:=u) true index) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  have condition : (Source.EM.sub inside (Source.evalE G F (fuel+4) (.bool true))).run (.nil,state) =
      (.ok (.val (.bool true),inside),(.nil,state)) := rfl
  have body : (Source.execS G F (fuel+4) nps ph
      (.block (items index) : Source.RStmt E R M ⟨true,u⟩ Γ Γ) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
    rw [Source.execS,Source.Hoare.run_bind,items_run G F fuel nps address ph bytes index inside state reference found]
  have got : (Source.getV (.val (.bool true)) : Source.EM E [] (Source.Val E.layout .bool)).run (.nil,state) =
      (.ok (.bool true),(.nil,state)) := rfl
  unfold loop
  rw [Source.execS,Source.Hoare.run_bind,condition]
  dsimp only
  rw [Source.Hoare.run_bind,got]
  dsimp only
  rw [Source.Hoare.run_bind,body]


theorem restore_cons {E : Source.Env} {Γ : Source.RCtx} (inside : Source.Locals E.layout Γ)
    (value : Source.Val E.layout (.bytes .memory)) :
    (Source.Locals.cons value inside).restore Γ = .ok inside := by
  have count : ((Source.STy.bytes .memory::Γ).length - Γ.length)=1 := by
    simp only [List.length_cons]
    omega
  unfold Source.Locals.restore
  rw [count]
  simp only [List.drop_succ_cons,List.drop_zero,dif_pos rfl]
  rfl

/-- On normal completion the actual unchecked constructor restores the old
local context and runs arbitrary rest under ORIGINAL F, not unchecked F. -/
theorem unchecked_decl_rest {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (rest : Source.RItems E R M ⟨l,false⟩ Γ Δ) (state : Source.St E) :
    (Source.execItems G F (fuel+4) nps ph
      (.unchecked (.stmt (.declInit (.local index) rfl : Source.RStmt E R M ⟨l,true⟩ Γ (.bytes .memory::Γ)) .nil) rest) inside).run (.nil,state) =
      (Source.execItems G F (fuel+3) nps ph rest inside).run (.nil,state) := by
  have inner : (Source.execItems G {F with checked:=false} (fuel+3) nps ph
      (.stmt (.declInit (.local index) rfl : Source.RStmt E R M ⟨l,true⟩ Γ (.bytes .memory::Γ)) .nil) inside).run (.nil,state) =
      (.ok (.normal (.cons (inside.get index) inside)),(.nil,state)) := by
    rw [Source.execItems,Source.Hoare.run_bind,declare]
    rfl
  have restored : (Source.EM.lift ((Source.Locals.cons (inside.get index) inside).restore Γ) :
      Source.EM E [] (Source.Locals E.layout Γ)).run (.nil,state) = (.ok inside,(.nil,state)) := by
    rw [restore_cons]
    rfl
  rw [Source.execItems,Source.Hoare.run_bind,inner]
  dsimp only
  rw [Source.Hoare.run_bind,restored]


theorem unchecked_low {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (rest : Source.RItems E R M ⟨l,false⟩ Γ Δ) (state : Source.St E) :
    ([0,1,2,3].map fun fuel => (Source.execItems G F fuel nps ph (unchecked index rest) inside).run (.nil,state)) =
      List.replicate 4 (.error .timeout,(Source.Locals.nil,state)) := rfl

theorem while_low {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    ([0,1,2,3,4].map fun fuel => (Source.execS G F fuel nps ph
      (loop (R:=R) (M:=M) (l:=l) (u:=u) true index) inside).run (.nil,state)) =
      List.replicate 5 (.error .timeout,(Source.Locals.nil,state)) := rfl

def execute {E : Source.Env} {Γ Δ Ξ : Source.RCtx} {R : List Source.STy} {M l}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (index : Source.Idx Δ (.bytes .memory))
    (inside : Source.Locals E.layout Δ) (rest : Source.RItems E R M ⟨l,false⟩ Δ Ξ) : Source.EM E Γ Unit := do
  let _ ← Source.EM.sub .nil (Source.execItems G F fuel 0 none (unchecked index rest) inside)
  pure ()

theorem execute_run {E : Source.Env} {Γ Δ Ξ : Source.RCtx} {R : List Source.STy} {M l}
    (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat) (bytes : List UInt8)
    (index : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ)
    (rest : Source.RItems E R M ⟨l,false⟩ Δ Ξ) (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (execute G F (fuel+4) index inside rest).run (outer,state) = (.error (.revert bytes),(outer,state)) := by
  unfold execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,unchecked_run G F fuel 0 address none bytes index inside rest state reference found]

/-- Companion to the actual evaluator/EM.sub/attempt execution. Journals are
retained boundary data; this does not implement a new world rollback operation. -/
def carry {E : Source.Env} {Γ Δ Ξ Λ : Source.RCtx} {R : List Source.STy} {M l}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (index : Source.Idx Δ (.bytes .memory))
    (inside : Source.Locals E.layout Δ) (rest : Source.RItems E R M ⟨l,false⟩ Δ Ξ)
    (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal) :=
  (AttemptPhysical.companion (execute G F fuel index inside rest) outer raw,residual,owned)

theorem carry_run {E : Source.Env} {Γ Δ Ξ Λ : Source.RCtx} {R : List Source.STy} {M l}
    (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat) (bytes : List UInt8)
    (index : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ)
    (rest : Source.RItems E R M ⟨l,false⟩ Δ Ξ) (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal)
    (reference : inside.get index=.memRef rfl address)
    (found : raw.2.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    carry G F (fuel+4) index inside rest outer raw residual owned =
      (((.ok (.error (.revert bytes)),(outer,raw.2)),raw),residual,owned) := by
  unfold carry
  rw [AttemptPhysical.companion_actual,execute_run G F fuel address bytes index inside rest outer raw.2 reference found]

/-- Same actual represented Source action/journals and existing completed raw
caller values; allocation only uses the real Heap.alloc post-state. -/
def sampleRaw (bytes : List UInt8) : LocalState originEnv ctx.tys :=
  (AttemptPhysical.input.1,RuntimeBlockPhysical.allocatedState firstPhysical.1.1.2.2 bytes)
def sampleInside (bytes : List UInt8) : Source.Locals originEnv.layout ScopeCatchPhysical.Inner :=
  .cons (.memRef rfl firstPhysical.1.1.2.2.heap.next) (.cons (.memRef rfl 0) .nil)
def poison : Source.RItems originEnv [] false ⟨false,false⟩ ScopeCatchPhysical.Inner ScopeCatchPhysical.Inner :=
  .stmt (.rethrow (.there .here)) .nil

def sample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :=
  carry G packedStepFrame fuel .here (sampleInside bytes) poison ScopeCatchPhysical.outer
    (sampleRaw bytes) firstPhysical.1.2 firstPhysical.2

theorem sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    sample G bytes (fuel+4) =
      (((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,(sampleRaw bytes).2)),sampleRaw bytes),
        firstPhysical.1.2,firstPhysical.2) := by
  apply carry_run G packedStepFrame fuel firstPhysical.1.1.2.2.heap.next bytes .here (sampleInside bytes)
    poison ScopeCatchPhysical.outer (sampleRaw bytes) firstPhysical.1.2 firstPhysical.2 rfl
  exact Source.Heap.alloc_get _ _

theorem sample_dead (G : Source.Glob originEnv) :
    (sample G [0xde,0xad] 4).1.1.1 = .ok (.error (.revert [0xde,0xad])) := by rw [sample_run G _ 0]

theorem sample_empty (G : Source.Glob originEnv) :
    (sample G [] 4).1.1.1 = .ok (.error (.revert [])) := by rw [sample_run G _ 0]

theorem sample_panic (G : Source.Glob originEnv) :
    (sample G (Source.panicData .assert) 4).1.1.1 = .ok (.error (.revert (Source.panicData .assert))) := by rw [sample_run G _ 0]

/-- Old alias0 has AABB, same length as DEAD. Complete byte inequality matters. -/
theorem sample_wrong_alias (G : Source.Glob originEnv) (fuel : Nat) :
    carry G packedStepFrame (fuel+4) (.there .here) (sampleInside [0xde,0xad]) poison ScopeCatchPhysical.outer
      (sampleRaw [0xde,0xad]) firstPhysical.1.2 firstPhysical.2 =
      (((.ok (.error (.revert [0xaa,0xbb])),(ScopeCatchPhysical.outer,(sampleRaw [0xde,0xad]).2)),sampleRaw [0xde,0xad]),
        firstPhysical.1.2,firstPhysical.2) := by
  apply carry_run G packedStepFrame fuel 0 [0xaa,0xbb] (.there .here) _ _ _ _ _ _ rfl
  rfl

theorem sample_raw (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+4)).1.2.1 = AttemptPhysical.input.1 := by rw [sample_run]; rfl

theorem sample_nonword (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+4)).1.2.1.get memoryRef.index = AttemptPhysical.input.1.get memoryRef.index := by rw [sample_raw]


theorem while_sample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (Source.execS G packedStepFrame (fuel+5) 0 none
      (loop (R:=[]) (M:=false) (l:=false) (u:=false) true .here) (sampleInside bytes)).run (.nil,(sampleRaw bytes).2) =
      (.error (.revert bytes),(.nil,(sampleRaw bytes).2)) := by
  apply while_true G packedStepFrame fuel 0 firstPhysical.1.1.2.2.heap.next none bytes .here _ _ rfl
  exact Source.Heap.alloc_get _ _

theorem while_break {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.whileLoop (.bool true) .brk : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.ok (.normal inside),(.nil,state)) := rfl

/-- The real continue branch consumes a horizon and re-enters the loop with the
same locals/state. This is not a supplied transition or a separate interpreter. -/
theorem while_continue_step {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.whileLoop (.bool true) .cont : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
    (Source.execS G F (fuel+1) nps ph
      (.whileLoop (.bool true) .cont : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) := rfl

theorem while_continue_timeout {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F fuel nps ph
      (.whileLoop (.bool true) .cont : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => rw [while_continue_step]; exact ih

end Solidity.Yul.Composition.UncheckedLoopPhysical
