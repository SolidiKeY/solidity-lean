import Solidity.Yul.Composition.ForPhysical

/-! Actual typed Source doWhile execution. Selected constructor laws and raw
companion transport, not general assembly/source/compiler adequacy. -/
namespace Solidity.Yul.Composition.DoWhilePhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

def body {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (index : Source.Idx Γ (.bytes .memory)) : Source.RStmt E R M ⟨true,u⟩ Γ Γ :=
  .block (UncheckedLoopPhysical.items index)

def loop {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (index : Source.Idx Γ (.bytes .memory)) (condition : Source.RExpr E Γ .bool) :
    Source.RStmt E R M ⟨l,u⟩ Γ Γ := .doWhile (body index) condition

theorem body_run {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (state : Source.St E) (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+4) nps ph (body (R:=R) (M:=M) (u:=u) index) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  unfold body
  rw [Source.execS,Source.Hoare.run_bind,
    UncheckedLoopPhysical.items_run G F fuel nps address ph bytes index inside state reference found]

/-- Arbitrary actual condition is unreachable on body revert, even a poison read. -/
theorem rethrow_run {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (condition : Source.RExpr E Γ .bool) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+5) nps ph (loop (R:=R) (M:=M) (l:=l) (u:=u) index condition) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  unfold loop
  rw [Source.execS,Source.Hoare.run_bind,body_run G F fuel nps address ph bytes index inside state reference found]

theorem break_run {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (condition : Source.RExpr E Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.doWhile .brk condition : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.ok (.normal inside),(.nil,state)) := rfl

theorem return_run {E : Source.Env} {Γ : Source.RCtx} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (condition : Source.RExpr E Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.doWhile (.ret rfl) condition : Source.RStmt E [] M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.ok (.ret inside),(.nil,state)) := rfl

theorem continue_false {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.doWhile .cont (.bool false) : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.ok (.normal inside),(.nil,state)) := rfl

/-- Continue reaches the actual assignment condition; old clean typed flag changes.
The independent dirty raw companion is never used as a clean Source local. -/
theorem continue_assign {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (flag : Source.Idx Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+3) nps ph
      (.doWhile .cont (.assign (.local flag) (.bool false)) : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.ok (.normal (inside.set flag (.bool false))),(.nil,state)) := rfl

/-- A real declaration extends the body's scope; doWhile restores it BEFORE
reading the original flag, so the fresh true is removed before the old flag is assigned. -/
theorem normal_restore {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (flag : Source.Idx Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+3) nps ph
      (.doWhile (.declInit (.bool true) rfl : Source.RStmt E R M ⟨true,u⟩ Γ (.bool::Γ)) (.assign (.local flag) (.bool false)) :
        Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.ok (.normal (inside.set flag (.bool false))),(.nil,state)) := by
  have declared : (Source.execS G F (fuel+2) nps ph
      (.declInit (.bool true) rfl : Source.RStmt E R M ⟨true,u⟩ Γ (.bool::Γ)) inside).run (.nil,state) =
      (.ok (.normal (.cons (.bool true) inside)),(.nil,state)) := rfl
  have restored : (Source.EM.lift ((Source.Locals.cons (.bool true) inside).restore Γ) :
      Source.EM E [] (Source.Locals E.layout Γ)).run (.nil,state) = (.ok inside,(.nil,state)) := by
    rw [ForPhysical.restore_head]; rfl
  rw [Source.execS,Source.Hoare.run_bind,declared]
  dsimp only
  rw [Source.Hoare.run_bind,restored]
  rfl

theorem low {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (condition : Source.RExpr E Γ .bool)
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    ([0,1,2,3,4].map fun fuel=>(Source.execS G F fuel nps ph
      (loop (R:=R) (M:=M) (l:=l) (u:=u) index condition) inside).run (.nil,state)) =
      List.replicate 5 (.error .timeout,(Source.Locals.nil,state)) := rfl

theorem continue_low {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (flag : Source.Idx Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    ([0,1,2].map fun fuel=>(Source.execS G F fuel nps ph
      (.doWhile .cont (.assign (.local flag) (.bool false)) : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state)) =
      List.replicate 3 (.error .timeout,(Source.Locals.nil,state)) := rfl

theorem true_continue_step {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.doWhile .cont (.bool true) : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
    (Source.execS G F (fuel+1) nps ph
      (.doWhile .cont (.bool true) : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) := rfl

theorem true_continue_timeout {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F fuel nps ph
      (.doWhile .cont (.bool true) : Source.RStmt E R M ⟨l,u⟩ Γ Γ) inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => rw [true_continue_step]; exact ih

def execute {E : Source.Env} {Γ Δ Ξ : Source.RCtx} {R : List Source.STy} {M k}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (code : Source.RStmt E R M k Δ Ξ)
    (inside : Source.Locals E.layout Δ) : Source.EM E Γ (Source.Out E.layout Δ Ξ) := do
  let (out,_) ← Source.EM.sub .nil (Source.execS G F fuel 0 none code inside)
  pure out

theorem execute_rethrow {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat) (bytes : List UInt8)
    (index : Source.Idx Δ (.bytes .memory)) (condition : Source.RExpr E Δ .bool)
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (execute G F (fuel+5) (loop (R:=R) (M:=M) (l:=l) (u:=u) index condition) inside).run (outer,state) =
      (.error (.revert bytes),(outer,state)) := by
  unfold execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,rethrow_run G F fuel 0 address none bytes index inside condition state reference found]

def carry {E : Source.Env} {Γ Δ Λ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (index : Source.Idx Δ (.bytes .memory))
    (condition : Source.RExpr E Δ .bool) (inside : Source.Locals E.layout Δ)
    (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal) :=
  (AttemptPhysical.companion (execute G F fuel (loop (R:=R) (M:=M) (l:=l) (u:=u) index condition) inside) outer raw,residual,owned)

theorem carry_rethrow {E : Source.Env} {Γ Δ Λ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat) (bytes : List UInt8)
    (index : Source.Idx Δ (.bytes .memory)) (condition : Source.RExpr E Δ .bool)
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal)
    (reference : inside.get index=.memRef rfl address)
    (found : raw.2.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    carry (R:=R) (M:=M) (l:=l) (u:=u) G F (fuel+5) index condition inside outer raw residual owned =
      (((.ok (.error (.revert bytes)),(outer,raw.2)),raw),residual,owned) := by
  unfold carry
  rw [AttemptPhysical.companion_actual,execute_rethrow G F fuel address bytes index condition inside outer raw.2 reference found]


def sample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :=
  carry (R:=[]) (M:=false) (l:=false) (u:=false) G packedStepFrame fuel ForPhysical.dataIndex (.bool false)
    (ForPhysical.sampleInside bytes) ScopeCatchPhysical.outer (UncheckedLoopPhysical.sampleRaw bytes)
    firstPhysical.1.2 firstPhysical.2

theorem sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    sample G bytes (fuel+5) =
      (((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,(UncheckedLoopPhysical.sampleRaw bytes).2)),
        UncheckedLoopPhysical.sampleRaw bytes),firstPhysical.1.2,firstPhysical.2) := by
  apply carry_rethrow G packedStepFrame fuel firstPhysical.1.1.2.2.heap.next bytes ForPhysical.dataIndex
    (.bool false) (ForPhysical.sampleInside bytes) ScopeCatchPhysical.outer (UncheckedLoopPhysical.sampleRaw bytes)
    firstPhysical.1.2 firstPhysical.2 rfl
  exact Source.Heap.alloc_get _ _

theorem sample_dead (G : Source.Glob originEnv) :
    (sample G [0xde,0xad] 5).1.1.1 = .ok (.error (.revert [0xde,0xad])) := by rw [sample_run G _ 0]
theorem sample_empty (G : Source.Glob originEnv) :
    (sample G [] 5).1.1.1 = .ok (.error (.revert [])) := by rw [sample_run G _ 0]
theorem sample_panic (G : Source.Glob originEnv) :
    (sample G (Source.panicData .assert) 5).1.1.1 = .ok (.error (.revert (Source.panicData .assert))) := by rw [sample_run G _ 0]

theorem sample_wrong_alias (G : Source.Glob originEnv) (fuel : Nat) :
    carry (R:=[]) (M:=false) (l:=false) (u:=false) G packedStepFrame (fuel+5)
      (.there (.there .here)) (.bool false) (ForPhysical.sampleInside [0xde,0xad]) ScopeCatchPhysical.outer
      (UncheckedLoopPhysical.sampleRaw [0xde,0xad]) firstPhysical.1.2 firstPhysical.2 =
      (((.ok (.error (.revert [0xaa,0xbb])),(ScopeCatchPhysical.outer,(UncheckedLoopPhysical.sampleRaw [0xde,0xad]).2)),
        UncheckedLoopPhysical.sampleRaw [0xde,0xad]),firstPhysical.1.2,firstPhysical.2) := by
  apply carry_rethrow G packedStepFrame fuel 0 [0xaa,0xbb] (.there (.there .here)) (.bool false)
    (ForPhysical.sampleInside [0xde,0xad]) ScopeCatchPhysical.outer (UncheckedLoopPhysical.sampleRaw [0xde,0xad])
    firstPhysical.1.2 firstPhysical.2 rfl
  rfl

/-- Non-revert continuation retains the complete Source state and outer scope;
only the actual clean typed flag changes. Dirty raw companion remains separate. -/
theorem execute_continue {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (flag : Source.Idx Δ .bool)
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (execute G F (fuel+3)
      (.doWhile .cont (.assign (.local flag) (.bool false)) : Source.RStmt E R M ⟨l,u⟩ Δ Δ) inside).run (outer,state) =
      (.ok (.normal (inside.set flag (.bool false))),(outer,state)) := by
  unfold execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,continue_assign]
  rfl

theorem continue_companion {E : Source.Env} {Γ Δ Λ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (flag : Source.Idx Δ .bool)
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal) :
    (AttemptPhysical.companion (execute G F (fuel+3)
      (.doWhile .cont (.assign (.local flag) (.bool false)) : Source.RStmt E R M ⟨l,u⟩ Δ Δ) inside) outer raw,residual,owned) =
      (((.ok (.ok (.normal (inside.set flag (.bool false)))),(outer,raw.2)),raw),residual,owned) := by
  rw [AttemptPhysical.companion_actual,execute_continue]

end Solidity.Yul.Composition.DoWhilePhysical
