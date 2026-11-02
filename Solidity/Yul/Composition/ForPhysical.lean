import Solidity.Yul.Composition.UncheckedLoopPhysical

/-! Actual intrinsically typed Source for-loop consumers, not the Yul for_
interpreter or general loop/Source/compiler adequacy. Selected boolean-local
changes are ordinary existing Source operations, without arithmetic choices. -/
namespace Solidity.Yul.Composition.ForPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

def init {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (flag : Bool) : Source.RStmt E R M ⟨true,u⟩ Γ (.bool::Γ) := .declInit (.bool flag) rfl

def condition {E : Source.Env} {Γ : Source.RCtx} : Source.ROptBool E (.bool::Γ) := .some (.local .here)

def post {E : Source.Env} {Γ : Source.RCtx} (flag : Source.Idx Γ .bool) : Source.ROptExpr E (.bool::Γ) :=
  .some (.assign (.local .here) (.assign (.local (.there flag)) (.bool false)))

def poison {E : Source.Env} {Γ : Source.RCtx} (bytes : Source.Idx Γ (.bytes .memory)) : Source.ROptExpr E (.bool::Γ) :=
  .some (.indexBytes (.local (.there bytes)) (.const (Source.Q.ofInt 100)) (by decide))

def body {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (bytes : Source.Idx Γ (.bytes .memory)) : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ) :=
  .block (UncheckedLoopPhysical.items (.there bytes))

theorem pure_run {E Γ α} (value : α) (state : Source.EMState E Γ) :
    (pure value : Source.EM E Γ α).run state = (.ok value,state) := rfl

theorem init_run {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (flag : Bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph (init (R:=R) (M:=M) (u:=u) flag) inside).run (.nil,state) =
      (.ok (.normal (.cons (.bool flag) inside)),(.nil,state)) := rfl

theorem restore_head {D : Source.Layout} {Γ : Source.RCtx} {τ : Source.STy}
    (value : Source.Val D τ) (inside : Source.Locals D Γ) :
    (Source.Locals.cons value inside).restore Γ = .ok inside := by
  have count : ((τ::Γ).length-Γ.length)=1 := by simp only [List.length_cons]; omega
  unfold Source.Locals.restore
  rw [count]
  simp only [List.drop_succ_cons,List.drop_zero,dif_pos rfl]
  rfl

theorem condition_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (flag : Bool)
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.EM.sub (.cons (.bool flag) inside) (Source.evalE G F (fuel+1) (.local .here))).run (.nil,state) =
      (.ok (.val (.bool flag),.cons (.bool flag) inside),(.nil,state)) := rfl

theorem get_bool {E : Source.Env} (flag : Bool) (state : Source.St E) :
    (Source.getV (.val (.bool flag)) : Source.EM E [] (Source.Val E.layout .bool)).run (.nil,state) =
      (.ok (.bool flag),(.nil,state)) := rfl

theorem iter_false {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (step : Source.ROptExpr E (.bool::Γ)) (code : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) Δ)
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.forIter G F (fuel+2) nps ph condition step code (.cons (.bool false) inside)).run (.nil,state) =
      (.ok (.normal (.cons (.bool false) inside)),(.nil,state)) := by
  rw [Source.forIter.eq_def]
  simp only [Nat.add_succ,Nat.add_zero,condition]
  rw [Source.Hoare.run_bind,condition_run]
  dsimp only
  rw [Source.Hoare.run_bind,get_bool]
  rfl

theorem for_false {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (step : Source.ROptExpr E (.bool::Γ)) (code : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) Δ)
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+3) nps ph
      (.forLoop (l:=l) (init false) condition step code) inside).run (.nil,state) =
      (.ok (.normal inside),(.nil,state)) := by
  rw [Source.execS,Source.Hoare.run_bind,init_run]
  dsimp only
  rw [Source.Hoare.run_bind,iter_false]
  dsimp only
  have restored : (Source.EM.lift ((Source.Locals.cons (.bool false) inside).restore Γ) :
      Source.EM E [] (Source.Locals E.layout Γ)).run (.nil,state) = (.ok inside,(.nil,state)) := by
    rw [restore_head]
    rfl
  rw [Source.Hoare.run_bind,restored]
  rfl

theorem iter_revert {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (step : Source.ROptExpr E (.bool::Γ)) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.forIter G F (fuel+5) nps ph condition step (body (R:=R) (M:=M) (u:=u) index)
      (.cons (.bool true) inside)).run (.nil,state) = (.error (.revert bytes),(.nil,state)) := by
  have ran : (Source.execS G F (fuel+4) nps ph (body (R:=R) (M:=M) (u:=u) index)
      (.cons (.bool true) inside)).run (.nil,state) = (.error (.revert bytes),(.nil,state)) := by
    unfold body
    rw [Source.execS,Source.Hoare.run_bind,
      UncheckedLoopPhysical.items_run G F fuel nps address ph bytes (.there index) _ state reference found]
  rw [Source.forIter.eq_def]
  simp only [Nat.add_succ,Nat.add_zero,condition]
  rw [Source.Hoare.run_bind,condition_run]
  dsimp only
  rw [Source.Hoare.run_bind,get_bool]
  dsimp only
  rw [Source.Hoare.run_bind,pure_run]
  dsimp only
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pure_run]
  dsimp only
  rw [Source.Hoare.run_bind,ran]

/-- Actual init and first body run; arbitrary post is NOT reached on revert. -/
theorem for_revert {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (step : Source.ROptExpr E (.bool::Γ)) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+6) nps ph
      (.forLoop (l:=l) (init true) condition step (body (R:=R) (M:=M) (u:=u) index)) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  rw [Source.execS,Source.Hoare.run_bind,init_run]
  dsimp only
  rw [Source.Hoare.run_bind,iter_revert G F fuel nps address ph bytes index inside step state reference found]

/-- ACTUAL nested boolean assignments: both the fresh condition local and the
old caller flag change. No raw caller is run through this clean typed action. -/
theorem post_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (flag : Source.Idx Γ .bool)
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE G F (fuel+3) (.assign (.local .here) (.assign (.local (.there flag)) (.bool false)))).run
      (.cons (.bool true) inside,state) =
      (.ok (.val (.bool false)),(.cons (.bool false) (inside.set flag (.bool false)),state)) := rfl


theorem iter_break {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (step : Source.ROptExpr E (.bool::Γ)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.forIter G F (fuel+2) nps ph condition step
      (.brk : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ)) (.cons (.bool true) inside)).run (.nil,state) =
      (.ok (.normal (.cons (.bool true) inside)),(.nil,state)) := rfl

/-- BREAK skips arbitrary post, preserves caller locals and removes fresh init. -/
theorem for_break {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (step : Source.ROptExpr E (.bool::Γ)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+3) nps ph
      (.forLoop (l:=l) (init true) condition step (.brk : Source.RStmt E R M ⟨true,u⟩ _ _)) inside).run (.nil,state) =
      (.ok (.normal inside),(.nil,state)) := by
  rw [Source.execS,Source.Hoare.run_bind,init_run]
  dsimp only
  rw [Source.Hoare.run_bind,iter_break]
  dsimp only
  have restored : (Source.EM.lift ((Source.Locals.cons (.bool true) inside).restore Γ) :
      Source.EM E [] (Source.Locals E.layout Γ)).run (.nil,state) = (.ok inside,(.nil,state)) := by
    rw [restore_head]
    rfl
  rw [Source.Hoare.run_bind,restored]
  rfl

/-- CONTINUE executes the real post, changing BOTH locals, then reads false
from the changed condition local in a SECOND actual iteration test. -/
theorem iter_continue {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (flag : Source.Idx Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.forIter G F (fuel+4) nps ph condition (post flag)
      (.cont : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ)) (.cons (.bool true) inside)).run (.nil,state) =
      (.ok (.normal (.cons (.bool false) (inside.set flag (.bool false)))),(.nil,state)) := rfl

theorem for_continue {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (flag : Source.Idx Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+5) nps ph
      (.forLoop (l:=l) (init true) condition (post flag) (.cont : Source.RStmt E R M ⟨true,u⟩ _ _)) inside).run (.nil,state) =
      (.ok (.normal (inside.set flag (.bool false))),(.nil,state)) := by
  rw [Source.execS,Source.Hoare.run_bind,init_run]
  dsimp only
  rw [Source.Hoare.run_bind,iter_continue]
  dsimp only
  have restored : (Source.EM.lift ((Source.Locals.cons (.bool false) (inside.set flag (.bool false))).restore Γ) :
      Source.EM E [] (Source.Locals E.layout Γ)).run (.nil,state) = (.ok (inside.set flag (.bool false)),(.nil,state)) := by
    rw [restore_head]
    rfl
  rw [Source.Hoare.run_bind,restored]
  rfl

theorem invalid_init {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) nps ph
      (.forLoop (l:=l) (.brk : Source.RStmt E R M ⟨true,u⟩ Γ Γ) (.some (.bool true)) .none .skip) inside).run (.nil,state) =
      (.error (.stuck "for initializer"),(.nil,state)) := rfl

/-- The actual low horizons fail before the body can complete its rethrow. -/
theorem low_revert {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (step : Source.ROptExpr E (.bool::Γ)) (state : Source.St E) :
    ([0,1,2,3,4,5].map fun fuel => (Source.execS G F fuel nps ph
      (.forLoop (l:=l) (init true) condition step (body (R:=R) (M:=M) (u:=u) index)) inside).run (.nil,state)) =
      List.replicate 6 (.error .timeout,(Source.Locals.nil,state)) := rfl

theorem low_continue {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (flag : Source.Idx Γ .bool) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    ([0,1,2,3,4].map fun fuel => (Source.execS G F fuel nps ph
      (.forLoop (l:=l) (init true) condition (post flag) (.cont : Source.RStmt E R M ⟨true,u⟩ _ _)) inside).run (.nil,state)) =
      List.replicate 5 (.error .timeout,(Source.Locals.nil,state)) := rfl


def breakBody {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (index : Source.Idx Γ (.bytes .memory)) : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ) :=
  .block (.stmt .brk (.stmt (.rethrow (.there index)) .nil))

/-- BREAK skips the remaining BODY items; code after the WHOLE loop is different. -/
theorem iter_break_body {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (step : Source.ROptExpr E (.bool::Γ))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.forIter G F (fuel+4) nps ph condition step (breakBody (R:=R) (M:=M) (u:=u) index)
      (.cons (.bool true) inside)).run (.nil,state) =
      (.ok (.normal (.cons (.bool true) inside)),(.nil,state)) := rfl

theorem for_break_body {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (index : Source.Idx Γ (.bytes .memory)) (step : Source.ROptExpr E (.bool::Γ))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+5) nps ph
      (.forLoop (l:=l) (init true) condition step (breakBody (R:=R) (M:=M) (u:=u) index)) inside).run (.nil,state) =
      (.ok (.normal inside),(.nil,state)) := by
  rw [Source.execS,Source.Hoare.run_bind,init_run]
  dsimp only
  rw [Source.Hoare.run_bind,iter_break_body]
  dsimp only
  have restored : (Source.EM.lift ((Source.Locals.cons (.bool true) inside).restore Γ) :
      Source.EM E [] (Source.Locals E.layout Γ)).run (.nil,state) = (.ok inside,(.nil,state)) := by
    rw [restore_head]
    rfl
  rw [Source.Hoare.run_bind,restored]
  rfl

theorem revert_skips_rest {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (step : Source.ROptExpr E (.bool::Γ)) (rest : Source.RItems E R M ⟨l,u⟩ Γ Δ) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+7) nps ph
      (.stmt (.forLoop (l:=l) (init true) condition step (body (R:=R) (M:=M) (u:=u) index)) rest) inside).run (.nil,state) =
      (.error (.revert bytes),(.nil,state)) := by
  rw [Source.execItems,Source.Hoare.run_bind,for_revert G F fuel nps address ph bytes index inside step state reference found]

/-- A real body break does NOT skip the statements AFTER the for-loop. -/
theorem break_runs_after_loop {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps address : Nat) (ph : Option (Source.Ph E))
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (step : Source.ROptExpr E (.bool::Γ)) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+6) nps ph
      (.stmt (.forLoop (l:=l) (init true) condition step (breakBody (R:=R) (M:=M) (u:=u) index))
        (.stmt (.rethrow index) .nil)) inside).run (.nil,state) = (.error (.revert bytes),(.nil,state)) := by
  rw [Source.execItems,Source.Hoare.run_bind,for_break_body]
  dsimp only
  rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,
    UncheckedLoopPhysical.rethrow G F (fuel+3) nps address ph bytes index inside state reference found]

/-- The actual callee scope runner returns changed clean loop locals as data;
old typed evaluator locals are restored. It never resumes dirty raw callers. -/
def execute {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M k}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (code : Source.RStmt E R M k Δ Δ)
    (inside : Source.Locals E.layout Δ) : Source.EM E Γ (Source.Out E.layout Δ Δ) := do
  let (out,_) ← Source.EM.sub .nil (Source.execS G F fuel 0 none code inside)
  pure out

theorem execute_revert {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat) (bytes : List UInt8)
    (index : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ)
    (step : Source.ROptExpr E (.bool::Δ)) (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get index=.memRef rfl address)
    (found : state.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    (execute G F (fuel+6) (.forLoop (l:=l) (init true) condition step (body (R:=R) (M:=M) (u:=u) index)) inside).run (outer,state) =
      (.error (.revert bytes),(outer,state)) := by
  unfold execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,for_revert G F fuel 0 address none bytes index inside step state reference found]

theorem execute_continue {E : Source.Env} {Γ Δ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (flag : Source.Idx Δ .bool)
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (execute G F (fuel+5) (.forLoop (l:=l) (init true) condition (post flag) (.cont : Source.RStmt E R M ⟨true,u⟩ _ _)) inside).run (outer,state) =
      (.ok (.normal (inside.set flag (.bool false))),(outer,state)) := by
  unfold execute
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,for_continue]
  rfl

def carry {E : Source.Env} {Γ Δ Λ : Source.RCtx} {R : List Source.STy} {M k}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (code : Source.RStmt E R M k Δ Δ)
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal) :=
  (AttemptPhysical.companion (execute G F fuel code inside) outer raw,residual,owned)

theorem carry_revert {E : Source.Env} {Γ Δ Λ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat) (bytes : List UInt8)
    (index : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ)
    (step : Source.ROptExpr E (.bool::Δ)) (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal)
    (reference : inside.get index=.memRef rfl address)
    (found : raw.2.heap.get address=some ⟨.bytes .memory,.bytes bytes⟩) :
    carry G F (fuel+6) (.forLoop (l:=l) (init true) condition step (body (R:=R) (M:=M) (u:=u) index))
      inside outer raw residual owned = (((.ok (.error (.revert bytes)),(outer,raw.2)),raw),residual,owned) := by
  unfold carry
  rw [AttemptPhysical.companion_actual,execute_revert G F fuel address bytes index inside step outer raw.2 reference found]

theorem carry_continue {E : Source.Env} {Γ Δ Λ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (flag : Source.Idx Δ .bool)
    (inside : Source.Locals E.layout Δ) (outer : Source.Locals E.layout Γ) (raw : LocalState E Λ)
    (residual : ResidualJournal complementCarrierOwnership) (owned : BoolEncodingJournal) :
    carry G F (fuel+5) (.forLoop (l:=l) (init true) condition (post flag) (.cont : Source.RStmt E R M ⟨true,u⟩ _ _))
      inside outer raw residual owned =
      (((.ok (.ok (.normal (inside.set flag (.bool false)))),(outer,raw.2)),raw),residual,owned) := by
  unfold carry
  rw [AttemptPhysical.companion_actual,execute_continue]

abbrev Clean := .bool :: ScopeCatchPhysical.Inner

def sampleInside (bytes : List UInt8) : Source.Locals originEnv.layout Clean :=
  .cons (.bool true) (UncheckedLoopPhysical.sampleInside bytes)
def dataIndex : Source.Idx Clean (.bytes .memory) := .there .here

def sample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :=
  carry G packedStepFrame fuel
    (.forLoop (l:=false) (init true) condition (poison dataIndex) (body (R:=[]) (M:=false) (u:=false) dataIndex))
    (sampleInside bytes) ScopeCatchPhysical.outer (UncheckedLoopPhysical.sampleRaw bytes) firstPhysical.1.2 firstPhysical.2

theorem sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    sample G bytes (fuel+6) =
      (((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,(UncheckedLoopPhysical.sampleRaw bytes).2)),UncheckedLoopPhysical.sampleRaw bytes),
        firstPhysical.1.2,firstPhysical.2) := by
  apply carry_revert G packedStepFrame fuel firstPhysical.1.1.2.2.heap.next bytes dataIndex _ _ _ _ _ _ rfl
  exact Source.Heap.alloc_get _ _

theorem sample_wrong_alias (G : Source.Glob originEnv) (fuel : Nat) :
    carry G packedStepFrame (fuel+6)
      (.forLoop (l:=false) (init true) condition (poison dataIndex)
        (body (R:=[]) (M:=false) (u:=false) (.there (.there .here))))
      (sampleInside [0xde,0xad]) ScopeCatchPhysical.outer (UncheckedLoopPhysical.sampleRaw [0xde,0xad]) firstPhysical.1.2 firstPhysical.2 =
      (((.ok (.error (.revert [0xaa,0xbb])),(ScopeCatchPhysical.outer,(UncheckedLoopPhysical.sampleRaw [0xde,0xad]).2)),UncheckedLoopPhysical.sampleRaw [0xde,0xad]),
        firstPhysical.1.2,firstPhysical.2) := by
  apply carry_revert G packedStepFrame fuel 0 [0xaa,0xbb] (.there (.there .here)) _ _ _ _ _ _ rfl
  rfl


/-- Omitting the post is genuinely different: actual continue never changes the
true condition local. The real iterator times out at EVERY horizon. -/
theorem iter_no_post_step {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.forIter G F (fuel+2) nps ph condition .none
      (.cont : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ)) (.cons (.bool true) inside)).run (.nil,state) =
    (Source.forIter G F (fuel+1) nps ph condition .none
      (.cont : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ)) (.cons (.bool true) inside)).run (.nil,state) := by
  have continued : (Source.execS G F (fuel+1) nps ph
      (.cont : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ)) (.cons (.bool true) inside)).run (.nil,state) =
      (.ok (.cont (.cons (.bool true) inside)),(.nil,state)) := rfl
  rw [Source.forIter.eq_def]
  simp only [Nat.add_succ,Nat.add_zero,condition]
  rw [Source.Hoare.run_bind,condition_run]
  dsimp only
  rw [Source.Hoare.run_bind,get_bool]
  dsimp only
  rw [Source.Hoare.run_bind,pure_run]
  dsimp only
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pure_run]
  dsimp only
  rw [Source.Hoare.run_bind,continued]
  dsimp only
  rw [Source.Hoare.run_bind,pure_run]
  dsimp only
  rw [Source.Hoare.run_bind,pure_run]

theorem iter_no_post_timeout {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.forIter G F fuel nps ph condition .none
      (.cont : Source.RStmt E R M ⟨true,u⟩ (.bool::Γ) (.bool::Γ)) (.cons (.bool true) inside)).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => rw [iter_no_post_step]; exact ih

theorem for_no_post_timeout {E : Source.Env} {Γ : Source.RCtx} {R : List Source.STy} {M l u}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F fuel nps ph
      (.forLoop (l:=l) (init true) condition .none (.cont : Source.RStmt E R M ⟨true,u⟩ _ _)) inside).run (.nil,state) =
      (.error .timeout,(.nil,state)) := by
  cases fuel with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ fuel =>
        rw [Source.execS,Source.Hoare.run_bind,init_run]
        dsimp only
        rw [Source.Hoare.run_bind,iter_no_post_timeout]

end Solidity.Yul.Composition.ForPhysical
