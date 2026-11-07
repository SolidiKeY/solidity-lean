import Solidity.Lowering.V08.IntegerCallable

/-! Guards the regression where integer-callable input fixtures inhabit only
uint256 or one signed width while the public component quantifies over every
native IntTy. Declaration membership, signature and selected body are realized
in the SAME environment for arbitrary valid sign/width. Actual execution uses
the unchanged published component laws, never an assumed desired run.
This is not ABI ingress, arbitrary-body compilation or SourceSpec admission. -/
namespace H62.AuditV08Adapters.IntegerCallableJoint
open Solidity Source
open Solidity.Lowering.V07
open Solidity.Lowering.V08

def intSyntax (t : Source.IntTy) : Syn .typeName := .elem (.int t.signed t.bits t.valid)
def params (t : Source.IntTy) : Syn (.list .param) :=
  .cons (.param (intSyntax t) none (some "n")) .nil
def returns (t : Source.IntTy) : Syn (.list .param) :=
  .cons (.param (intSyntax t) none (some "answer")) .nil
def fnSyntax (t : Source.IntTy) : Syn (.part false) :=
  .function (.ident "echo") (params t) (some .pub) none .nil false none (returns t)
    (.some (.block (.cons ScalarCallableTransport.returnSyntax .nil)))
def unit (t : Source.IntTy) : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
    (.cons ScalarCallableTransport.savedSyntax (.cons ScalarCallableTransport.scratchSyntax
      (.cons (fnSyntax t) .nil)))) .nil)
def env (t : Source.IntTy) : Source.Env := (unit t).env
def declaration (t : Source.IntTy) : Source.Decl :=
  ⟨.function,"echo",some "C",false,fnSyntax t⟩
def program (t : Source.IntTy) : Source.Program (env t) :=
  {body:=fun _ => some (IntegerCallable.body (env t) t),
   consts:=fun _ => none,inits:=fun _ => [],ctor:=fun _ => none,
   ctorLocals:=fun _ => [],baseArgs:=fun _ => [],contracts:=["C"]}
def global (t : Source.IntTy) (p : Roadmap.Pipeline) : Source.Glob (env t) :=
  {prog:=program t,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
   balance0:=fun _ => ScalarCallableTransport.word 93,hasCode:=fun _ _ => false,
   callee:=fun _ => .answer (.success []),timestamp:=ScalarCallableTransport.word 12345}
abbrev frame := ScalarCallableTransport.frame

/-- All four public Inputs fields hold together for every native integer type. -/
theorem inputs (t : Source.IntTy) (p : Roadmap.Pipeline) :
    IntegerCallable.Inputs (global t p) frame (declaration t) t := by
  constructor
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))
  · rfl
  · cases t with | mk signed bits valid => rfl
  · rfl

/-- The numeric range premise has a value in the SAME selected input model. -/
theorem joint (t : Source.IntTy) (p : Roadmap.Pipeline) :
    IntegerCallable.Inputs (global t p) frame (declaration t) t ∧
      ∃ n : Int, t.lo ≤ n ∧ n ≤ t.hi :=
  ⟨inputs t p, 0, t.zero_mem⟩

/-- Exact original source-call law, with no assumed selection or execution. -/
theorem source_actual (t : Source.IntTy) (p : Roadmap.Pipeline)
    (extra : Nat) (state : Source.St (env t)) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (Source.callInternal (global t p) frame (extra+12) (declaration t)
      (.cons (.int n h) .nil) [.int t]).run (Source.L0 (env t),state) =
      (.ok (.val (.int n h)),(Source.L0 (env t),state)) :=
  IntegerCallable.source_call _ _ _ _ (inputs t p) extra state n h

/-- The full original component transport on this coherent model, including
both target phases, value relation and restoration of the entire caller. -/
theorem transport_actual (t : Source.IntTy) (p : Roadmap.Pipeline)
    (extra : Nat) (source : Source.St (env t)) (C : Contract) (target : State C [])
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (Source.callInternal (global t p) frame (extra+12) (declaration t)
      (.cons (.int n h) .nil) [.int t]).run (Source.L0 (env t),source) =
      (.ok (.val (.int n h)),(Source.L0 (env t),source)) ∧
    (IntegerCallable.entry C (declaration t) t n h).body.run target =
      .ok ⟨target.push (t:=.val (integerPrim t)) (integerValue t n h),List.prefix_refl _⟩ ∧
    (IntegerCallable.entry C (declaration t) t n h).result
      (target.push (t:=.val (integerPrim t)) (integerValue t n h)) =
      .ok (integerValue t n h) ∧
    IntValueRel t (.int n h : Source.Val (env t).layout (.int t)) (integerValue t n h) ∧
    (target.push (t:=.val (integerPrim t)) (integerValue t n h)).drop
      (IntegerCallable.entry C (declaration t) t n h).body.ext = target :=
  IntegerCallable.transport _ _ _ _ (inputs t p) extra source C target n h

/-- A different mathematical result cannot be hidden by target numeric encoding. -/
theorem wrong_value_refused (t : Source.IntTy) (n : Int)
    (h : t.lo ≤ n ∧ n ≤ t.hi) (wrong : Int) (different : n ≠ wrong) :
    PrimTy.num? (integerValue t n h) ≠ some wrong := by
  rw [integer_observe]
  intro same
  exact different (Option.some.inj same)

def missing (t : Source.IntTy) (p : Roadmap.Pipeline) : Source.Glob (env t) :=
  {global t p with prog := {program t with body := fun _ => none}}

/-- A missing body cannot satisfy the same Inputs; no execution filter is added. -/
theorem missing_body_refused (t : Source.IntTy) (p : Roadmap.Pipeline) :
    ¬ IntegerCallable.Inputs (missing t p) frame (declaration t) t := by
  intro h
  have bad := h.selected
  change none = some (IntegerCallable.body (env t) t) at bad
  cases bad

/-- Missing selection has the actual stuck outcome, with the full state retained. -/
theorem missing_actual (t : Source.IntTy) (p : Roadmap.Pipeline)
    (extra : Nat) (state : Source.St (env t)) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (Source.callInternal (missing t p) frame (extra+1) (declaration t)
      (.cons (.int n h) .nil) [.int t]).run (Source.L0 (env t),state) =
      (.error (.stuck "function without a body"),(Source.L0 (env t),state)) :=
  SourceCallable.missing_body _ _ extra _ _ state rfl

/-- Even the inhabited successful model times out at the original zero horizon. -/
theorem timeout_actual (t : Source.IntTy) (p : Roadmap.Pipeline)
    (state : Source.St (env t)) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (Source.callInternal (global t p) frame 0 (declaration t)
      (.cons (.int n h) .nil) [.int t]).run (Source.L0 (env t),state) =
      (.error .timeout,(Source.L0 (env t),state)) :=
  SourceCallable.zero_horizon _ _ _ _ state

/-- Both endpoints inhabit the SAME original native integer range. -/
theorem lower_range (t : Source.IntTy) : t.lo ≤ t.lo ∧ t.lo ≤ t.hi :=
  ⟨Int.le_refl _, Int.le_trans t.zero_mem.1 t.zero_mem.2⟩

theorem upper_range (t : Source.IntTy) : t.lo ≤ t.hi ∧ t.hi ≤ t.hi :=
  ⟨Int.le_trans t.zero_mem.1 t.zero_mem.2, Int.le_refl _⟩

/-- Minimum, zero and maximum execute in one selected model, each preserving
its complete supplied locals/state pair; these are three component calls. -/
theorem boundary_calls (t : Source.IntTy) (p : Roadmap.Pipeline)
    (extra : Nat) (state : Source.St (env t)) :
    IntegerCallable.Inputs (global t p) frame (declaration t) t ∧
    (Source.callInternal (global t p) frame (extra+12) (declaration t)
      (.cons (.int t.lo (lower_range t)) .nil) [.int t]).run (Source.L0 (env t),state) =
      (.ok (.val (.int t.lo (lower_range t))),(Source.L0 (env t),state)) ∧
    (Source.callInternal (global t p) frame (extra+12) (declaration t)
      (.cons (.int 0 t.zero_mem) .nil) [.int t]).run (Source.L0 (env t),state) =
      (.ok (.val (.int 0 t.zero_mem)),(Source.L0 (env t),state)) ∧
    (Source.callInternal (global t p) frame (extra+12) (declaration t)
      (.cons (.int t.hi (upper_range t)) .nil) [.int t]).run (Source.L0 (env t),state) =
      (.ok (.val (.int t.hi (upper_range t))),(Source.L0 (env t),state)) :=
  ⟨inputs t p, source_actual t p extra state t.lo (lower_range t),
    source_actual t p extra state 0 t.zero_mem,
    source_actual t p extra state t.hi (upper_range t)⟩

/-- Target observations retain the mathematical endpoints, including the
signed lower endpoint rather than replacing it with its unsigned encoding. -/
theorem boundary_values (t : Source.IntTy) :
    PrimTy.num? (integerValue t t.lo (lower_range t)) = some t.lo ∧
    PrimTy.num? (integerValue t 0 t.zero_mem) = some 0 ∧
    PrimTy.num? (integerValue t t.hi (upper_range t)) = some t.hi :=
  ⟨integer_observe _ _ _, integer_observe _ _ _, integer_observe _ _ _⟩

#print axioms joint
#print axioms transport_actual
#print axioms missing_body_refused
#print axioms wrong_value_refused
#print axioms missing_actual
#print axioms timeout_actual
#print axioms boundary_calls
#print axioms boundary_values

end H62.AuditV08Adapters.IntegerCallableJoint
