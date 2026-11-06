import Solidity.Backend.PrimitivePackets.Comparisons.Agreement
import Solidity.Roadmap.Controls

/-! Inhabited physical layouts and actual observations at equality, signed sign
boundaries and maximum unsigned operands. Both source pipelines are exercised;
the complete initial physical machine survives below the Boolean result. -/
namespace Solidity.Backend.PrimitivePackets.Comparisons.Controls
open Lowering.V07 Evm Evm.Memory

def C : Contract := contract!{}
def E : Source.Env := ⟨[]⟩
def program : Source.Program E where
  body := fun _ => none
  consts := fun _ => none
  inits := fun _ => []
  ctor := fun _ => none
  ctorLocals := fun _ => []
  baseArgs := fun _ => []
  contracts := []
def global (p : Roadmap.Pipeline) : Source.Glob E :=
  ⟨program,p,Roadmap.Controls.toyFixed,fun _ => ⟨0,by decide⟩,
    fun _ _ => false,fun _ => .answer (.success []),⟨0,by decide⟩⟩
def frame : Source.Fr where
  this := ⟨0,by decide⟩
  sender := ⟨0,by decide⟩
  value := ⟨0,by decide⟩
  static := false
  contract := "C"
def sourceState : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩,Source.Transient.empty,[]⟩,
    Source.Heap.empty,[],[(⟨0,by decide⟩,[7])],⟨[.bool],.cons (.bool true) .nil⟩,
    Source.FailureExecution.Cursor.empty⟩
def initial : State C [] := State.init C
def machine0 : Machine := (Machine.init (fun _ => 0) ⟨0,W_pos⟩).push w[77]
def addresses : Nat → Fin W := fun _ => wmod 0

theorem initial_repr : StateRepr 1 0 4 (Frag.init []) initial addresses machine0 := by
  have noRef {R : RefTy} (r : HRef [] R) : False := by
    simpa only [List.getElem?_nil,reduceCtorEq] using r.get?
  have core : Sim C 1 0 (Frag.init []) initial machine0 := by
    refine ⟨?_,(fun i => nomatch i),(fun i => nomatch i),?_,rfl,by decide,
      (fun i => nomatch i),⟨rfl,rfl,rfl,rfl⟩,rfl,?_⟩
    · intro name T h
      change (none : Option Ty) = some T at h
      cases h
    · intro a different
      rfl
    · intro addr amt a b ha hb
      rfl
  refine ⟨core,
    ⟨fun r => (noRef r).elim,fun r => (noRef r).elim,fun r _ _ => (noRef r).elim⟩,
    ?_,by decide,
    ⟨fun r => (noRef r).elim,fun r => (noRef r).elim,fun r => (noRef r).elim⟩,
    (fun _ r => (noRef r).elim),RefFieldsRepr.withoutStructs _ _ _ (fun r => noRef r)⟩
  intro R i
  nomatch i

def word (signed : Bool) (x : Int) (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) : Evm.Word := by
  cases signed
  · exact .val (integerValue (ty false) x hx).word
  · exact .val (sword x)

theorem word_repr (signed : Bool) (x : Int) (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) :
    ReprV (prim signed) (integerValue (ty signed) x hx) (word signed x hx) := by
  cases signed
  · exact ⟨_,rfl,(word_val (integerValue (ty false) x hx)).symm⟩
  · exact ReprV.int_word (integerValue (ty true) x hx)

def target (signed : Bool) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) :=
  (initial.push (t:=.val (prim signed)) (integerValue (ty signed) y hy)).push
    (t:=.val (prim signed)) (integerValue (ty signed) x hx)
def machine (signed : Bool) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) :=
  writeMachine (writeMachine machine0 (cell 0) (word signed y hy)) (cell 1) (word signed x hx)
def fragment (signed : Bool) := (Frag.init []).push (.val (prim signed)) .ok |>.push (.val (prim signed)) .ok

def source (signed : Bool) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) :
    Source.EMState E [.int (ty signed),.int (ty signed)] :=
  (.cons (.int x hx) (.cons (.int y hy) .nil),sourceState)

def Check (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) : Prop :=
  StateRepr 1 0 4 (fragment signed) (target signed x y hx hy) addresses (machine signed x y hx hy) ∧
  (Source.evalE (global p) frame 3 (expression o signed .here (.there .here))).run (source signed x y hx hy) =
    (.ok (.val (.bool (result o x y))),source signed x y hx hy) ∧
  compileVal 0 (fragment signed) (value (C:=C) o signed .here (.there .here)) =
    some (selected (C:=C) 0 (fragment signed) o signed .here (.there .here)) ∧
  run (selected (C:=C) 0 (fragment signed) o signed .here (.there .here)).code (machine signed x y hx hy) =
    .ok ((machine signed x y hx hy).push (.val (bword (result o x y)))) 0

theorem checked (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi) (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) : Check o signed p x y hx hy := by
  have repr := (initial_repr.consVal (integerValue (ty signed) y hy) (word signed y hy) (word_repr signed y hy) (by decide)).consVal
    (integerValue (ty signed) x hx) (word signed x hx) (word_repr signed x hx) (by change 2 ≤ 4; decide)
  exact ⟨repr,agreement (global p) frame 0 (source signed x y hx hy) (target signed x y hx hy)
    o signed .here (.there .here) .here (.there .here) x y hx hy rfl rfl rfl rfl repr⟩

theorem equality (o : Order) (signed : Bool) (p : Roadmap.Pipeline) :
    Check o signed p 7 7 (by cases signed <;> decide) (by cases signed <;> decide) :=
  checked o signed p 7 7 _ _

theorem sign_boundary (o : Order) (p : Roadmap.Pipeline) :
    Check o true p (-1) 0 (by decide) (by decide) :=
  checked o true p (-1) 0 _ _

theorem endpoints (signed : Bool) : (ty signed).lo ≤ (ty signed).hi := by
  cases signed <;> simp only [ty,Source.IntTy.lo,Source.IntTy.hi,↓reduceIte] <;> omega

theorem signed_extremes (o : Order) (p : Roadmap.Pipeline) :
    Check o true p (ty true).lo (ty true).hi ⟨Int.le_refl _,endpoints true⟩ ⟨endpoints true,Int.le_refl _⟩ :=
  checked o true p _ _ _ _

theorem unsigned_maximum (o : Order) (p : Roadmap.Pipeline) :
    Check o false p (ty false).hi (ty false).lo ⟨endpoints false,Int.le_refl _⟩ ⟨Int.le_refl _,endpoints false⟩ :=
  checked o false p _ _ _ _

#print axioms initial_repr
#print axioms checked
#print axioms equality
#print axioms sign_boundary
#print axioms signed_extremes
#print axioms unsigned_maximum
end Solidity.Backend.PrimitivePackets.Comparisons.Controls
