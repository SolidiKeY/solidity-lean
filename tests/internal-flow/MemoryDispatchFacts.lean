import tests.«internal-flow».FiniteDispatchFacts
import Solidity.Syntax.Splice
import Solidity.Semantics.Dispatch
namespace Solidity.Backend.InternalFlow.MemoryDispatchChecks
open Evm Evm.Memory FiniteDispatch PublishedDirectCalls

def C : Contract := contract!{
  uint count;
  function first(uint[] memory xs, uint k) returns (uint[] memory r) {
    uint[] memory dead = new uint[](4); count = 1000; r = xs;
  }
  function second(uint[] memory xs, uint k) returns (uint[] memory r) {
    xs[0] = xs[0] + k; count = count + 2; r = xs;
    xs = new uint[](2); xs[0] = 99; xs[1] = 101;
  }
}
def front := sol[C]{
  count = 9; uint marker = 42;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](2); other[0] = 23; other[1] = 29;
  function (uint[] memory, uint) returns (uint[] memory) h = second;
  uint[] memory returned = h(xs, 5);
}

abbrev A : RefTy := .array (.prim .uint)
abbrev Caller : Ctx := [.mem A,.val .uint,.mem A,.val .uint,.mem A,.mem A,.mem A,.val .uint]
abbrev Final : Ctx := .mem A :: Caller
private def suffix {Γ Δ : Ctx} (n : Nat) (P : Prog C Γ Δ) : Σ Ξ, Prog C Ξ Δ :=
  match n,P with
  | 0,P => ⟨Γ,P⟩
  | _+1,.nil => ⟨Γ,.nil⟩
  | n+1,.cons _ P => suffix n P
private def splitAt {Γ Δ : Ctx} (n : Nat) (P : Prog C Γ Δ) :
    Σ Ξ, Prog C Γ Ξ × Prog C Ξ Δ :=
  match n,P with
  | 0,P => ⟨Γ,.nil,P⟩
  | _+1,.nil => ⟨Γ,.nil,.nil⟩
  | n+1,.cons s P => let t := splitAt n P; ⟨t.1,.cons s t.2.1,t.2.2⟩
def seedProgram : Prog C [] Caller := (splitAt 13 front).2.1
def directFirst := sol[C]{count = 9; uint marker = 42;
 uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
 uint[] memory same = xs; uint[] memory other = new uint[](2); other[0] = 23; other[1] = 29;
 function (uint[] memory, uint) returns (uint[] memory) h = second;
 uint[] memory se1 = xs; uint se2 = 5; uint[] memory mv3;mv3 = first(se1,se2);}
def directSecond := sol[C]{count = 9; uint marker = 42;
 uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
 uint[] memory same = xs; uint[] memory other = new uint[](2); other[0] = 23; other[1] = 29;
 function (uint[] memory, uint) returns (uint[] memory) h = second;
 uint[] memory se1 = xs; uint se2 = 5; uint[] memory mv3;mv3 = second(se1,se2);}
def actualFirst : DispatchArm C Caller := match (suffix 13 front).2 with
 | .cons (.ite c t _) _ => ⟨c,t⟩
 | _ => ⟨.simple (.bool false),.nil⟩
def rest : Σ Ξ, Prog C Caller Ξ := match (suffix 13 front).2 with
 | .cons (.ite _ _ e) _ => ⟨_,e⟩
 | _ => ⟨Caller,.nil⟩
def actualSecond : DispatchArm C Caller := match rest.2 with
 | .cons (.ite c t _) .nil => ⟨c,t⟩
 | _ => ⟨.simple (.bool false),.nil⟩
def actualDispatch := DispatchArm.chain [actualFirst,actualSecond] (.revert : Stmt C Caller Caller)
def post : Prog C Caller Final := (suffix 14 front).2
theorem frontend_link : front = seedProgram.join (.cons actualDispatch post) := by rfl
def guard (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Caller .bool :=
 .binop .eqB rfl rfl (.simple (.local (.there (.there (.there .here))))) (.simple (.lit n hn))
theorem first_guard : actualFirst.cond = guard 1 rfl := by rfl
theorem second_guard : actualSecond.cond = guard 2 rfl := by rfl
theorem first_direct (σ : State C Caller) :
 (actualFirst.body.run σ).map (fun o => o.st.drop actualFirst.body.ext) =
 (((suffix 13 directFirst).2).run σ).map (fun o => o.st.drop ((suffix 13 directFirst).2).ext) := by rfl
theorem second_direct (σ : State C Caller) :
 (actualSecond.body.run σ).map (fun o => o.st.drop actualSecond.body.ext) =
 (((suffix 13 directSecond).2).run σ).map (fun o => o.st.drop ((suffix 13 directSecond).2).ext) := by rfl

private theorem actual_get {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by cases r <;> cases h <;> rfl
private theorem ok_of_toOption {α : Type} (r : TRes α) (a : α) (h : r.toOption = some a) : r = .ok a := by
  cases r <;> cases h <;> rfl
abbrev bases := DispatchChecks.bases
abbrev machine := DispatchChecks.machine
theorem initial_repr : StateRepr 1 1 64 (Frag.init []) (State.init C) bases machine ∧
 StructAllocatorRepr (State.init C).heap bases 64 (wmod 128) machine := DispatchChecks.initial_repr C

def seed : Calls.Program 1 (Frag.init []) seedProgram :=
 (Calls.compile 1 (Frag.init []) seedProgram).get (by decide +kernel)
attribute [irreducible] seed
def mid : Solidity.Out C [] Caller := (seedProgram.run (State.init C)).toOption.get (by decide +kernel)
theorem seed_run : seedProgram.run (State.init C) = .ok mid := actual_get _ (by decide +kernel)
def firstCert : Calls.Program 1 seed.frag actualFirst.body :=
 (Calls.compile 1 seed.frag actualFirst.body).get (by decide +kernel)
def secondCert : Calls.Program 1 seed.frag actualSecond.body :=
 (Calls.compile 1 seed.frag actualSecond.body).get (by decide +kernel)
attribute [irreducible] firstCert secondCert
def firstCond : CompiledVal 1 seed.frag actualFirst.cond :=
 (Memory.compileVal 1 seed.frag actualFirst.cond).get (by decide +kernel)
def secondCond : CompiledVal 1 seed.frag actualSecond.cond :=
 (Memory.compileVal 1 seed.frag actualSecond.cond).get (by decide +kernel)
def fallback : Calls.Statement 1 seed.frag (.revert : Stmt C Caller Caller) :=
 Calls.plainStmt ((Memory.compileStmt 1 seed.frag (.revert : Stmt C Caller Caller)).get (by decide +kernel))
def checked : Calls.Statement 1 seed.frag actualDispatch :=
 checkedChain 1 seed.frag .revert fallback [actualFirst,actualSecond]
   ⟨⟨firstCond,firstCert⟩,⟨⟨secondCond,secondCert⟩,()⟩⟩
attribute [irreducible] checked

def armOut : Solidity.Out C mid.st.H actualSecond.Γ' :=
 (actualSecond.body.run mid.st).toOption.get (by decide +kernel)
def chosen : Solidity.Out C mid.st.H Caller := ⟨armOut.st.drop actualSecond.body.ext,armOut.ext⟩
theorem first_miss : actualFirst.cond.evalT mid.st = .ok false := ok_of_toOption _ false (by decide +kernel)
theorem second_hit : actualSecond.cond.evalT mid.st = .ok true := ok_of_toOption _ true (by decide +kernel)
theorem body_run : actualSecond.body.run mid.st = .ok armOut := actual_get _ (by decide +kernel)
theorem chosen_run : actualDispatch.run mid.st = .ok chosen := by
 change (DispatchArm.chain ([actualFirst] ++ actualSecond :: []) (.revert : Stmt C Caller Caller)).run mid.st = _
 rw [select_run [actualFirst] actualSecond [] .revert mid.st (by
   intro a h; have ha := List.mem_singleton.mp h; subst a; exact first_miss) second_hit,body_run]
 rfl

def postCert : Calls.Program 1 checked.frag post := (Calls.compile 1 checked.frag post).get (by decide +kernel)
attribute [irreducible] postCert
def finished : Solidity.Out C chosen.st.H Final := (post.run chosen.st).toOption.get (by decide +kernel)
theorem post_run : post.run chosen.st = .ok finished := actual_get _ (by decide +kernel)

def array {Γ : Ctx} (σ : State C Γ) (id : Nat) : Option (List Int) :=
 if h : σ.H[id]? = some A then
   let r : HRef σ.H A := ⟨id,h⟩
   some ((σ.heap.len r .dyn : Int) :: (MObj.elems .dyn (σ.heap.get r)).map (fun n => n.1))
 else none
def root {Γ : Ctx} (σ : State C Γ) : Option Int :=
 ((Val.read (.root "count" rfl) : Val C Γ .uint).evalT σ).toOption.map (·.1)
def locals (σ : State C Caller) : List (Option Nat) :=
 [σ.env.1.map (·.id),some σ.env.2.1.1.toNat,σ.env.2.2.1.map (·.id),
  some σ.env.2.2.2.1.1.toNat,σ.env.2.2.2.2.1.map (·.id),
  σ.env.2.2.2.2.2.1.map (·.id),σ.env.2.2.2.2.2.2.1.map (·.id),
  some σ.env.2.2.2.2.2.2.2.1.1.toNat]
theorem before_values : (mid.st.H.length,[array mid.st 0,array mid.st 1,array mid.st 2],locals mid.st,root mid.st) =
 (3,[some [2,7,11],some [2,23,29],some [0]],
  [some 2,some 5,some 0,some 2,some 1,some 0,some 0,some 42],some 9) := by decide +kernel
theorem after_values : (chosen.st.H.length,[array chosen.st 0,array chosen.st 1,array chosen.st 2,array chosen.st 3,array chosen.st 4],locals chosen.st,root chosen.st) =
 (5,[some [2,12,11],some [2,23,29],some [0],some [0],some [2,99,101]],
  [some 0,some 5,some 0,some 2,some 1,some 0,some 0,some 42],some 11) := by decide +kernel
theorem final_values :
 (finished.st.H.length,finished.st.env.1.map (·.id),
  locals (finished.st.drop (Ext.append Caller [.mem A])),root finished.st) =
 (5,some 0,[some 0,some 5,some 0,some 2,some 1,some 0,some 0,some 42],some 11) := by decide +kernel

theorem seed_cost : seed.cost (State.init C) = 7 := by decide +kernel
theorem seed_frame : 1 + seed.need ≤ 64 := by decide +kernel
theorem first_cost : firstCert.cost mid.st = 6 := by decide +kernel
theorem second_cost : secondCert.cost mid.st = 4 := by decide +kernel
theorem reached_cost : checked.cost mid.st = 4 := by decide +kernel
theorem frame_need : checked.need = 12 := by decide +kernel
theorem room : 1 + checked.need ≤ 64 := by rw [frame_need]; decide
theorem post_cost : postCert.cost chosen.st = 0 := by decide +kernel
theorem post_room : 1 + postCert.need ≤ 64 := by decide +kernel

def old : HRef mid.st.H A := ⟨0,by decide +kernel⟩
def other : HRef mid.st.H A := ⟨1,by decide +kernel⟩
def sharedDefault : HRef mid.st.H A := ⟨2,by decide +kernel⟩
def callDefault : HRef chosen.st.H A := ⟨3,by decide +kernel⟩
def privateNew : HRef chosen.st.H A := ⟨4,by decide +kernel⟩
def exported : HRef finished.st.H A := (old.wk chosen.ext).wk finished.ext
private theorem ref_by_id {H : HTy} {R : RefTy} (v : Option (HRef H R)) (r : HRef H R)
 (h : v.map (·.id) = some r.id) : v = some r := by
 cases v with
 | none => cases h
 | some q =>
   have eq : q = r := by
     cases q; cases r
     have e := Option.some.inj h
     cases e; rfl
   cases eq; rfl

theorem final_aliases :
 TEnv.get (.here : Idx Final (.mem A)) finished.st.env = some exported ∧
 TEnv.get (.there .here : Idx Final (.mem A)) finished.st.env = some exported ∧
 TEnv.get (.there (.there (.there .here)) : Idx Final (.mem A)) finished.st.env = some exported ∧
 TEnv.get (.there (.there (.there (.there (.there (.there .here))))) : Idx Final (.mem A)) finished.st.env = some exported ∧
 TEnv.get (.there (.there (.there (.there (.there (.there (.there .here)))))) : Idx Final (.mem A)) finished.st.env = some exported ∧
 TEnv.get (.there (.there (.there (.there (.there .here)))) : Idx Final (.mem A)) finished.st.env = some ((other.wk chosen.ext).wk finished.ext) := by
 refine ⟨ref_by_id _ _ (by decide +kernel),ref_by_id _ _ (by decide +kernel),
   ref_by_id _ _ (by decide +kernel),ref_by_id _ _ (by decide +kernel),
   ref_by_id _ _ (by decide +kernel),ref_by_id _ _ (by decide +kernel)⟩

theorem heap_values :
 finished.st.heap.len exported .dyn = 2 ∧
 finished.st.heap.len ((other.wk chosen.ext).wk finished.ext) .dyn = 2 ∧
 finished.st.heap.len ((sharedDefault.wk chosen.ext).wk finished.ext) .dyn = 0 ∧
 finished.st.heap.len (callDefault.wk finished.ext) .dyn = 0 ∧
 finished.st.heap.len (privateNew.wk finished.ext) .dyn = 2 ∧
 (MObj.elems .dyn (finished.st.heap.get exported))[0]? = some (indexValue (wmod 12)) ∧
 (MObj.elems .dyn (finished.st.heap.get exported))[1]? = some (indexValue (wmod 11)) ∧
 (MObj.elems .dyn (finished.st.heap.get ((other.wk chosen.ext).wk finished.ext)))[0]? = some (indexValue (wmod 23)) ∧
 (MObj.elems .dyn (finished.st.heap.get ((other.wk chosen.ext).wk finished.ext)))[1]? = some (indexValue (wmod 29)) ∧
 (MObj.elems .dyn (finished.st.heap.get (privateNew.wk finished.ext)))[0]? = some (indexValue (wmod 99)) ∧
 (MObj.elems .dyn (finished.st.heap.get (privateNew.wk finished.ext)))[1]? = some (indexValue (wmod 101)) := by
 repeat' constructor
 all_goals decide +kernel

#print axioms final_aliases
#print axioms heap_values
#print axioms frontend_link
#print axioms first_guard
#print axioms second_guard
#print axioms first_direct
#print axioms second_direct
#print axioms seed_run
#print axioms first_miss
#print axioms second_hit
#print axioms body_run
#print axioms chosen_run
#print axioms post_run
#print axioms before_values
#print axioms after_values
#print axioms final_values
#print axioms seed_cost
#print axioms seed_frame
#print axioms first_cost
#print axioms second_cost
#print axioms reached_cost
#print axioms frame_need
#print axioms room
#print axioms post_cost
#print axioms post_room
end Solidity.Backend.InternalFlow.MemoryDispatchChecks
