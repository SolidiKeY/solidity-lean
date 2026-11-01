import Solidity.Backend.InternalFlow.FiniteDispatch
import Solidity.Syntax.Splice
import Solidity.Evm.Correct
import Solidity.Semantics.Dispatch
namespace Solidity.Backend.InternalFlow.DispatchChecks
open Evm Evm.Memory FiniteDispatch PublishedDirectCalls

def C : Contract := contract!{
  uint count;
  function first(uint[] memory xs, uint k) returns (uint r) {
    uint[] memory dead = new uint[](4); count = 1000; r = xs[0] + k;
  }
  function second(uint[] memory xs, uint k) returns (uint r) {
    uint[] memory tmp = new uint[](2); tmp[0] = 70; tmp[1] = 71;
    xs[1] = xs[1] + k; count = count + 1; r = xs[1];
  }
}
def front := sol[C]{
  count = 9; uint marker = 42;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](2); other[0] = 23; other[1] = 29;
  function (uint[] memory, uint) returns (uint) h = second;
  uint r = h(xs, 5);
}

abbrev A : RefTy := .array (.prim .uint)
abbrev Caller : Ctx := [.val .uint,.mem A,.val .uint,.val .uint,.mem A,.mem A,.mem A,.val .uint]
private def suffix {Γ Δ : Ctx} (n : Nat) (P : Prog C Γ Δ) : Σ Ξ, Prog C Ξ Δ :=
  match n,P with
  | 0,P => ⟨Γ,P⟩
  | _+1,.nil => ⟨Γ,.nil⟩
  | n+1,.cons _ P => suffix n P
def manualSeed : Prog C [] Caller := sol[C]{count = 9; uint marker = 42;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](2); other[0] = 23; other[1] = 29;
  function (uint[] memory, uint) returns (uint) h = second;
  uint r; uint[] memory se1 = xs; uint se2 = 5;}
private def splitAt {Γ Δ : Ctx} (n : Nat) (P : Prog C Γ Δ) :
    Σ Ξ, Prog C Γ Ξ × Prog C Ξ Δ :=
  match n,P with
  | 0,P => ⟨Γ,.nil,P⟩
  | _+1,.nil => ⟨Γ,.nil,.nil⟩
  | n+1,.cons s P => let t := splitAt n P; ⟨t.1,.cons s t.2.1,t.2.2⟩
def seedProgram : Prog C [] Caller := (splitAt 13 front).2.1
def directFirst := sol[C]{count = 9; uint marker = 42;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](2); other[0] = 23; other[1] = 29;
  function (uint[] memory, uint) returns (uint) h = second;
  uint r; uint[] memory se1 = xs; uint se2 = 5;r = first(se1,se2);}
def directSecond := sol[C]{count = 9; uint marker = 42;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](2); other[0] = 23; other[1] = 29;
  function (uint[] memory, uint) returns (uint) h = second;
  uint r; uint[] memory se1 = xs; uint se2 = 5;r = second(se1,se2);}
def bodyFirst : Prog C Caller Caller := (suffix 13 directFirst).2
def bodySecond : Prog C Caller Caller := (suffix 13 directSecond).2
def guard (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Caller .bool :=
  .binop .eqB rfl rfl (.simple (.local (.there (.there (.there .here))))) (.simple (.lit n hn))
def armFirst : DispatchArm C Caller := ⟨guard 1 rfl,bodyFirst⟩
def armSecond : DispatchArm C Caller := ⟨guard 2 rfl,bodySecond⟩
def dispatch := DispatchArm.chain [armFirst,armSecond] (.revert : Stmt C Caller Caller)
def expanded : Prog C [] Caller := seedProgram.join (.cons dispatch .nil)

def actualFirst : DispatchArm C Caller := match (suffix 13 front).2 with
  | .cons (.ite c t _) .nil => ⟨c,t⟩
  | _ => ⟨.simple (.bool false),.nil⟩
theorem first_guard : actualFirst.cond = guard 1 rfl := by rfl
theorem first_body : actualFirst.body = bodyFirst := by rfl
def rest : Σ Ξ, Prog C Caller Ξ := match (suffix 13 front).2 with
  | .cons (.ite _ _ e) .nil => ⟨_,e⟩
  | _ => ⟨Caller,.nil⟩
def actualSecond : DispatchArm C Caller := match rest.2 with
  | .cons (.ite c t _) .nil => ⟨c,t⟩
  | _ => ⟨.simple (.bool false),.nil⟩
theorem second_guard : actualSecond.cond = guard 2 rfl := by rfl
theorem second_run : actualSecond.body.runR = bodySecond.runR := by funext σ; rfl
def actualDispatch := DispatchArm.chain [actualFirst,actualSecond] (.revert : Stmt C Caller Caller)
theorem actual_frontend_link : front = seedProgram.join (.cons actualDispatch .nil) := by rfl


def bases : Nat → Fin W := fun _ => wmod 0
def machine : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[128] else if a = 63 then w[99] else w[0]}
theorem initial_repr (K : Contract) :
    StateRepr 1 1 64 (Frag.init []) (State.init K) bases machine ∧
    StructAllocatorRepr (State.init K).heap bases 64 (wmod 128) machine := by
  have noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?
  have hh : HeapRepr (State.init K).heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr (State.init K).heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated (State.init K).heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init K 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩, ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx,
    fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; nomatch i
    · intro R i hi; nomatch i
    · intro R i hi; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 128 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl


private theorem actual_get {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by cases r <;> cases h <;> rfl

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
  checkedChain 1 seed.frag .revert fallback [actualFirst,actualSecond] ⟨⟨firstCond,firstCert⟩,⟨⟨secondCond,secondCert⟩,()⟩⟩
attribute [irreducible] checked

def armOut : Solidity.Out C mid.st.H Caller := (actualSecond.body.run mid.st).toOption.get (by decide +kernel)
def chosen : Solidity.Out C mid.st.H Caller := ⟨armOut.st.drop actualSecond.body.ext,armOut.ext⟩
private theorem ok_of_toOption {α : Type} (r : TRes α) (a : α) (h : r.toOption = some a) : r = .ok a := by
  cases r <;> cases h <;> rfl
theorem first_miss : actualFirst.cond.evalT mid.st = .ok false :=
  ok_of_toOption _ false (by decide +kernel)
theorem second_hit : actualSecond.cond.evalT mid.st = .ok true :=
  ok_of_toOption _ true (by decide +kernel)
theorem body_run : actualSecond.body.run mid.st = .ok armOut := actual_get _ (by decide +kernel)
theorem chosen_run : actualDispatch.run mid.st = .ok chosen := by
  change (DispatchArm.chain ([actualFirst] ++ actualSecond :: []) (.revert : Stmt C Caller Caller)).run mid.st = _
  rw [select_run [actualFirst] actualSecond [] .revert mid.st (by
    intro a h; have ha := List.mem_singleton.mp h; subst a; exact first_miss) second_hit,body_run]
  rfl

def array {Γ : Ctx} (σ : State C Γ) (id : Nat) : Option (List Int) :=
  if h : σ.H[id]? = some A then
    let r : HRef σ.H A := ⟨id,h⟩
    some ((σ.heap.len r .dyn : Int) :: (MObj.elems .dyn (σ.heap.get r)).map (fun n => n.1))
  else none
def root {Γ : Ctx} (σ : State C Γ) : Option Int :=
  ((Val.read (.root "count" rfl) : Val C Γ .uint).evalT σ).toOption.map (·.1)
def locals (σ : State C Caller) : List (Option Nat) :=
  [some σ.env.1.1.toNat,σ.env.2.1.map (·.id),some σ.env.2.2.1.1.toNat,
   some σ.env.2.2.2.1.1.toNat,σ.env.2.2.2.2.1.map (·.id),
   σ.env.2.2.2.2.2.1.map (·.id),σ.env.2.2.2.2.2.2.1.map (·.id),
   some σ.env.2.2.2.2.2.2.2.1.1.toNat]
theorem before_values : (mid.st.H.length,[array mid.st 0,array mid.st 1],locals mid.st,root mid.st) =
    (2,[some [2,7,11],some [2,23,29]],
     [some 5,some 0,some 0,some 2,some 1,some 0,some 0,some 42],some 9) := by decide +kernel
theorem after_values : (chosen.st.H.length,[array chosen.st 0,array chosen.st 1,array chosen.st 2],locals chosen.st,root chosen.st) =
    (3,[some [2,7,16],some [2,23,29],some [2,70,71]],
     [some 5,some 0,some 16,some 2,some 1,some 0,some 0,some 42],some 10) := by decide +kernel

theorem seed_cost : seed.cost (State.init C) = 6 := by decide +kernel
theorem seed_frame : 1 + seed.need ≤ 64 := by decide +kernel
theorem first_cost : firstCert.cost mid.st = 5 := by decide +kernel
theorem second_cost : secondCert.cost mid.st = 3 := by decide +kernel
theorem reached_cost : checked.cost mid.st = 3 := by decide +kernel
theorem frame_need : checked.need = 12 := by decide +kernel
theorem room : 1 + checked.need ≤ 64 := by rw [frame_need]; decide

def callName {Γ Δ : Ctx} (P : Prog C Γ Δ) : Option Name := match P with
  | .cons (.call f _ _ _) .nil => some f
  | _ => none
theorem candidate_names : (callName actualFirst.body,callName actualSecond.body) =
    (some "first",some "second") := rfl
/-- Raw declaration types/locations are kernel data; canonical printing is partial. -/
theorem candidate_signatures : C.funs.map (fun (_,d) => (d.params,d.paramLocs,d.rets,d.retMem,d.retStorage)) =
    [([("xs",Ty.ref A),("k",Ty.uint)],[("xs",ParamLoc.memory)],[("r",Ty.uint)],false,false),
     ([("xs",Ty.ref A),("k",Ty.uint)],[("xs",ParamLoc.memory)],[("r",Ty.uint)],false,false)] := by rfl
/-- info: true -/
#guard_msgs in #eval decide (C.funs.map (fun (_,d) => FunDecl.sigTy? C d) =
  [some "function(uint[]memory,uint)returns(uint)",some "function(uint[]memory,uint)returns(uint)"])

def old : HRef mid.st.H A := ⟨0,by decide +kernel⟩
def other : HRef mid.st.H A := ⟨1,by decide +kernel⟩
def fresh : HRef chosen.st.H A := ⟨2,by decide +kernel⟩
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

theorem aliases :
    TEnv.get (.there .here : Idx Caller (.mem A)) chosen.st.env = some (old.wk chosen.ext) ∧
    TEnv.get (.there (.there (.there (.there (.there .here)))) : Idx Caller (.mem A)) chosen.st.env = some (old.wk chosen.ext) ∧
    TEnv.get (.there (.there (.there (.there (.there (.there .here))))) : Idx Caller (.mem A)) chosen.st.env = some (old.wk chosen.ext) ∧
    TEnv.get (.there (.there (.there (.there .here))) : Idx Caller (.mem A)) chosen.st.env = some (other.wk chosen.ext) := by
  refine ⟨ref_by_id _ _ (by decide +kernel),ref_by_id _ _ (by decide +kernel),
    ref_by_id _ _ (by decide +kernel),ref_by_id _ _ (by decide +kernel)⟩

theorem heap_values :
    chosen.st.heap.len (old.wk chosen.ext) .dyn = 2 ∧
    chosen.st.heap.len (other.wk chosen.ext) .dyn = 2 ∧ chosen.st.heap.len fresh .dyn = 2 ∧
    (MObj.elems .dyn (chosen.st.heap.get (old.wk chosen.ext)))[0]? = some (indexValue (wmod 7)) ∧
    (MObj.elems .dyn (chosen.st.heap.get (old.wk chosen.ext)))[1]? = some (indexValue (wmod 16)) ∧
    (MObj.elems .dyn (chosen.st.heap.get (other.wk chosen.ext)))[0]? = some (indexValue (wmod 23)) ∧
    (MObj.elems .dyn (chosen.st.heap.get (other.wk chosen.ext)))[1]? = some (indexValue (wmod 29)) ∧
    (MObj.elems .dyn (chosen.st.heap.get fresh))[0]? = some (indexValue (wmod 70)) ∧
    (MObj.elems .dyn (chosen.st.heap.get fresh))[1]? = some (indexValue (wmod 71)) := by
  repeat' constructor
  all_goals decide +kernel

def clearTag : Stmt C Caller Caller := .assignLocal (.there (.there (.there .here))) (.simple (.lit 0 rfl))
def cleared : Solidity.Out C mid.st.H Caller :=
  ⟨mid.st.setLocal (.there (.there (.there .here))) (indexValue (wmod 0)),List.prefix_refl _⟩
def clearCert : Calls.Statement 1 seed.frag clearTag :=
  Calls.plainStmt ((Memory.compileStmt 1 seed.frag clearTag).get (by decide +kernel))
theorem clear_run : clearTag.run mid.st = .ok cleared := by rfl
theorem clear_frag : clearCert.frag = seed.frag := by rfl
theorem clear_cost : clearCert.cost mid.st = 0 := by decide +kernel
theorem clear_room : 1 + clearCert.need ≤ 64 := by decide +kernel
theorem all_miss : ∀ a ∈ [actualFirst,actualSecond], a.cond.evalT cleared.st = .ok false := by
  intro a h
  rcases List.mem_cons.mp h with h | h
  · subst a; exact ok_of_toOption _ false (by decide +kernel)
  rcases List.mem_cons.mp h with h | h
  · subst a; exact ok_of_toOption _ false (by decide +kernel)
  · cases h
theorem no_match_run : actualDispatch.run cleared.st = .error .revert := by
  change (DispatchArm.chain [actualFirst,actualSecond] (.revert : Stmt C Caller Caller)).run cleared.st = _
  rw [none_run [actualFirst,actualSecond] .revert cleared.st all_miss]
  rfl
theorem no_match_cost : checked.cost cleared.st = 0 := by decide +kernel

theorem frame_only_caller_refused : ¬ 1 + checked.need ≤ 1 + Caller.length := by
 rw [frame_need]; decide +kernel
theorem wrong_reached_costs : checked.cost mid.st ≠ 5 ∧ checked.cost mid.st ≠ 8 := by
 rw [reached_cost]; constructor <;> decide

theorem payload_refused : (Calls.compile 1 seed.frag
 (.cons (.revertData [.bytes [17,0,33]] : Stmt C Caller Caller) .nil)).isSome = false := by decide +kernel
theorem recursive_constructor_refused : (Calls.compile 1 seed.frag
 (.cons (.callRec "unavailable" 2 (.nil : Args C Caller []) .none (fun _ => .nil)) .nil)).isSome = false := by decide +kernel
theorem storage_result_refused : (Calls.compile 1 seed.frag
 (.cons (.call "unavailable" (.nil : Args C Caller []) (.storage A (.user "r"))
   (.nil : Prog C [.alias A] [.alias A])) .nil)).isSome = false := by decide +kernel
#print axioms frame_only_caller_refused
#print axioms wrong_reached_costs
#print axioms payload_refused
#print axioms recursive_constructor_refused
#print axioms storage_result_refused
#print axioms clear_run
#print axioms clear_frag
#print axioms clear_cost
#print axioms clear_room
#print axioms all_miss
#print axioms no_match_run
#print axioms no_match_cost
#print axioms cons_frag
#print axioms cons_need
#print axioms candidate_names
#print axioms candidate_signatures
#print axioms aliases
#print axioms heap_values
#print axioms checkedChain
#print axioms select_run
#print axioms none_run
#print axioms selected_endpoint
#print axioms fallback_revert
#print axioms actual_frontend_link
#print axioms first_guard
#print axioms second_guard
#print axioms first_body
#print axioms second_run
#print axioms seed_run
#print axioms first_miss
#print axioms second_hit
#print axioms body_run
#print axioms chosen_run
#print axioms before_values
#print axioms after_values
#print axioms seed_cost
#print axioms seed_frame
#print axioms first_cost
#print axioms second_cost
#print axioms reached_cost
#print axioms frame_need
#print axioms room
end Solidity.Backend.InternalFlow.DispatchChecks
