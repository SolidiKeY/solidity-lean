import Solidity.Backend.Passes.EffectfulShortCircuit
import Solidity.Backend.Passes.PositiveAllocationFailure
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.EffectfulShortCircuit.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0 s0)
abbrev C := PositiveAllocationFailure.C
abbrev Γ : Ctx := [.val .bool,.val .bool,.val .bool,.val .uint]
abbrev srcΓ : Source.RCtx := [.bool,.bool,.bool]
abbrev F := Frag.init Γ
abbrev i : Idx Γ (.val .bool) := .here
abbrev a : Idx Γ (.val .bool) := .there .here
abbrev j : Idx Γ (.val .bool) := .there (.there .here)
def state (x : Bool) : State C Γ :=
  ((PositiveAllocationFailure.before.push (t := .val .bool) true).push
    (t := .val .bool) x).push (t := .val .bool) false
def source (x : Bool) : Source.EMState E0 srcΓ :=
  (.cons (.bool false) (.cons (.bool x) (.cons (.bool true) .nil)),s0)
def alignment : ContextMap srcΓ Γ :=
  (((ContextMap.empty.wk (.drop .refl)).cons .bool (.val .bool)).cons
    .bool (.val .bool)).cons .bool (.val .bool)
def relation (τ : Source.STy) (u : LTy) :
    Source.Val E0.layout τ → u.TDenote C [] → Prop :=
  match τ,u with
  | .bool,.val .bool => fun v x => v = .bool x
  | _,_ => fun _ _ => False

theorem aligned (x : Bool) : alignment.Related relation (source x).1 (state x).env := by
  intro τ idx
  cases idx with
  | here => rfl
  | there idx => cases idx with
    | here => rfl
    | there idx => cases idx with
      | here => rfl
      | there idx => nomatch idx

def program (conj : Bool) : Prog C Γ (.val .bool :: Γ) := shortAssignPrefix conj i a j i
def selected (conj : Bool) : Memory.CompiledProg 1 F (program conj) :=
  (Memory.compileProg 1 F (program conj)).get (by cases conj <;> decide +kernel)
def compiled (conj : Bool) : Compilation 1 F (program conj) := .memory (selected conj)
def cursor : Fin W := wmod 64
def machine (x : Bool) : Machine :=
  writeMachine (writeMachine (writeMachine (PositiveAllocationFailure.machine cursor)
    2 (.val (bword true))) 3 (.val (bword x))) 4 (.val (bword false))

theorem represented (x : Bool) :
    StateRepr 1 1 16 F (state x) PositiveAllocationFailure.base (machine x) := by
  have h := (PositiveAllocationFailure.initial cursor (by decide)).1
  exact ((h.consVal (p := .bool) true (.val (bword true)) rfl (by decide)).consVal (p := .bool)
    x (.val (bword x)) rfl (by decide)).consVal (p := .bool) false (.val (bword false)) rfl (by decide)

theorem input (conj x : Bool) :
    (compiled conj).Input 1 16 PositiveAllocationFailure.base (state x) (machine x) := by
  refine ⟨represented x,?_,?_⟩
  · cases conj <;> decide +kernel
  · apply Or.inl
    cases conj <;> rfl

/-- One emitted program for both runtime Booleans, with an actual full physical
Input. The RHS aliases the local written by the left assignment. -/
def application (pipeline : Roadmap.Pipeline) (fuel : Nat) (conj x : Bool) :=
  execution (G0 pipeline) F0 fuel (source x) (state x) alignment relation (aligned x)
    (fun _ _ h => h) conj .here (.there .here) (.there (.there .here)) .here
    i a j i rfl rfl rfl rfl (compiled conj) (input conj x)

def cells : List Nat := [0,1,2,3,4,5,8,9]
private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
private theorem extracted {out : Evm.Out} (h : (okMachine out).isSome) :
    out = .ok ((okMachine out).get h) 0 := by
  cases out with
  | ok m skip => cases skip with
    | zero => rfl
    | succ n => cases h
  | revert => cases h
  | fault => cases h

@[irreducible] def executed (conj x : Bool) : Machine :=
  (okMachine (run (compiled conj).code (machine x))).get
    (by cases conj <;> cases x <;> decide +kernel)
def observed (conj x : Bool) (tail : List Word) : Machine :=
  {executed conj x with stack := tail}

theorem actual_target (conj x : Bool) :
    run (compiled conj).code (machine x) = .ok (executed conj x) 0 := by
  unfold executed
  exact extracted _
theorem executed_stack (conj x : Bool) : (executed conj x).stack = [w[77]] := by
  have hs := short_assign_prefix_run (state x) conj i a j i x rfl
  obtain ⟨out,ht,stack,_⟩ := compilation_success (compiled conj) (input conj x)
    (payment_free conj i a j i) hs
  have same : out = executed conj x := (Evm.Out.ok.inj (ht.symm.trans (actual_target conj x))).1
  rw [← same]
  exact stack

theorem target_tail (conj x : Bool) (tail : List Word) :
    run (compiled conj).code {machine x with stack := tail} =
      .ok (observed conj x tail) 0 := by
  have success := actual_target conj x
  have canonical := compilation_tail_exact (compiled conj) (input conj x)
    (payment_free conj i a j i) [w[77]]
  change run (compiled conj).code (machine x) = _ at canonical
  rw [success] at canonical
  have target := compilation_tail_exact (compiled conj) (input conj x)
    (payment_free conj i a j i) tail
  cases outcome : run (compiled conj).code {machine x with stack := []} with
  | ok final skip =>
    rw [outcome] at canonical target
    have skipZero : skip = 0 := (Evm.Out.ok.inj canonical).2.symm
    subst skip
    have same := (Evm.Out.ok.inj canonical).1
    have projected := congrArg (fun m : Machine => {m with stack := tail}) same
    simpa only [replaceOutStack,observed] using target.trans
      (congrArg (fun m => Evm.Out.ok m 0) projected.symm)
  | revert => rw [outcome] at canonical; cases canonical
  | fault => rw [outcome] at canonical; cases canonical

theorem initial_observations (x : Bool) :
    (cells.map (machine x).mem,(machine x).stack) =
      ([w[64],w[0],w[1],.val (bword x),w[0],w[0],w[10],w[99]],[w[77]]) := by
  cases x <;> rfl

theorem complete_observations (conj x : Bool) (tail : List Word) :
    (cells.map (observed conj x tail).mem,(observed conj x tail).stack) =
      ([w[64],w[0],.val (bword (if needsRight conj x then x else true)),
        .val (bword x),.val (bword x),.val (bword x),w[10],w[99]],tail) := by
  apply Prod.ext
  · change cells.map (executed conj x).mem =
      [w[64],w[0],.val (bword (if needsRight conj x then x else true)),
        .val (bword x),.val (bword x),.val (bword x),w[10],w[99]]
    unfold executed
    cases conj <;> cases x <;> decide +kernel
  · rfl

/-- Eager RHS execution would overwrite j on the stopping conjunction case. -/
theorem eager_rhs_wrong : (observed true false []).mem 2 ≠ .val (bword false) := by unfold observed executed; decide +kernel
/-- Reversing the assignments reads the old false alias, losing the true result. -/
theorem stale_alias_wrong : (observed true true []).mem 5 ≠ .val (bword false) := by unfold observed executed; decide +kernel

theorem saved_tail_wrong (conj x : Bool) (tail : List Word) :
    (observed conj x (w[77] :: tail)).stack ≠ w[78] :: tail := by
  intro same
  exact (by decide : (w[77] : Word) ≠ w[78]) (List.cons.inj same).1

/-- Actual alternate intrinsic programs, not merely alternative output values. -/
def eager : Prog C Γ (.val .bool :: Γ) :=
  .cons (.assignLocal i (.simple (.local a)))
    (.cons (.declLocal .bool (.user "v07_short_left") (some (.simple (.local i))))
      (shortRight j i))
def reversed : Prog C Γ (.val .bool :: Γ) :=
  .cons (.assignLocal j (.simple (.local i)))
    (.cons (.assignLocal i (.simple (.local a)))
      (.cons (.declLocal .bool (.user "wrong") (some (.simple (.local j)))) .nil))
def eagerCode : Memory.CompiledProg 1 F eager :=
  (Memory.compileProg 1 F eager).get (by decide +kernel)
def reversedCode : Memory.CompiledProg 1 F reversed :=
  (Memory.compileProg 1 F reversed).get (by decide +kernel)
def eagerMachine : Machine := (okMachine (run eagerCode.code (machine false))).get (by decide +kernel)
def reversedMachine : Machine := (okMachine (run reversedCode.code (machine true))).get (by decide +kernel)

theorem eager_source : eager.run (state false) =
    .ok ⟨((state false).setLocal i false |>.setLocal j false).push
      (t := .val .bool) false,List.prefix_refl _⟩ := by rfl
theorem reversed_source : reversed.run (state true) =
    .ok ⟨((state true).setLocal j false |>.setLocal i true).push
      (t := .val .bool) false,List.prefix_refl _⟩ := by rfl
theorem eager_target : run eagerCode.code (machine false) = .ok eagerMachine 0 := extracted _
theorem reversed_target : run reversedCode.code (machine true) = .ok reversedMachine 0 := extracted _

theorem eager_complete : (cells.map eagerMachine.mem,eagerMachine.stack) =
    ([w[64],w[0],w[0],w[0],w[0],w[0],w[10],w[99]],[w[77]]) := by decide +kernel
theorem reversed_complete : (cells.map reversedMachine.mem,reversedMachine.stack) =
    ([w[64],w[0],w[0],w[1],w[1],w[0],w[10],w[99]],[w[77]]) := by decide +kernel


theorem insufficient_frame (conj x : Bool) :
    ¬ (compiled conj).Input 1 5 PositiveAllocationFailure.base (state x) (machine x) := by
  intro h
  have room := h.2.1
  cases conj <;> change 6 ≤ 5 at room <;> omega

theorem source_observations (pipeline : Roadmap.Pipeline) (fuel : Nat) (conj x : Bool) :
    (Source.evalE (G0 pipeline) F0 (fuel+3)
      (.binary (if conj then .and else .or)
        (.assign (.local (.here : Source.Idx srcΓ .bool)) (.local (.there .here)))
        (.assign (.local (.there (.there .here))) (.local .here)))).run (source x) =
      (.ok (.val (.bool x)),
        (.cons (.bool x) (.cons (.bool x)
          (.cons (.bool (if needsRight conj x then x else true)) .nil)),s0)) := by
  have h := source_short_assign_run (G0 pipeline) F0 fuel (source x) conj
    .here (.there .here) (.there (.there .here)) .here x false rfl rfl
  cases conj <;> cases x <;> exact h

end Solidity.Backend.Passes.EffectfulShortCircuit.Controls
